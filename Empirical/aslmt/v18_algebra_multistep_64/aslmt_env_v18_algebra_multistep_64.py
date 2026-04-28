import math
from dataclasses import dataclass
from typing import Optional

import torch
from torch.utils.data import Dataset


@dataclass(frozen=True)
class AlgebraEpisodeCfg:
    n_states: int
    n_views: int
    y_classes: int
    steps: int
    # observation vocab for each view: values in [0, obs_vocab)
    obs_vocab: int


def _pairs_count(n: int) -> int:
    n = int(n)
    return (n * (n - 1)) // 2


def _seeded_gen(seed: int) -> torch.Generator:
    g = torch.Generator()
    g.manual_seed(int(seed))
    return g


def _randint(g: torch.Generator, low: int, high: int, shape: tuple[int, ...]) -> torch.Tensor:
    # high is exclusive
    return torch.randint(low=int(low), high=int(high), size=shape, generator=g)


def _balanced_sigma_for_base(
    *, g: torch.Generator, base_labels: torch.Tensor, y_classes: int, max_tries: int = 200
) -> torch.Tensor:
    """
    Sample σ so that within each base bucket, σ is not constant (barrier),
    and is approximately balanced to avoid leakage.
    """
    y_classes = int(y_classes)
    n = int(base_labels.numel())
    base = base_labels.to(torch.long)
    uniq = torch.unique(base).tolist()

    for _ in range(int(max_tries)):
        sigma = _randint(g, 0, y_classes, (n,)).to(torch.long)

        ok = True
        for b in uniq:
            idx = (base == int(b)).nonzero(as_tuple=False).flatten()
            if int(idx.numel()) <= 1:
                ok = False
                break
            vals = sigma[idx]
            if int(torch.unique(vals).numel()) < 2:
                ok = False
                break
        if ok:
            return sigma

    # Fallback: force non-const per bucket by flipping one element when needed.
    sigma = _randint(g, 0, y_classes, (n,)).to(torch.long)
    for b in uniq:
        idx = (base == int(b)).nonzero(as_tuple=False).flatten()
        if int(idx.numel()) >= 2:
            vals = sigma[idx]
            if int(torch.unique(vals).numel()) < 2:
                sigma[idx[0]] = (sigma[idx[0]] + 1) % y_classes
    return sigma


def _candidate_mask(
    *,
    tables: torch.Tensor,
    base_obs: int,
    actions: list[int],
    responses: list[int],
) -> torch.Tensor:
    """
    Return boolean mask over states consistent with observed transcript.
    """
    n_views, n_states = tables.shape
    m = (tables[0] == int(base_obs))
    for a, r in zip(actions, responses):
        a = int(a)
        if a < 0 or a >= int(n_views):
            raise ValueError(f"action out of range: {a} for n_views={n_views}")
        m = m & (tables[a] == int(r))
    return m


def _sigma_ambiguity(*, sigma: torch.Tensor, cand_mask: torch.Tensor) -> int:
    vals = sigma[cand_mask]
    if int(vals.numel()) == 0:
        return 0
    return int(torch.unique(vals).numel())


def _greedy_opt_actions(
    *,
    tables: torch.Tensor,
    sigma: torch.Tensor,
    x: int,
    steps: int,
    forbid_view0: bool = True,
) -> list[int]:
    """
    Greedy policy: at each step choose the view that minimizes σ-ambiguity
    inside the next candidate fiber (conditioned on the true x response).
    """
    n_views, _ = tables.shape
    steps = int(steps)
    x = int(x)

    base_obs = int(tables[0, x].item())
    chosen: list[int] = []
    seen_actions: set[int] = set()

    for t in range(steps):
        best_a: Optional[int] = None
        best_score = None

        for a in range(int(n_views)):
            if forbid_view0 and a == 0:
                continue
            if a in seen_actions:
                continue

            # response value for this candidate action at true x
            r = int(tables[a, x].item())
            cand = _candidate_mask(tables=tables, base_obs=base_obs, actions=chosen + [a], responses=[int(tables[aa, x].item()) for aa in chosen] + [r])
            amb = _sigma_ambiguity(sigma=sigma, cand_mask=cand)
            # primary: ambiguity; secondary: candidate set size (smaller is better)
            size = int(cand.to(torch.long).sum().item())
            score = (amb, size, a)
            if best_score is None or score < best_score:
                best_score = score
                best_a = int(a)

        if best_a is None:
            # if we ran out of actions, repeat last action (will not help but keeps shapes stable)
            best_a = 1 if int(n_views) > 1 else 0

        chosen.append(int(best_a))
        seen_actions.add(int(best_a))

    return chosen


def _is_closed_after_steps(
    *, tables: torch.Tensor, sigma: torch.Tensor, x: int, actions: list[int]
) -> bool:
    base_obs = int(tables[0, int(x)].item())
    responses = [int(tables[int(a), int(x)].item()) for a in actions]
    cand = _candidate_mask(tables=tables, base_obs=base_obs, actions=actions, responses=responses)
    return _sigma_ambiguity(sigma=sigma, cand_mask=cand) == 1


def sample_episode(
    *,
    idx: int,
    cfg: AlgebraEpisodeCfg,
    ood: bool,
    seed_base: int,
    max_resample: int = 200,
) -> dict[str, torch.Tensor]:
    """
    Deterministic-by-(seed_base,idx) episode sampler.

    Guarantees:
    - base view is not sufficient (σ varies within each base fiber)
    - σ becomes closed after exactly `cfg.steps` greedy steps
    - σ is not closed after `cfg.steps-1` greedy steps (non-trivial multistep)
    """
    n = int(cfg.n_states)
    v = int(cfg.n_views)
    y = int(cfg.y_classes)
    T = int(cfg.steps)
    obs_vocab = int(cfg.obs_vocab)
    if n < 4:
        raise ValueError("n_states must be >= 4 for multistep closure")
    if v < 3:
        raise ValueError("n_views must be >= 3 (base + >=2 queries)")
    if T < 2:
        raise ValueError("steps must be >= 2 for multistep closure")
    if obs_vocab < 2:
        raise ValueError("obs_vocab must be >= 2")

    # Deterministic generator keyed by (seed_base, idx, ood).
    # IID vs OOD changes the distribution of distractor views and σ pattern selection,
    # without changing the observable format (all values remain in [0, obs_vocab)).
    ood = bool(ood)
    g = _seeded_gen(int(seed_base) + int(idx) * 9973 + (1337 if ood else 0))

    # Constructive core (multistep=2):
    # X ≅ Base × {0,1} × {0,1}. Base observation is Base only. Two query views reveal the two bits.
    # σ is sampled so that neither bit alone closes σ inside any base fiber, but (bit1,bit2) does.
    if int(T) == 2 and int(n) % 4 == 0 and int(v) >= 3:
        n_base = int(n) // 4
        if n_base < 2:
            raise ValueError("need n_states/4 >= 2 for multistep algebra core")
        if obs_vocab < max(n_base, 2):
            raise ValueError("obs_vocab too small for constructive multistep core")

        # Base labels occupy [0,n_base), then we randomly relabel into [0,obs_vocab) to avoid shortcuts.
        base_raw = torch.arange(n, dtype=torch.long) // 4
        perm = torch.randperm(int(obs_vocab), generator=g)
        base_lbl = perm[base_raw % int(obs_vocab)]

        bit1_raw = (torch.arange(n, dtype=torch.long) // 2) % 2
        bit2_raw = torch.arange(n, dtype=torch.long) % 2
        bit1_lbl = perm[bit1_raw]
        bit2_lbl = perm[bit2_raw]

        tables = torch.zeros((v, n), dtype=torch.long)
        tables[0] = base_lbl
        tables[1] = bit1_lbl
        tables[2] = bit2_lbl

        # Distractor views: functions of the base only (do not refine inside base fibers).
        # This prevents any closure shortcut via distractor intersections.
        for i in range(3, v):
            per_bucket = _randint(g, 0, int(obs_vocab), (n_base,)).to(torch.long)
            if ood:
                # OOD: different relabeling, same information content (still base-only)
                per_bucket = perm[per_bucket % int(obs_vocab)]
            tables[i] = per_bucket[base_raw]

        # σ pattern: XOR/XNOR per base bucket (guarantees:
        #   - base alone not closed
        #   - (base,bit1) not closed
        #   - (base,bit2) not closed
        #   - (base,bit1,bit2) closed
        # and keeps distractor views uninformative by construction).
        if int(y) != 2:
            raise ValueError("constructive multistep core currently requires y_classes=2")
        flip = _randint(g, 0, 2, (n_base,)).to(torch.long)  # per-base-bucket XOR/XNOR toggle
        sigma = (bit1_raw ^ bit2_raw ^ flip[base_raw]).to(torch.long)

        # Randomly permute the non-base views so that the informative query channels
        # are not at fixed indices (prevents a constant policy from succeeding).
        perm_nonbase = torch.randperm(int(v - 1), generator=g) + 1  # values in [1,v)
        row_perm = torch.cat([torch.tensor([0], dtype=torch.long), perm_nonbase.to(torch.long)], dim=0)
        tables = tables[row_perm]

        x = int(_randint(g, 0, n, (1,)).item())
        actions = _greedy_opt_actions(tables=tables, sigma=sigma, x=x, steps=T, forbid_view0=True)
        base_obs = int(tables[0, x].item())
        responses = torch.tensor([int(tables[a, x].item()) for a in actions], dtype=torch.long)
        return {
            "tables": tables,
            "sigma": sigma,
            "x": torch.tensor(int(x), dtype=torch.long),
            "y": torch.tensor(int(sigma[x].item()), dtype=torch.long),
            "base_obs": torch.tensor(int(base_obs), dtype=torch.long),
            "opt_actions": torch.tensor(actions, dtype=torch.long),
            "opt_responses": responses,
        }

    # Fallback generic sampler (kept for future extensions of T>2).
    for _ in range(int(max_resample)):
        tables = _randint(g, 0, int(obs_vocab), (v, n)).to(torch.long)
        perm = torch.randperm(int(obs_vocab), generator=g)
        tables = perm[tables]

        sigma = _balanced_sigma_for_base(g=g, base_labels=tables[0], y_classes=y)
        x = int(_randint(g, 0, n, (1,)).item())

        actions = _greedy_opt_actions(tables=tables, sigma=sigma, x=x, steps=T, forbid_view0=True)
        if _is_closed_after_steps(tables=tables, sigma=sigma, x=x, actions=actions) and (not _is_closed_after_steps(tables=tables, sigma=sigma, x=x, actions=actions[:-1])):
            base_obs = int(tables[0, x].item())
            responses = torch.tensor([int(tables[a, x].item()) for a in actions], dtype=torch.long)
            return {
                "tables": tables,
                "sigma": sigma,
                "x": torch.tensor(int(x), dtype=torch.long),
                "y": torch.tensor(int(sigma[x].item()), dtype=torch.long),
                "base_obs": torch.tensor(int(base_obs), dtype=torch.long),
                "opt_actions": torch.tensor(actions, dtype=torch.long),
                "opt_responses": responses,
            }

    raise RuntimeError("failed to sample a valid episode (increase obs_vocab or max_resample)")


class V18AlgebraMultistepDataset64(Dataset):
    def __init__(
        self,
        *,
        size: int,
        n_states: int,
        n_views: int,
        y_classes: int,
        steps: int,
        obs_vocab: int,
        ood: bool,
        seed: int,
    ):
        self.size = int(size)
        self.cfg = AlgebraEpisodeCfg(
            n_states=int(n_states),
            n_views=int(n_views),
            y_classes=int(y_classes),
            steps=int(steps),
            obs_vocab=int(obs_vocab),
        )
        self.ood = bool(ood)
        self.seed = int(seed)

    def __len__(self) -> int:
        return int(self.size)

    def __getitem__(self, idx: int):
        return sample_episode(idx=int(idx), cfg=self.cfg, ood=bool(self.ood), seed_base=int(self.seed))
