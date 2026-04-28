import math
from dataclasses import dataclass

import torch
from torch.utils.data import Dataset


@dataclass(frozen=True)
class AlgebraStrongEpisodeCfg:
    n_states: int
    n_views: int
    y_classes: int
    steps: int
    obs_vocab: int


def _seeded_gen(seed: int) -> torch.Generator:
    g = torch.Generator()
    g.manual_seed(int(seed))
    return g


def _randint(g: torch.Generator, low: int, high: int, shape: tuple[int, ...]) -> torch.Tensor:
    return torch.randint(low=int(low), high=int(high), size=shape, generator=g)


def _candidate_mask(
    *,
    tables: torch.Tensor,  # (V,N)
    base_obs: int,
    actions: list[int],
    responses: list[int],
) -> torch.Tensor:
    V, _ = tables.shape
    m = tables[0].eq(int(base_obs))
    for a, r in zip(actions, responses):
        a = int(a)
        if a < 0 or a >= int(V):
            raise ValueError(f"action out of range: {a} for n_views={V}")
        m = m & tables[a].eq(int(r))
    return m


def _sigma_ambiguity(*, sigma: torch.Tensor, cand_mask: torch.Tensor) -> int:
    vals = sigma[cand_mask]
    if int(vals.numel()) == 0:
        return 0
    return int(torch.unique(vals).numel())


def _is_closed_after_steps(
    *,
    tables: torch.Tensor,  # (V,N)
    sigma: torch.Tensor,  # (N,)
    x: int,
    actions: list[int],
) -> bool:
    base_obs = int(tables[0, int(x)].item())
    responses = [int(tables[int(a), int(x)].item()) for a in actions]
    cand = _candidate_mask(tables=tables, base_obs=base_obs, actions=actions, responses=responses)
    return _sigma_ambiguity(sigma=sigma, cand_mask=cand) == 1


def sample_episode(
    *,
    idx: int,
    cfg: AlgebraStrongEpisodeCfg,
    ood: bool,
    seed_base: int,
) -> dict[str, torch.Tensor]:
    """
    Strong version of v18 multistep:

    Goal: prevent a local "uniq>1" heuristic from identifying the useful query views.

    Construction (T=2, n divisible by 8):
      X ≅ Base × {0,1} × {0,1} × {0,1}
               base   bit1   bit2   noise

    - base view reveals Base only
    - two useful query views reveal bit1 and bit2 (order/indices permuted per episode)
    - distractor views reveal ONLY noise (so they vary inside the base fiber but do not help close σ)
    - σ depends on (bit1,bit2) with a per-base flip (XOR/XNOR), so:
        base alone not closed,
        any single query not closed,
        both bit views together close.
    """
    n = int(cfg.n_states)
    v = int(cfg.n_views)
    y = int(cfg.y_classes)
    T = int(cfg.steps)
    obs_vocab = int(cfg.obs_vocab)
    if T != 2:
        raise ValueError("strong core currently defined only for steps=2")
    if y != 2:
        raise ValueError("strong core currently requires y_classes=2")
    if n < 8 or (n % 8) != 0:
        raise ValueError("strong core requires n_states divisible by 8")
    if v < 5:
        raise ValueError("need n_views >= 5 (base + 2 useful + >=2 distractors)")
    if obs_vocab < 4:
        raise ValueError("obs_vocab too small")

    g = _seeded_gen(int(seed_base) + int(idx) * 9973 + (1337 if bool(ood) else 0))

    n_base = int(n) // 8
    base_raw = torch.arange(n, dtype=torch.long) // 8
    bit1_raw = (torch.arange(n, dtype=torch.long) // 4) % 2
    bit2_raw = (torch.arange(n, dtype=torch.long) // 2) % 2
    noise_raw = torch.arange(n, dtype=torch.long) % 2

    # Random relabeling into [0, obs_vocab) to prevent fixed-token shortcuts.
    perm = torch.randperm(int(obs_vocab), generator=g).to(torch.long)
    base_lbl = perm[base_raw % int(obs_vocab)]
    bit1_lbl = perm[bit1_raw]
    bit2_lbl = perm[bit2_raw]

    tables = torch.zeros((v, n), dtype=torch.long)
    tables[0] = base_lbl

    # Useful query channels (bit1/bit2).
    tables[1] = bit1_lbl
    tables[2] = bit2_lbl

    # Distractors: noise-only refinements inside the base fiber.
    # Each distractor picks two labels per base bucket, and applies them by noise bit.
    for i in range(3, v):
        a0 = _randint(g, 0, int(obs_vocab), (n_base,)).to(torch.long)
        a1 = _randint(g, 0, int(obs_vocab), (n_base,)).to(torch.long)
        if bool(ood):
            a0 = perm[a0 % int(obs_vocab)]
            a1 = perm[a1 % int(obs_vocab)]
        out = torch.where(noise_raw == 0, a0[base_raw], a1[base_raw])
        tables[i] = out.to(torch.long)

    # σ pattern: XOR/XNOR per base bucket (depends only on bit1,bit2).
    flip = _randint(g, 0, 2, (n_base,)).to(torch.long)
    sigma = (bit1_raw ^ bit2_raw ^ flip[base_raw]).to(torch.long)

    # Permute non-base view rows so the useful channels are not at fixed indices.
    perm_nonbase = torch.randperm(int(v - 1), generator=g).to(torch.long) + 1
    row_perm = torch.cat([torch.tensor([0], dtype=torch.long), perm_nonbase], dim=0)
    tables = tables[row_perm]

    # Identify where the original bit rows landed after permutation.
    # row_perm is a mapping new_row -> old_row.
    # We need inverse: old_row -> new_row.
    inv = torch.empty_like(row_perm)
    inv[row_perm] = torch.arange(int(v), dtype=torch.long)
    bit1_idx = int(inv[1].item())
    bit2_idx = int(inv[2].item())

    # Canonical "optimal" action sequence = sorted indices of the two useful views.
    opt_actions = [int(min(bit1_idx, bit2_idx)), int(max(bit1_idx, bit2_idx))]

    # Sample x and compute episode tensors.
    x = int(_randint(g, 0, n, (1,)).item())
    base_obs = int(tables[0, x].item())
    opt_responses = torch.tensor([int(tables[a, x].item()) for a in opt_actions], dtype=torch.long)

    # Sanity: closure happens after T=2, and not after 1.
    if not _is_closed_after_steps(tables=tables, sigma=sigma, x=x, actions=opt_actions):
        raise RuntimeError("strong episode invariant violated: not closed after 2")
    if _is_closed_after_steps(tables=tables, sigma=sigma, x=x, actions=opt_actions[:1]):
        raise RuntimeError("strong episode invariant violated: closed after 1")

    return {
        "tables": tables,
        "sigma": sigma,
        "x": torch.tensor(int(x), dtype=torch.long),
        "y": torch.tensor(int(sigma[x].item()), dtype=torch.long),
        "base_obs": torch.tensor(int(base_obs), dtype=torch.long),
        "opt_actions": torch.tensor(opt_actions, dtype=torch.long),
        "opt_responses": opt_responses,
    }


class V18AlgebraMultistepDataset64_Strong(Dataset):
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
        self.cfg = AlgebraStrongEpisodeCfg(
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

