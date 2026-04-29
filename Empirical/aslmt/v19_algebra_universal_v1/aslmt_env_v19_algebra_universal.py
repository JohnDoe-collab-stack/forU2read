import math
from dataclasses import dataclass

import torch
from torch.utils.data import Dataset


@dataclass(frozen=True)
class AlgebraUniversalEpisodeCfg:
    n_states: int
    n_views: int
    y_classes: int
    obs_vocab: int
    max_steps: int
    # convention: base view is always row 0 in tables
    base_view: int = 0
    # stop action id (must be == n_views)
    # action space size = n_views + 1


def _seeded_gen(seed: int) -> torch.Generator:
    g = torch.Generator()
    g.manual_seed(int(seed))
    return g


def _randint(g: torch.Generator, low: int, high: int, shape: tuple[int, ...]) -> torch.Tensor:
    return torch.randint(low=int(low), high=int(high), size=shape, generator=g)


def _candidate_mask(
    *,
    tables: torch.Tensor,  # (V,N)
    base_view: int,
    base_obs: int,
    actions: list[int],
    responses: list[int],
) -> torch.Tensor:
    V, _ = tables.shape
    m = tables[int(base_view)].eq(int(base_obs))
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


def _is_closed(
    *,
    tables: torch.Tensor,
    sigma: torch.Tensor,
    base_view: int,
    x: int,
    actions: list[int],
) -> bool:
    base_obs = int(tables[int(base_view), int(x)].item())
    responses = [int(tables[int(a), int(x)].item()) for a in actions]
    cand = _candidate_mask(tables=tables, base_view=base_view, base_obs=base_obs, actions=actions, responses=responses)
    return _sigma_ambiguity(sigma=sigma, cand_mask=cand) == 1


def _greedy_opt_actions(
    *,
    tables: torch.Tensor,  # (V,N)
    sigma: torch.Tensor,  # (N,)
    base_view: int,
    x: int,
    max_steps: int,
) -> list[int]:
    """
    Simple universal oracle v1: greedy in expected ambiguity (myopic).

    Note: strong/horizon versions can override this with a DP oracle.
    """
    V, _ = tables.shape
    base_obs = int(tables[int(base_view), int(x)].item())
    actions: list[int] = []
    responses: list[int] = []
    used: set[int] = set()
    for _t in range(int(max_steps)):
        if _is_closed(tables=tables, sigma=sigma, base_view=base_view, x=x, actions=actions):
            break
        cand0 = _candidate_mask(tables=tables, base_view=base_view, base_obs=base_obs, actions=actions, responses=responses)
        idx0 = cand0.nonzero(as_tuple=False).flatten()
        if int(idx0.numel()) == 0:
            break
        total0 = float(idx0.numel())
        best_a = None
        best_exp_amb = 1e18
        for a in range(int(V)):
            if a == int(base_view) or a in used:
                continue
            labels = tables[int(a), idx0].to(torch.long)
            uniq = torch.unique(labels)
            ea = 0.0
            for r in uniq.tolist():
                r = int(r)
                cand1 = cand0 & tables[int(a)].eq(r)
                sz1 = int(cand1.to(torch.long).sum().item())
                if sz1 <= 0:
                    continue
                p = float(sz1) / total0
                ea += p * float(_sigma_ambiguity(sigma=sigma, cand_mask=cand1))
            if ea < best_exp_amb:
                best_exp_amb = float(ea)
                best_a = int(a)
        if best_a is None:
            break
        used.add(int(best_a))
        actions.append(int(best_a))
        responses.append(int(tables[int(best_a), int(x)].item()))
    return actions


def _min_closing_plan(
    *,
    tables: torch.Tensor,  # (V,N)
    sigma: torch.Tensor,  # (N,)
    base_view: int,
    x: int,
    max_steps: int,
) -> list[int]:
    """
    Exact oracle: find a minimal-length (<=max_steps) plan that closes σ for this episode.

    We search over action sequences without repetition. This is exponential in V but tiny for the intended regimes
    (e.g. V<=8, max_steps<=3/4).
    """
    V, _ = tables.shape
    V = int(V)
    max_steps = int(max_steps)
    if max_steps < 0:
        raise ValueError("max_steps must be >= 0")

    # If already closed (shouldn't happen under the barrier), return empty.
    if _is_closed(tables=tables, sigma=sigma, base_view=base_view, x=x, actions=[]):
        return []

    actions_all = list(range(V))
    if int(base_view) in actions_all:
        actions_all.remove(int(base_view))

    # Depth-first search by increasing length.
    def rec(prefix: list[int], used: set[int], depth_left: int) -> list[int] | None:
        if _is_closed(tables=tables, sigma=sigma, base_view=base_view, x=x, actions=prefix):
            return list(prefix)
        if depth_left <= 0:
            return None
        for a in actions_all:
            if int(a) in used:
                continue
            used.add(int(a))
            prefix.append(int(a))
            got = rec(prefix, used, depth_left - 1)
            prefix.pop()
            used.remove(int(a))
            if got is not None:
                return got
        return None

    for L in range(1, max_steps + 1):
        got = rec([], set(), L)
        if got is not None:
            return list(got)
    return []


def sample_episode(
    *,
    idx: int,
    cfg: AlgebraUniversalEpisodeCfg,
    ood: bool,
    seed_base: int,
) -> dict[str, torch.Tensor]:
    """
    Universal v1 episode:

    - Finite latent space X={0..N-1}.
    - Provide (tables, sigma) as cue (full information to compute closure).
    - Base view is row 0.
    - Query loop uses any subset of views to reach closure, then stop.

    v1 family sampler:
    - family_id=0: k-bit closure (k in {1,2,3} depending on max_steps), distractors vary but are non-closing.
    - family_id=1: parity-like closure (needs multiple bit views), with OOD permuted labels.

    This is a scaffold; additional families can be added without changing the protocol.
    """
    n = int(cfg.n_states)
    v = int(cfg.n_views)
    y = int(cfg.y_classes)
    obs_vocab = int(cfg.obs_vocab)
    max_steps = int(cfg.max_steps)
    base_view = int(cfg.base_view)
    if y != 2:
        raise ValueError("v19 universal v1 currently requires y_classes=2")
    if base_view != 0:
        raise ValueError("v19 universal v1 expects base_view=0")
    if v < 3:
        raise ValueError("need n_views>=3")
    if max_steps < 1:
        raise ValueError("need max_steps>=1")
    if obs_vocab < 4:
        raise ValueError("obs_vocab too small")

    g = _seeded_gen(int(seed_base) + int(idx) * 9973 + (1337 if bool(ood) else 0))

    # family choice (OOD can shift distribution)
    fam = int(_randint(g, 0, 2, (1,)).item())
    if bool(ood):
        fam = 1 - fam

    # Universal construction: enforce a fixed internal factorization so that:
    # - base-only is NEVER closed (barrier)
    # - closure requires querying a subset of bit views (k varies per episode)
    #
    # Let M := max_steps. We use:
    #   X ≅ Base × {0,1}^M × {0,1}
    # where the last bit is noise used for distractors.
    M = int(max_steps)
    if int(M) < 1:
        raise ValueError("max_steps must be >= 1")
    if int(n) < 2 ** (int(M) + 1) or (int(n) % (2 ** (int(M) + 1))) != 0:
        raise ValueError("require n_states divisible by 2^(max_steps+1) to guarantee base barrier")

    n_base = int(n) // (2 ** (int(M) + 1))
    # base buckets are contiguous blocks of size 2^(M+1)
    base_raw = torch.arange(n, dtype=torch.long) // (2 ** (int(M) + 1))

    # Define M useful bits and 1 noise bit within each base bucket.
    bits = []
    for b in range(int(M)):
        # within each base bucket, b-th bit toggles with period 2^(b+1)
        bits.append(((torch.arange(n, dtype=torch.long) // (2**b)) % 2).to(torch.long))
    noise_raw = (torch.arange(n, dtype=torch.long) // (2**int(M))) % 2

    perm = torch.randperm(int(obs_vocab), generator=g).to(torch.long)
    base_lbl = perm[base_raw % int(obs_vocab)]

    tables = torch.zeros((v, n), dtype=torch.long)
    tables[0] = base_lbl

    # Choose useful bit views count k (bounded by max_steps), always >=1.
    k = int(min(1 + int(_randint(g, 0, int(M), (1,)).item()), int(M)))
    useful = torch.randperm(len(bits), generator=g)[:k].tolist()

    # Assign useful bit views to random view rows 1..v-1.
    nonbase_rows = torch.randperm(v - 1, generator=g).to(torch.long) + 1
    useful_rows = nonbase_rows[:k].tolist()
    distract_rows = nonbase_rows[k:].tolist()

    for row, bi in zip(useful_rows, useful):
        tables[int(row)] = perm[bits[int(bi)]]

    # Distractors: per-base random noise refinements (vary but do not help close sigma).
    for row in distract_rows:
        a0 = _randint(g, 0, int(obs_vocab), (n_base,)).to(torch.long)
        a1 = _randint(g, 0, int(obs_vocab), (n_base,)).to(torch.long)
        if bool(ood):
            a0 = perm[a0 % int(obs_vocab)]
            a1 = perm[a1 % int(obs_vocab)]
        tables[int(row)] = torch.where(noise_raw == 0, a0[base_raw], a1[base_raw]).to(torch.long)

    # sigma construction: depends only on the selected useful bits, with per-base flip.
    flip = _randint(g, 0, 2, (n_base,)).to(torch.long)
    if int(fam) == 0:
        # Family 0: XOR over selected bits (parity-like).
        sig = torch.zeros((n,), dtype=torch.long)
        for bi in useful:
            sig ^= bits[int(bi)]
        sig ^= flip[base_raw]
        sigma = sig.to(torch.long)
    else:
        # Family 1: majority-of-bits threshold (different algebraic shape than XOR).
        s = torch.zeros((n,), dtype=torch.long)
        for bi in useful:
            s += bits[int(bi)]
        # threshold at ceil(k/2)
        thr = (int(k) + 1) // 2
        sig = (s >= int(thr)).to(torch.long) ^ flip[base_raw]
        sigma = sig.to(torch.long)

    # Enforce barrier: base-only must not be closed.
    x_probe = int(_randint(g, 0, n, (1,)).item())
    if _is_closed(tables=tables, sigma=sigma, base_view=0, x=x_probe, actions=[]):
        raise RuntimeError("universal episode invariant violated: base-only closed")

    # Sample x
    x = int(_randint(g, 0, n, (1,)).item())
    base_obs = int(tables[0, x].item())

    # Oracle actions (exact): minimal closing plan length <= max_steps (if closable).
    opt_actions = _min_closing_plan(tables=tables, sigma=sigma, base_view=0, x=x, max_steps=int(max_steps))
    if not opt_actions:
        raise RuntimeError("universal episode invariant violated: no closing plan found within max_steps")
    opt_stop_t = int(len(opt_actions))

    # stop action id is always n_views
    stop_action = int(v)

    # Fixed-size action supervision for batching: length == max_steps.
    # Convention: after closure is first achievable at opt_stop_t, the oracle plays STOP forever.
    opt_actions_full = [int(stop_action) for _ in range(int(max_steps))]
    for i, a in enumerate(opt_actions):
        if i >= int(max_steps):
            break
        opt_actions_full[i] = int(a)
    if int(opt_stop_t) < int(max_steps):
        opt_actions_full[int(opt_stop_t)] = int(stop_action)

    return {
        "tables": tables,
        "sigma": sigma,
        "x": torch.tensor(int(x), dtype=torch.long),
        "y": torch.tensor(int(sigma[x].item()), dtype=torch.long),
        "base_obs": torch.tensor(int(base_obs), dtype=torch.long),
        "max_steps": torch.tensor(int(max_steps), dtype=torch.long),
        "stop_action": torch.tensor(int(stop_action), dtype=torch.long),
        "opt_stop_t": torch.tensor(int(opt_stop_t), dtype=torch.long),
        "opt_actions": torch.tensor(opt_actions_full, dtype=torch.long),
        "k_useful": torch.tensor(int(k), dtype=torch.long),
        "family_id": torch.tensor(int(fam), dtype=torch.long),
    }


class V19AlgebraUniversalDataset(Dataset):
    def __init__(
        self,
        *,
        size: int,
        n_states: int,
        n_views: int,
        y_classes: int,
        obs_vocab: int,
        max_steps: int,
        ood: bool,
        seed: int,
    ):
        self.size = int(size)
        self.cfg = AlgebraUniversalEpisodeCfg(
            n_states=int(n_states),
            n_views=int(n_views),
            y_classes=int(y_classes),
            obs_vocab=int(obs_vocab),
            max_steps=int(max_steps),
        )
        self.ood = bool(ood)
        self.seed = int(seed)

    def __len__(self) -> int:
        return int(self.size)

    def __getitem__(self, idx: int):
        return sample_episode(idx=int(idx), cfg=self.cfg, ood=bool(self.ood), seed_base=int(self.seed))
