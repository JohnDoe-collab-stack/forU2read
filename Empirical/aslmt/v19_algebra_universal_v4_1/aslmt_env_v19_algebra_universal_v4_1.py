from dataclasses import dataclass

import torch
from torch.utils.data import Dataset

from aslmt_oracle_v19_algebra_universal_v4_1_common import (
    HorizonOracleCfg,
    candidate_mask,
    oracle_allowed_actions,
    sigma_ambiguity,
)


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


def _is_closed(
    *,
    tables: torch.Tensor,  # (V,N)
    sigma: torch.Tensor,  # (N,)
    base_obs: int,
    actions: list[int],
    responses: list[int],
) -> bool:
    cand = candidate_mask(tables=tables, base_obs=int(base_obs), actions=list(actions), responses=list(responses))
    return int(sigma_ambiguity(sigma=sigma, cand_mask=cand)) == 1


def _rollout_oracle_policy(
    *,
    tables: torch.Tensor,  # (V,N)
    sigma: torch.Tensor,  # (N,)
    x: int,
    base_obs: int,
    max_steps: int,
    oracle_cfg: HorizonOracleCfg,
) -> tuple[list[int], int]:
    """
    Online oracle: at each step, choose an action from the horizon-optimal set computed from the
    current transcript prefix, then reveal the actual response for x and continue.

    Returns:
      opt_actions_full: length == max_steps, padded with STOP from the first time STOP is correct.
      opt_stop_t: earliest t where closure already holds (so STOP is correct at t).
    """
    V, _ = tables.shape
    V = int(V)
    stop = int(V)

    actions: list[int] = []
    responses: list[int] = []

    opt_actions_full = [int(stop) for _ in range(int(max_steps))]
    opt_stop_t: int | None = None

    for t in range(int(max_steps)):
        if _is_closed(tables=tables, sigma=sigma, base_obs=int(base_obs), actions=actions, responses=responses):
            if opt_stop_t is None:
                opt_stop_t = int(t)
            opt_actions_full[t] = int(stop)
            continue

        allowed = oracle_allowed_actions(
            tables=tables,
            sigma=sigma,
            base_obs=int(base_obs),
            actions_prefix=list(actions),
            responses_prefix=list(responses),
            remaining_steps=int(max_steps - t),
            cfg=oracle_cfg,
        )
        # Under the intended construction, STOP is not allowed unless already closed.
        allowed = [int(a) for a in allowed if int(a) != int(stop)]
        if not allowed:
            # Fallback: pick the smallest available view (never base, never repeated).
            allowed = [a for a in range(1, int(V)) if a not in set(actions)]
        if not allowed:
            raise RuntimeError("oracle failure: no allowed action available")

        a = int(min(allowed))
        actions.append(int(a))
        responses.append(int(tables[int(a), int(x)].item()))
        opt_actions_full[t] = int(a)

    if opt_stop_t is None:
        # Closure must be reached within the budget (protocol invariant).
        if _is_closed(tables=tables, sigma=sigma, base_obs=int(base_obs), actions=actions, responses=responses):
            opt_stop_t = int(max_steps)
        else:
            raise RuntimeError("universal episode invariant violated: oracle did not reach closure within max_steps")

    return opt_actions_full, int(opt_stop_t)


def sample_episode(
    *,
    idx: int,
    cfg: AlgebraUniversalEpisodeCfg,
    ood: bool,
    seed_base: int,
) -> dict[str, torch.Tensor]:
    """
    Universal v4.1 episode:

    - Finite latent space X={0..N-1}.
    - Provide (tables, sigma) as cue (full information to compute closure).
    - Base view is row 0.
    - Query loop uses any subset of views to reach closure, then STOP.

    Families (same as v1; v2 fixed horizon-consistent oracle; v3 fixed strict barrier; v4 changes model learning):
    - family_id=0: XOR over k useful bit-views, with per-base flips.
    - family_id=1: threshold/majority over k useful bit-views, with per-base flips.
    """
    n = int(cfg.n_states)
    v = int(cfg.n_views)
    y = int(cfg.y_classes)
    obs_vocab = int(cfg.obs_vocab)
    max_steps = int(cfg.max_steps)
    base_view = int(cfg.base_view)
    if y != 2:
        raise ValueError("v19 universal v4.1 currently requires y_classes=2")
    if base_view != 0:
        raise ValueError("v19 universal v4.1 expects base_view=0")
    if v < 3:
        raise ValueError("need n_views>=3")
    if max_steps < 1:
        raise ValueError("need max_steps>=1")
    if obs_vocab < 4:
        raise ValueError("obs_vocab too small")

    g = _seeded_gen(int(seed_base) + int(idx) * 9973 + (1337 if bool(ood) else 0))

    fam = int(_randint(g, 0, 2, (1,)).item())
    if bool(ood):
        fam = 1 - fam

    # Enforce a factorization guaranteeing base-only is never closed:
    #   X ≅ Base × {0,1}^M × {0,1}   where M := max_steps
    M = int(max_steps)
    if int(n) < 2 ** (int(M) + 1) or (int(n) % (2 ** (int(M) + 1))) != 0:
        raise ValueError("require n_states divisible by 2^(max_steps+1) to guarantee base barrier")

    n_base = int(n) // (2 ** (int(M) + 1))
    base_raw = torch.arange(n, dtype=torch.long) // (2 ** (int(M) + 1))

    bits = []
    for b in range(int(M)):
        bits.append(((torch.arange(n, dtype=torch.long) // (2**b)) % 2).to(torch.long))
    noise_raw = (torch.arange(n, dtype=torch.long) // (2**int(M))) % 2

    perm = torch.randperm(int(obs_vocab), generator=g).to(torch.long)
    base_lbl = perm[base_raw % int(obs_vocab)]

    tables = torch.zeros((v, n), dtype=torch.long)
    tables[0] = base_lbl

    # Choose useful bit views count k, always >=1 and <=M.
    k = int(min(1 + int(_randint(g, 0, int(M), (1,)).item()), int(M)))
    useful = torch.randperm(len(bits), generator=g)[:k].tolist()

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

    # IMPORTANT (v3): `base_obs` is the *observable* base label (in `0..obs_vocab-1`).
    # We must ensure `σ` depends on the base only through what is *observable* at base time,
    # otherwise closure can fail when multiple `base_raw` buckets share the same `base_obs`.
    flip_lbl = _randint(g, 0, 2, (int(obs_vocab),)).to(torch.long)
    if int(fam) == 0:
        sig = torch.zeros((n,), dtype=torch.long)
        for bi in useful:
            sig ^= bits[int(bi)]
        sig ^= flip_lbl[base_lbl]
        sigma = sig.to(torch.long)
    else:
        s = torch.zeros((n,), dtype=torch.long)
        for bi in useful:
            s += bits[int(bi)]
        thr = (int(k) + 1) // 2
        sig = (s >= int(thr)).to(torch.long) ^ flip_lbl[base_lbl]
        sigma = sig.to(torch.long)

    # Barrier (v3, strict): base-only must never be closed *as seen from base_obs*.
    # I.e. within every observable base label bucket, σ must attain both values {0,1}.
    for b in range(int(obs_vocab)):
        m0 = base_lbl.eq(int(b))
        if int(m0.sum().item()) == 0:
            continue
        if int(torch.unique(sigma[m0]).numel()) != 2:
            raise RuntimeError("universal episode invariant violated: base-only closed for some base_obs")

    x = int(_randint(g, 0, n, (1,)).item())
    base_obs = int(tables[0, x].item())

    oracle_cfg = HorizonOracleCfg(forbid_view0=True, allow_stop_only_if_closed=True)
    opt_actions_full, opt_stop_t = _rollout_oracle_policy(
        tables=tables,
        sigma=sigma,
        x=int(x),
        base_obs=int(base_obs),
        max_steps=int(max_steps),
        oracle_cfg=oracle_cfg,
    )

    stop_action = int(v)
    return {
        "tables": tables,
        "sigma": sigma,
        "x": torch.tensor(int(x), dtype=torch.long),
        "y": torch.tensor(int(sigma[x].item()), dtype=torch.long),
        "base_obs": torch.tensor(int(base_obs), dtype=torch.long),
        "max_steps": torch.tensor(int(max_steps), dtype=torch.long),
        "stop_action": torch.tensor(int(stop_action), dtype=torch.long),
        "opt_stop_t": torch.tensor(int(opt_stop_t), dtype=torch.long),
        "opt_actions": torch.tensor([int(a) for a in opt_actions_full], dtype=torch.long),
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
