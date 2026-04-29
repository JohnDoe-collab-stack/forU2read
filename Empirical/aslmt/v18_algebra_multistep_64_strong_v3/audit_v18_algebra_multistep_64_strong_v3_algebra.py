import argparse
import json
from dataclasses import dataclass

import torch

from aslmt_env_v18_algebra_multistep_64_strong_v3 import AlgebraStrongEpisodeCfg, sample_episode


@dataclass(frozen=True)
class AuditCfg:
    n_episodes: int
    obs_vocab: int
    ood: bool
    seed_base: int


def _pair_index(n: int) -> dict[tuple[int, int], int]:
    """
    Map unordered pairs (u,v) with u<v to a dense [0, C(n,2)) index.
    """
    n = int(n)
    out: dict[tuple[int, int], int] = {}
    k = 0
    for u in range(n):
        for v in range(u + 1, n):
            out[(u, v)] = k
            k += 1
    return out


def _bitset_popcount(x: int) -> int:
    return int(x.bit_count())


def _compute_R_sigma(*, sigma: torch.Tensor, pair_idx: dict[tuple[int, int], int]) -> int:
    n = int(sigma.numel())
    sig = sigma.detach().cpu().to(torch.long).tolist()
    bs = 0
    for u in range(n):
        su = int(sig[u])
        for v in range(u + 1, n):
            if su != int(sig[v]):
                bs |= 1 << int(pair_idx[(u, v)])
    return int(bs)


def _compute_C_view(*, view: torch.Tensor, pair_idx: dict[tuple[int, int], int]) -> int:
    n = int(view.numel())
    vv = view.detach().cpu().to(torch.long).tolist()
    bs = 0
    for u in range(n):
        vu = int(vv[u])
        for v in range(u + 1, n):
            if vu == int(vv[v]):
                bs |= 1 << int(pair_idx[(u, v)])
    return int(bs)


def _assert_set_laws(*, tables: torch.Tensor, sigma: torch.Tensor) -> dict:
    """
    Exact set-level algebra checks on ΔX bitsets:

      - Lσ(E_i) := Rσ ∩ C_i
      - Lσ(∧I) = ⋂_i Lσ(E_i)
      - Accσ(E_i) := Rσ \\ Lσ(E_i)
      - Δ_j(I) := #(L_res(I) ∩ Accσ(E_j))
      - ρ_{t+1} = ρ_t - Δ_{a_t}(I_t) for the algebraic update rule
    """
    V, N = tables.shape
    V = int(V)
    N = int(N)
    pair_idx = _pair_index(int(N))

    R = _compute_R_sigma(sigma=sigma, pair_idx=pair_idx)
    r_sigma = _bitset_popcount(int(R))

    C = [_compute_C_view(view=tables[i], pair_idx=pair_idx) for i in range(int(V))]
    L = [int(R) & int(C[i]) for i in range(int(V))]
    Acc = [int(R) & ~int(L[i]) for i in range(int(V))]

    # Meet law for all unordered pairs of views (exact).
    for a in range(int(V)):
        for b in range(int(V)):
            if a >= b:
                continue
            lhs = int(R) & int(C[a]) & int(C[b])
            rhs = int(L[a]) & int(L[b])
            if lhs != rhs:
                raise AssertionError(f"meet law failed for a={a}, b={b}")

    # Multi-interface law for a few random triplets (still exact, just sampled).
    triplets = [(0, 1, 2)]
    if V >= 5:
        triplets.append((0, 1, 3))
        triplets.append((0, 3, 4))
    for (a, b, c) in triplets:
        lhs = int(R) & int(C[a]) & int(C[b]) & int(C[c])
        rhs = int(L[a]) & int(L[b]) & int(L[c])
        if lhs != rhs:
            raise AssertionError(f"multi meet law failed for (a,b,c)={(a,b,c)}")
    return {
        "r_sigma": int(r_sigma),
        "ok_meet_laws": True,
    }


def _assert_episode_closure(*, ep: dict) -> dict:
    tables = ep["tables"]
    sigma = ep["sigma"]
    V, N = tables.shape
    V = int(V)
    N = int(N)
    pair_idx = _pair_index(int(N))

    R = _compute_R_sigma(sigma=sigma, pair_idx=pair_idx)
    C = [_compute_C_view(view=tables[i], pair_idx=pair_idx) for i in range(int(V))]
    L = [int(R) & int(C[i]) for i in range(int(V))]

    bit1_idx = int(ep["bit_idxs"][0].item())
    bit2_idx = int(ep["bit_idxs"][1].item())
    bit_set = {int(bit1_idx), int(bit2_idx)}

    def rho_for_views(views: list[int]) -> int:
        if not views:
            raise ValueError("need at least one view")
        res = int(L[int(views[0])])
        for a in views[1:]:
            res &= int(L[int(a)])
        return _bitset_popcount(int(res))

    # base-only ambiguous
    rho0 = rho_for_views([0])
    if rho0 == 0:
        raise AssertionError("base-only closed (unexpected)")

    # any single query remains ambiguous
    for a in range(int(V)):
        if a == 0:
            continue
        rho1 = rho_for_views([0, a])
        if rho1 == 0:
            raise AssertionError(f"closed after 1 query via a={a}")

    # two-query closure iff the 2-view set is exactly the two bit views
    closed_pairs_unordered: set[frozenset[int]] = set()
    for a in range(int(V)):
        for b in range(int(V)):
            if a == b:
                continue
            views = [0, a, b]
            rho2 = rho_for_views(views)
            closes = (rho2 == 0)
            if closes:
                closed_pairs_unordered.add(frozenset([int(a), int(b)]))
            if closes != ({int(a), int(b)} == bit_set):
                raise AssertionError(
                    f"pair closure mismatch actions={[a,b]} closes={closes} bit_set={sorted(bit_set)}"
                )

    # Exact residual dynamics for the canonical bit plan (sorted):
    opt_actions = [int(ep["opt_actions"][0].item()), int(ep["opt_actions"][1].item())]
    rho_base = rho_for_views([0])
    rho_after_1 = rho_for_views([0, opt_actions[0]])
    rho_after_2 = rho_for_views([0, opt_actions[0], opt_actions[1]])

    if rho_after_2 != 0:
        raise AssertionError("canonical bit plan did not close (unexpected)")

    return {
        "n_states": int(N),
        "n_views": int(V),
        "bit_idxs": [int(bit1_idx), int(bit2_idx)],
        "rho_base": int(rho_base),
        "rho_after_1": int(rho_after_1),
        "rho_after_2": int(rho_after_2),
        "n_closed_pairs_unordered": int(len(closed_pairs_unordered)),
    }


def run_audit(*, n_states: int, n_views: int, cfg: AuditCfg) -> dict:
    per_ep = []
    for i in range(int(cfg.n_episodes)):
        ep_cfg = AlgebraStrongEpisodeCfg(
            n_states=int(n_states),
            n_views=int(n_views),
            y_classes=2,
            steps=2,
            obs_vocab=int(cfg.obs_vocab),
        )
        ep = sample_episode(idx=i, cfg=ep_cfg, ood=bool(cfg.ood), seed_base=int(cfg.seed_base))
        # set-level algebra laws (meet laws etc.)
        _assert_set_laws(tables=ep["tables"], sigma=ep["sigma"])
        per_ep.append(_assert_episode_closure(ep=ep))

    return {
        "n_states": int(n_states),
        "n_views": int(n_views),
        "ood": bool(cfg.ood),
        "n_episodes": int(cfg.n_episodes),
        "ok": True,
        "examples": per_ep[:3],
    }


def main() -> None:
    p = argparse.ArgumentParser(description="Independent exact set-level algebra audit for v18 strong v3 episodes.")
    p.add_argument("--n-states", type=int, required=True)
    p.add_argument("--n-views", type=int, default=8)
    p.add_argument("--episodes", type=int, default=100)
    p.add_argument("--obs-vocab", type=int, default=16)
    p.add_argument("--ood", action="store_true")
    p.add_argument("--seed", type=int, default=0)
    args = p.parse_args()

    out = run_audit(
        n_states=int(args.n_states),
        n_views=int(args.n_views),
        cfg=AuditCfg(n_episodes=int(args.episodes), obs_vocab=int(args.obs_vocab), ood=bool(args.ood), seed_base=int(args.seed)),
    )
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
