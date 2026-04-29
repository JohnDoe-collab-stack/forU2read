import argparse
import json
from dataclasses import dataclass

import torch

from aslmt_env_v19_algebra_universal import AlgebraUniversalEpisodeCfg, sample_episode


@dataclass(frozen=True)
class AuditCfg:
    n_episodes: int
    obs_vocab: int
    ood: bool
    seed_base: int
    max_steps: int


def _pair_index(n: int) -> dict[tuple[int, int], int]:
    out: dict[tuple[int, int], int] = {}
    k = 0
    for u in range(int(n)):
        for v in range(u + 1, int(n)):
            out[(u, v)] = k
            k += 1
    return out


def _popcount(x: int) -> int:
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


def _sigma_ambiguity(*, sigma: torch.Tensor, cand_mask: torch.Tensor) -> int:
    vals = sigma[cand_mask]
    if int(vals.numel()) == 0:
        return 0
    return int(torch.unique(vals).numel())


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


def _assert_algebra_laws(*, tables: torch.Tensor, sigma: torch.Tensor) -> None:
    V, N = tables.shape
    V = int(V)
    N = int(N)
    pair_idx = _pair_index(int(N))
    R = _compute_R_sigma(sigma=sigma, pair_idx=pair_idx)
    C = [_compute_C_view(view=tables[i], pair_idx=pair_idx) for i in range(int(V))]
    L = [int(R) & int(C[i]) for i in range(int(V))]

    # meet law: Lσ(E_a ∧ E_b) = Lσ(E_a) ∩ Lσ(E_b)
    for a in range(int(V)):
        for b in range(int(V)):
            if a >= b:
                continue
            lhs = int(R) & int(C[a]) & int(C[b])
            rhs = int(L[a]) & int(L[b])
            if lhs != rhs:
                raise AssertionError(f"meet law failed for a={a}, b={b}")


def _episode_rho_trace(*, tables: torch.Tensor, sigma: torch.Tensor, x: int, actions: list[int]) -> list[int]:
    """
    Transcript-relative residual trace: measure ambiguity (proxy for rho) on the *candidate set*
    induced by the actual responses for x.
    """
    V, _ = tables.shape
    V = int(V)
    x = int(x)
    base_obs = int(tables[0, x].item())

    actions_prefix: list[int] = []
    responses_prefix: list[int] = []

    out = []
    for a in [None] + [int(a) for a in actions]:
        cand = _candidate_mask(tables=tables, base_view=0, base_obs=base_obs, actions=actions_prefix, responses=responses_prefix)
        amb = _sigma_ambiguity(sigma=sigma, cand_mask=cand)
        out.append(int(amb))
        if a is None:
            continue
        if int(a) == int(V):
            continue
        actions_prefix.append(int(a))
        responses_prefix.append(int(tables[int(a), x].item()))
    return out


def run_audit(*, n_states: int, n_views: int, y_classes: int, cfg: AuditCfg) -> dict:
    per_ep = []
    for i in range(int(cfg.n_episodes)):
        ep_cfg = AlgebraUniversalEpisodeCfg(
            n_states=int(n_states),
            n_views=int(n_views),
            y_classes=int(y_classes),
            obs_vocab=int(cfg.obs_vocab),
            max_steps=int(cfg.max_steps),
        )
        ep = sample_episode(idx=i, cfg=ep_cfg, ood=bool(cfg.ood), seed_base=int(cfg.seed_base))
        tables = ep["tables"]
        sigma = ep["sigma"]
        x = int(ep["x"].item())

        _assert_algebra_laws(tables=tables, sigma=sigma)
        opt_actions = ep["opt_actions"].detach().cpu().to(torch.long).tolist()
        # opt_actions is padded with STOP at the end; we keep only max_steps elements
        opt_actions = [int(a) for a in opt_actions[: int(cfg.max_steps)]]
        rho_trace = _episode_rho_trace(tables=tables, sigma=sigma, x=x, actions=opt_actions)

        per_ep.append(
            {
                "family_id": int(ep["family_id"].item()),
                "k_useful": int(ep["k_useful"].item()),
                "opt_stop_t": int(ep["opt_stop_t"].item()),
                "rho_trace": rho_trace[: min(5, len(rho_trace))],
            }
        )

    return {
        "n_states": int(n_states),
        "n_views": int(n_views),
        "y_classes": int(y_classes),
        "ood": bool(cfg.ood),
        "n_episodes": int(cfg.n_episodes),
        "max_steps": int(cfg.max_steps),
        "ok": True,
        "examples": per_ep[:3],
    }


def main() -> None:
    p = argparse.ArgumentParser(description="Independent algebra audit for v19 universal v1 episodes.")
    p.add_argument("--n-states", type=int, required=True)
    p.add_argument("--n-views", type=int, default=8)
    p.add_argument("--y-classes", type=int, default=2)
    p.add_argument("--episodes", type=int, default=100)
    p.add_argument("--obs-vocab", type=int, default=16)
    p.add_argument("--max-steps", type=int, default=3)
    p.add_argument("--ood", action="store_true")
    p.add_argument("--seed", type=int, default=0)
    args = p.parse_args()

    out = run_audit(
        n_states=int(args.n_states),
        n_views=int(args.n_views),
        y_classes=int(args.y_classes),
        cfg=AuditCfg(
            n_episodes=int(args.episodes),
            obs_vocab=int(args.obs_vocab),
            ood=bool(args.ood),
            seed_base=int(args.seed),
            max_steps=int(args.max_steps),
        ),
    )
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
