import argparse
import json
from dataclasses import dataclass

import torch

from aslmt_env_v18_algebra_multistep_64_strong import AlgebraStrongEpisodeCfg, sample_episode


@dataclass(frozen=True)
class AuditCfg:
    n_episodes: int
    obs_vocab: int
    ood: bool
    seed_base: int


def _candidate_mask(
    *,
    tables: torch.Tensor,  # (V,N)
    base_obs: int,
    actions: list[int],
    responses: list[int],
) -> torch.Tensor:
    v, _ = tables.shape
    m = tables[0].eq(int(base_obs))
    for a, r in zip(actions, responses):
        a = int(a)
        if a < 0 or a >= int(v):
            raise ValueError(f"action out of range: {a} for n_views={v}")
        m = m & tables[a].eq(int(r))
    return m


def _sigma_ambiguity(*, sigma: torch.Tensor, cand_mask: torch.Tensor) -> int:
    vals = sigma[cand_mask]
    if int(vals.numel()) == 0:
        return 0
    return int(torch.unique(vals).numel())


def _residual_rho_after(
    *,
    tables: torch.Tensor,  # (V,N)
    sigma: torch.Tensor,  # (N,)
    x: int,
    actions: list[int],
) -> int:
    base_obs = int(tables[0, int(x)].item())
    responses = [int(tables[int(a), int(x)].item()) for a in actions]
    cand = _candidate_mask(tables=tables, base_obs=base_obs, actions=actions, responses=responses)
    amb = _sigma_ambiguity(sigma=sigma, cand_mask=cand)
    if amb <= 1:
        return 0
    # For y_classes=2, residual ambiguity==2 corresponds to rho>0. Return amb as a proxy.
    return int(amb)


def _assert_episode_invariants(*, ep: dict, v: int) -> dict:
    tables = ep["tables"]
    sigma = ep["sigma"]
    x = int(ep["x"].item())
    base_obs = int(ep["base_obs"].item())
    bit_idxs = [int(ep["bit_idxs"][0].item()), int(ep["bit_idxs"][1].item())]
    bit_set = set(bit_idxs)

    # Base-only must be ambiguous.
    cand0 = _candidate_mask(tables=tables, base_obs=base_obs, actions=[], responses=[])
    if _sigma_ambiguity(sigma=sigma, cand_mask=cand0) <= 1:
        raise AssertionError("base-only closed (unexpected)")

    # Any single view must be ambiguous.
    for a in range(int(v)):
        r = int(tables[a, x].item())
        cand1 = _candidate_mask(tables=tables, base_obs=base_obs, actions=[a], responses=[r])
        if _sigma_ambiguity(sigma=sigma, cand_mask=cand1) <= 1:
            raise AssertionError(f"closed after 1 query via a={a}")

    # Exactly one unordered pair closes: the two bit views.
    closes_pairs_unordered: set[frozenset[int]] = set()
    for a in range(int(v)):
        for b in range(int(v)):
            if a == b:
                continue
            actions = [a, b]
            rho = _residual_rho_after(tables=tables, sigma=sigma, x=x, actions=actions)
            closes = (rho == 0)
            if closes:
                closes_pairs_unordered.add(frozenset([int(a), int(b)]))
            if closes != (set(actions) == bit_set):
                raise AssertionError(
                    f"pair closure mismatch actions={actions} closes={closes} bit_set={sorted(bit_set)}"
                )

    return {
        "bit_idxs": bit_idxs,
        "n_closed_pairs_unordered": len(closes_pairs_unordered),
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
        per_ep.append(_assert_episode_invariants(ep=ep, v=int(n_views)))

    return {
        "n_states": int(n_states),
        "n_views": int(n_views),
        "ood": bool(cfg.ood),
        "n_episodes": int(cfg.n_episodes),
        "ok": True,
        "examples": per_ep[:3],
    }


def main() -> None:
    p = argparse.ArgumentParser(description="Independent algebra/closure audit for v18 strong v2 episodes.")
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
