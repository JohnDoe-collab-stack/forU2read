import argparse
import json
from dataclasses import dataclass

import torch

from aslmt_env_v19_algebra_universal_v4_4 import AlgebraUniversalEpisodeCfg, sample_episode
from aslmt_oracle_v19_algebra_universal_v4_4_common import candidate_mask, sigma_ambiguity


@dataclass(frozen=True)
class AuditCfg:
    n_episodes: int
    obs_vocab: int
    ood: bool
    seed_base: int
    max_steps: int


def _assert_base_barrier(*, tables: torch.Tensor, sigma: torch.Tensor) -> None:
    """
    Strict barrier check (v4.4):
    for every observable base label value, base-only candidate set must have ambiguity==2.
    """
    base_row = tables[0].detach().cpu().to(torch.long)
    sigma = sigma.detach().cpu().to(torch.long)
    for base_obs in torch.unique(base_row).tolist():
        base_obs = int(base_obs)
        cand = candidate_mask(tables=tables, base_obs=base_obs, actions=[], responses=[])
        amb = int(sigma_ambiguity(sigma=sigma, cand_mask=cand))
        if amb != 2:
            raise AssertionError(f"base barrier violated for base_obs={base_obs}: ambiguity={amb}")


def _episode_amb_trace(*, tables: torch.Tensor, sigma: torch.Tensor, x: int, actions: list[int]) -> list[int]:
    V, _ = tables.shape
    V = int(V)
    x = int(x)
    base_obs = int(tables[0, x].item())
    actions_prefix: list[int] = []
    responses_prefix: list[int] = []
    out = []
    # We record ambiguity for:
    # - base only
    # - after each queried action is applied
    out.append(int(sigma_ambiguity(sigma=sigma, cand_mask=candidate_mask(tables=tables, base_obs=int(base_obs), actions=[], responses=[]))))
    for a in [int(a) for a in actions]:
        cand = candidate_mask(tables=tables, base_obs=int(base_obs), actions=actions_prefix, responses=responses_prefix)
        if int(a) == int(V):
            # STOP does not refine; keep ambiguity unchanged
            out.append(int(sigma_ambiguity(sigma=sigma, cand_mask=cand)))
            continue
        actions_prefix.append(int(a))
        responses_prefix.append(int(tables[int(a), x].item()))
        cand2 = candidate_mask(tables=tables, base_obs=int(base_obs), actions=actions_prefix, responses=responses_prefix)
        out.append(int(sigma_ambiguity(sigma=sigma, cand_mask=cand2)))
    return out


def _assert_transcript_well_formed(*, actions: list[int], V: int, opt_stop_t: int) -> None:
    stop = int(V)
    # views must be non-base and not repeated until STOP
    seen: set[int] = set()
    stopped = False
    for t, a in enumerate(actions):
        a = int(a)
        if stopped:
            if a != stop:
                raise AssertionError("STOP must persist after first STOP")
            continue
        if a == stop:
            stopped = True
            continue
        if a <= 0 or a >= V:
            raise AssertionError(f"invalid view action: {a} for V={V}")
        if a in seen:
            raise AssertionError(f"repeated view action: {a}")
        seen.add(int(a))
    # opt_stop_t is the earliest t where STOP becomes correct; it must be within budget.
    if int(opt_stop_t) < 0 or int(opt_stop_t) > len(actions):
        raise AssertionError("opt_stop_t out of range")


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

        _assert_base_barrier(tables=tables, sigma=sigma)
        opt_actions = ep["opt_actions"].detach().cpu().to(torch.long).tolist()
        opt_actions = [int(a) for a in opt_actions[: int(cfg.max_steps)]]
        amb_trace = _episode_amb_trace(tables=tables, sigma=sigma, x=x, actions=opt_actions)
        _assert_transcript_well_formed(actions=opt_actions, V=int(n_views), opt_stop_t=int(ep["opt_stop_t"].item()))
        # Closure must be reached: final ambiguity is 1.
        if int(amb_trace[-1]) != 1:
            raise AssertionError(f"closure not reached: amb_trace={amb_trace}")
        # Ambiguity must not increase along the oracle transcript.
        for u, v in zip(amb_trace, amb_trace[1:]):
            if int(v) > int(u):
                raise AssertionError(f"ambiguity increased along transcript: {amb_trace}")

        per_ep.append(
            {
                "family_id": int(ep["family_id"].item()),
                "k_useful": int(ep["k_useful"].item()),
                "opt_stop_t": int(ep["opt_stop_t"].item()),
                "amb_trace": amb_trace[: min(6, len(amb_trace))],
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
    p = argparse.ArgumentParser(description="Independent algebra audit for v19 universal v4.4 episodes.")
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
