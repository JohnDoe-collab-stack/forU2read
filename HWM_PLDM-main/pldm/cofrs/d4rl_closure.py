from __future__ import annotations

from dataclasses import asdict
from typing import Any

import numpy as np
import torch

from pldm.logger import Logger


def _snapshot_env_state_for_pointmaze(env: Any) -> dict[str, Any]:
    """
    Snapshot a minimal state sufficient to restore a pointmaze env deterministically.

    This repo wraps D4RL PointMaze environments; for these, `set_state(qpos, qvel)`
    is used throughout the codebase (see env generator). We snapshot from `_get_obs()`
    to avoid relying on MuJoCo internals being present on wrappers.
    """
    base = env.unwrapped
    obs = np.asarray(base._get_obs(), dtype=np.float32)
    qpos = obs[:2].copy()
    qvel = obs[2:].copy()
    target = np.asarray(base.get_target(), dtype=np.float32).copy()
    return {"qpos": qpos, "qvel": qvel, "target": target}


def _restore_env_state_for_pointmaze(env: Any, snap: dict[str, Any]) -> None:
    # `reset()` is important to restore internal time/episode counters.
    env.reset()
    base = env.unwrapped
    base.set_state(qpos=snap["qpos"], qvel=snap["qvel"])
    base.set_target(snap["target"])


def _success_rate_from_reward_history(reward_history: list[torch.Tensor]) -> float:
    if not reward_history:
        return 0.0
    # reward is binary (1 iff goal reached)
    rewards = torch.stack([r.detach().cpu() for r in reward_history], dim=0)  # (T, B)
    success = (rewards > 0).any(dim=0).to(torch.float32)
    return float(success.mean().item())


@torch.no_grad()
def run_cofrs_closure_probe_flat_vs_hierarchical(
    *,
    planning_evaluator: Any,
    config: Any,
) -> dict[str, Any]:
    """
    Small-N closure probe: compare flat L1 planning against hierarchical planning
    on the same env instances (restoring env state between runs).

    This is not wired into the default evaluation path because it can be expensive.
    It is meant as an explicit probe that you enable when you want a direct,
    same-start comparison.
    """
    if not getattr(config, "enabled", False):
        return {}
    if not bool(getattr(config, "closure_probe_enabled", False)):
        return {}

    n_envs = int(getattr(config, "closure_probe_n_envs", 2))
    max_steps = int(getattr(config, "closure_probe_max_steps", 100))
    if n_envs <= 0 or max_steps <= 0:
        out = {
            "cofrs/closure_probe_skipped": 1.0,
            "cofrs/closure_probe_skip_reason": "invalid_config",
            "cofrs/closure_probe_n_envs": int(n_envs),
            "cofrs/closure_probe_max_steps": int(max_steps),
        }
        Logger.run().log(out, commit=True)
        return out

    envs = list(getattr(planning_evaluator, "envs", []))[:n_envs]
    if not envs:
        out = {
            "cofrs/closure_probe_skipped": 1.0,
            "cofrs/closure_probe_skip_reason": "no_envs",
            "cofrs/closure_probe_n_envs": int(0),
            "cofrs/closure_probe_max_steps": int(max_steps),
        }
        Logger.run().log(out, commit=True)
        return out

    # Snapshot once and restore between probes.
    snaps = [_snapshot_env_state_for_pointmaze(e) for e in envs]

    # Flat (L1) planning.
    flat_planner = planning_evaluator._construct_planner(n_envs=len(envs))
    flat_result = planning_evaluator._perform_mpc(
        planner=flat_planner,
        envs=envs,
        bilevel_planning=False,
        max_steps_override=max_steps,
    )
    flat_success = _success_rate_from_reward_history(flat_result.reward_history)

    for e, s in zip(envs, snaps):
        _restore_env_state_for_pointmaze(e, s)

    # Hierarchical planning (bilevel planner) with the same explicit step budget.
    h_planner = planning_evaluator._construct_h_planner(n_envs=len(envs))
    h_result = planning_evaluator._perform_mpc(
        planner=h_planner,
        envs=envs,
        bilevel_planning=True,
        max_steps_override=max_steps,
    )
    h_success = _success_rate_from_reward_history(h_result.reward_history)

    for e, s in zip(envs, snaps):
        _restore_env_state_for_pointmaze(e, s)

    out = {
        "cofrs/closure_probe_n_envs": int(len(envs)),
        "cofrs/closure_probe_max_steps": int(max_steps),
        "cofrs/closure_probe_flat_success_rate": float(flat_success),
        "cofrs/closure_probe_hier_success_rate": float(h_success),
        "cofrs/closure_probe_success_delta": float(h_success - flat_success),
    }

    Logger.run().log(out, commit=True)
    Logger.run().log_summary(
        {"cofrs/config": asdict(config)} if hasattr(config, "__dataclass_fields__") else {},
        commit=True,
    )

    return out
