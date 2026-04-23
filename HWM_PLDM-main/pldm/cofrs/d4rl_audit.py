from __future__ import annotations

from dataclasses import asdict
from typing import Any

import numpy as np
import torch

from pldm.logger import Logger
from pldm.planning.planners.two_lvl_planner import TwoLvlPlanner


def _stack_obs_if_needed(obs: torch.Tensor, *, stack_states: int) -> torch.Tensor:
    if int(stack_states) <= 1:
        return obs
    return torch.cat([obs] * int(stack_states), dim=1)


@torch.no_grad()
def run_cofrs_audit_hierarchical_d4rl(
    *,
    planning_evaluator: Any,
    config: Any,
) -> dict[str, Any]:
    """
    Behavioral audit (small-N) for the hierarchical planning loop.

    This audit is intentionally tiny and cheap:
    - we instantiate the hierarchical planner on a small number of envs,
    - we compute the L2 subgoal once (via L2 plan),
    - we run L1 planning twice: with the original subgoal, and with a swapped subgoal,
    - we log how strongly the first action responds to the swapped mediator (subgoal).

    The result is a concrete "mediator effect" signal at the behavior level.
    """

    if not getattr(config, "enabled", False):
        return {}
    if not getattr(config, "audit_hierarchical_d4rl", True):
        return {}

    n_envs = int(getattr(config, "audit_n_envs", 2))
    if n_envs <= 0:
        out = {
            "cofrs/audit_skipped": 1.0,
            "cofrs/audit_skip_reason": "invalid_config",
            "cofrs/audit_n_envs": int(n_envs),
        }
        Logger.run().log(out, commit=True)
        return out

    envs = list(getattr(planning_evaluator, "envs", []))[:n_envs]
    if len(envs) < 2:
        out = {
            "cofrs/audit_skipped": 1.0,
            "cofrs/audit_skip_reason": "need_at_least_two_envs",
            "cofrs/audit_n_envs": int(len(envs)),
        }
        Logger.run().log(out, commit=True)
        return out

    device = planning_evaluator.device if hasattr(planning_evaluator, "device") else torch.device("cuda")

    # Build hierarchical planner for the selected envs.
    h_planner = planning_evaluator._construct_h_planner(n_envs=len(envs))
    if not isinstance(h_planner, TwoLvlPlanner):
        out = {
            "cofrs/audit_skipped": 1.0,
            "cofrs/audit_skip_reason": "unexpected_planner_type",
            "cofrs/audit_n_envs": int(len(envs)),
            "cofrs/audit_planner_type": type(h_planner).__name__,
        }
        Logger.run().log(out, commit=True)
        return out

    # Initial observation.
    obs0 = torch.stack([e.get_obs() for e in envs]).float()
    obs0 = _stack_obs_if_needed(obs0, stack_states=int(planning_evaluator.config.stack_states))

    # Proprio / location for L1 backbone if used.
    model = planning_evaluator.model
    if model.level1.using_proprio_pos:
        curr_proprio_pos = torch.from_numpy(np.stack([e.get_proprio_pos(normalized=True) for e in envs])).float()
    else:
        curr_proprio_pos = None
    if model.level1.using_proprio_vel:
        curr_proprio_vel = torch.from_numpy(np.stack([e.get_proprio_vel(normalized=True) for e in envs])).float()
    else:
        curr_proprio_vel = None
    if model.level1.using_location:
        curr_locations = torch.from_numpy(np.stack([e.get_pos(normalized=True) for e in envs])).float()
    else:
        curr_locations = None

    proprio_l1 = None
    if curr_proprio_pos is not None and curr_proprio_vel is not None:
        proprio_l1 = torch.cat([curr_proprio_pos, curr_proprio_vel], dim=-1).to(device)
    elif curr_proprio_pos is not None:
        proprio_l1 = curr_proprio_pos.to(device)
    elif curr_proprio_vel is not None:
        proprio_l1 = curr_proprio_vel.to(device)

    locations_cuda = curr_locations.to(device) if curr_locations is not None else None

    # Compute backbone output (same path as TwoLvlPlanner.plan).
    backbone_output = h_planner.l1_planner.model.backbone(
        obs0.to(device), proprio=proprio_l1, locations=locations_cuda
    )

    # L2 planning (macro plan) to get the first subgoal representation.
    plan_size_l2 = int(planning_evaluator.config.level2.max_plan_length)
    l2_result = h_planner.l2_planner.plan(
        current_state=backbone_output,
        plan_size=plan_size_l2,
        repr_input=True,
    )

    # This matches TwoLvlPlanner.plan: subgoal is the first predicted obs token after the current one.
    subgoal = l2_result.pred_obs[1].detach()

    # Base L1 plan with the true subgoal.
    h_planner.l1_planner.reset_targets(subgoal, repr_input=True)
    l1_base = h_planner.l1_planner.plan(
        current_state=backbone_output,
        plan_size=int(h_planner.l2_step_skip),
        repr_input=True,
        curr_proprio_pos=curr_proprio_pos,
        curr_proprio_vel=curr_proprio_vel,
    )
    a_base = l1_base.actions[:, 0].detach()

    # Swapped subgoal: behavioral counterfactual on the mediator.
    g = torch.Generator(device=subgoal.device)
    g.manual_seed(int(getattr(config, "audit_seed", 0)))
    perm = torch.randperm(subgoal.shape[0], generator=g, device=subgoal.device)
    subgoal_swapped = subgoal[perm]

    h_planner.l1_planner.reset_targets(subgoal_swapped, repr_input=True)
    l1_swap = h_planner.l1_planner.plan(
        current_state=backbone_output,
        plan_size=int(h_planner.l2_step_skip),
        repr_input=True,
        curr_proprio_pos=curr_proprio_pos,
        curr_proprio_vel=curr_proprio_vel,
    )
    a_swap = l1_swap.actions[:, 0].detach()

    deltas = torch.norm(a_base - a_swap, dim=-1)  # (B,)
    eps = float(getattr(config, "action_change_eps", 1e-6))
    changed = (deltas > eps).to(torch.float32)

    # Swap-follow: compare a_swap against the permuted base action sequence.
    perm_eps = float(getattr(config, "action_perm_eps", eps))
    a_perm = a_base[perm]
    perm_deltas = torch.norm(a_swap - a_perm, dim=-1)
    swap_follows_perm = (perm_deltas <= perm_eps).to(torch.float32)

    out = {
        "cofrs/audit_n_envs": int(subgoal.shape[0]),
        "cofrs/subgoal_swap_action_delta_l2_mean": float(deltas.mean().item()),
        "cofrs/subgoal_swap_action_delta_l2_min": float(deltas.min().item()),
        "cofrs/subgoal_swap_action_delta_l2_max": float(deltas.max().item()),
        "cofrs/subgoal_swap_action_changed_frac": float(changed.mean().item()),
        "cofrs/subgoal_swap_action_delta_vs_perm_l2_mean": float(perm_deltas.mean().item()),
        "cofrs/subgoal_swap_action_follows_perm_frac": float(swap_follows_perm.mean().item()),
    }

    if bool(getattr(config, "audit_include_ablation", True)):
        # Ablated subgoal: constant/zero mediator counterfactual.
        subgoal_ablated = torch.zeros_like(subgoal)
        h_planner.l1_planner.reset_targets(subgoal_ablated, repr_input=True)
        l1_abl = h_planner.l1_planner.plan(
            current_state=backbone_output,
            plan_size=int(h_planner.l2_step_skip),
            repr_input=True,
            curr_proprio_pos=curr_proprio_pos,
            curr_proprio_vel=curr_proprio_vel,
        )
        a_abl = l1_abl.actions[:, 0].detach()
        abl_deltas = torch.norm(a_base - a_abl, dim=-1)
        abl_changed = (abl_deltas > eps).to(torch.float32)
        out.update(
            {
                "cofrs/subgoal_abl_action_delta_l2_mean": float(abl_deltas.mean().item()),
                "cofrs/subgoal_abl_action_delta_l2_min": float(abl_deltas.min().item()),
                "cofrs/subgoal_abl_action_delta_l2_max": float(abl_deltas.max().item()),
                "cofrs/subgoal_abl_action_changed_frac": float(abl_changed.mean().item()),
            }
        )

    # Log as a single committed entry.
    Logger.run().log(out, commit=True)
    Logger.run().log_summary(
        {"cofrs/config": asdict(config)} if hasattr(config, "__dataclass_fields__") else {},
        commit=True,
    )

    return out
