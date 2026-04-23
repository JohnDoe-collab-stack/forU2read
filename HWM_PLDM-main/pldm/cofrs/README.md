# COFRS hooks (HWM_PLDM)

This folder adds two evaluation-time hooks for *hierarchical planning as a mediated solver*:

1. **Mediator audit (swap/ablation on the subgoal)**: shows whether the first low-level action
   actually depends on the level-2 subgoal (mediator).
2. **Closure probe (flat vs hierarchical, same-start)**: small-N comparison on the *same* env
   instances (state is restored between runs) to estimate whether hierarchical planning is
   operationally required in a given batch of episodes.

These hooks are intentionally small and cheap by default; you can scale them up explicitly.

## How to enable

In `EvalConfig` (`pldm/evaluation/evaluator.py`), set:

- `cofrs.enabled = true`
- `cofrs.audit_hierarchical_d4rl = true` to enable the mediator audit.
- `cofrs.closure_probe_enabled = true` to enable the flat-vs-hierarchical probe.

Key knobs live in `pldm/cofrs/config.py`.

## Logged metrics

Mediator audit (`run_cofrs_audit_hierarchical_d4rl`):

- `cofrs/subgoal_swap_action_delta_*`: action change under subgoal swap.
- `cofrs/subgoal_swap_action_follows_perm_frac`: “swap-follow” diagnostic against the swap permutation.
- `cofrs/subgoal_abl_action_delta_*`: action change under subgoal ablation (if enabled).

Closure probe (`run_cofrs_closure_probe_flat_vs_hierarchical`):

- `cofrs/closure_probe_*`: success rates for flat and hierarchical planning from the same starts.

