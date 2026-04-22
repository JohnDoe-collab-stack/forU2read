# law_v3b_unified_v2_strong_qforced_zquery

This is a strict variant of `law_v3b_unified_v2_strong` whose goal is to make the query action operationally necessary.

Key change (compared to `law_v3b_unified_v2_strong`):

- The response bit is no longer an invertible flip of `k` under the wrong action.
- If the queried interface is wrong, the response bit carries no information about `k`.

Additional change (compared to `law_v3b_unified_v2_strong_qforced`):

- The query logits are computed from the internal `z` logits (cue memory) rather than directly from raw `(x,y)` marker coordinates.
  This matches the intended v3b spirit: action is a function of internal state, not a separate parallel classifier.

Motivation:

- In the flip design, if the model can infer `h % 2` from the cue, then `k` can be recovered from `(res_bit, h % 2)` even when the action is wrong.
- This can allow the model to solve the task while keeping the learned query action degenerate (for example always action 0), which defeats the intended autoreflexive pressure.

This folder only introduces new scripts and does not modify historical scripts used for cited runs.

Operational note:
- Use `aslmt_campaign_law_v3b_unified_v2_strong_qforced_matrix_diagstop_v2.py` for `profile=solid` runs.
  It fixes the partial verify tool call to use the qforced verifier (the original diagstop script pointed to the strong verifier).
