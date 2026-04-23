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

## Reference run (solid, zread)

This folder includes a `zread` variant where the query action is a readout from the discrete mediator `z`
(one-hot), rather than a readout from continuous `z_logits`.

Run directory:

- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_law_v3b_unified_v2_strong_qforced_zread_solid_20260423_102039_9f958bfafaad`

Master JSONL:

- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_law_v3b_unified_v2_strong_qforced_zread_solid_20260423_102039_9f958bfafaad/law_v3b_unified_v2_strong_qforced_zread_solid_master_20260423_102039_9f958bfafaad.jsonl`

Snapshot verifier:

- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/snapshots/aslmt_law_v3b_unified_v2_strong_qforced_zread_solid_20260423_102039_9f958bfafaad/verify_aslmt_law_v3b_unified_v2_strong_qforced_matrix.py`

Re-run the verifier:

```bash
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/snapshots/aslmt_law_v3b_unified_v2_strong_qforced_zread_solid_20260423_102039_9f958bfafaad/verify_aslmt_law_v3b_unified_v2_strong_qforced_matrix.py \
  --master-jsonl /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_law_v3b_unified_v2_strong_qforced_zread_solid_20260423_102039_9f958bfafaad/law_v3b_unified_v2_strong_qforced_zread_solid_master_20260423_102039_9f958bfafaad.jsonl \
  --profile solid \
  --min-seeds 5 \
  --n-classes-list 8 \
  --z-policy A1
```

### Observed strict behavior (ref z=n)

For `n=8, z=8, seed=0..4`, both splits (IID and OOD) satisfy:

- `q_acc_min = 1.0`, `res_acc_min = 1.0`, `z_acc_min = 1.0`
- `query_action_rate` is balanced (approx. 0.48–0.52)
- barriers are valid (`obs_*_barrier_ok = true`)
- `A_both_image_pair_rate = 1.0`, `A_both_cue_pair_rate = 1.0`
- baselines are zero (`B_* = 0.0`)
- ablation is zero (`A_ablated_* = 0.0`)
- swap follows and swap-orig breaks (`swap_follow = 1.0`, `swap_orig = 0.0`)
