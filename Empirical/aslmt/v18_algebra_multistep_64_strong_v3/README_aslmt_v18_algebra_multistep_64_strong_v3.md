# ASLMT v18 — Algebra Multistep (64) **STRONG v3**

This folder is a strict follow-up to `v18_algebra_multistep_64_strong_v2`.

**Naming note:** the `..._64...` substring is a legacy label in this family name; the actual latent size is controlled by the run argument `--n-states` and is recorded per row as `n_states` in the master JSONL.

**Traceability note:** `v2` produced a cited solid run. Per project rules, we do **not** edit `v2` scripts.
All hardening changes land in this `v3` folder.

## What v3 hardens (no protocol drift)

Same intended theorem of the synthetic task:

- base-only: not closed
- any single query: not closed
- querying both useful bit views: closed

v3 hardens *implementation details* to remove avoidable loopholes / degeneracies:

1) **No base-label collisions**

- Enforce `n_base := n_states / 8 <= obs_vocab`.
- If violated, the generator raises a clear error.

2) **Distractors are strictly varying inside each base bucket**

- Distractor parameters are sampled with `a1 != a0` per base bucket (resampling).
- This removes “locally constant distractor” buckets that can weaken the strong condition.

3) **Verifier checks protocol identity**

The strict verifier additionally checks:

- `kind`
- `profile`
- `n_views`, `q_steps`, `y_classes`, `obs_vocab`
- presence/uniqueness of `(n_states, seed)` keys (no duplicates)

## Status of the model claim

`aslmt_model_v18_algebra_multistep_64_strong_actionz_v3.py` still implements an **explicit algebraic planner**:
it computes (from `tables`, `σ`, and the transcript) an exact horizon-aware score, then learns only a small mapping
from these computed features to query logits.

So the current experimental status is best described as:

- **constructive demonstration**: an internal algebraic planner can causally drive a query loop via a discrete mediator `z`.

Upgrading this into a “learned discovery” claim requires replacing the exact planner features with a learned encoder,
then auditing that the same invariant structure emerges internally.

## Files

- `aslmt_env_v18_algebra_multistep_64_strong_v3.py`: strong episode generator + dataset (hardened)
- `aslmt_model_v18_algebra_multistep_64_strong_actionz_v3.py`: action-as-`z` model (same architecture contract)
- `aslmt_train_v18_algebra_multistep_64_strong_matrix_diagstop_actionz_v3.py`: trainer producing master JSONL rows
- `verify_aslmt_v18_algebra_multistep_64_strong_matrix_v3.py`: strict verifier for `solid` (hardened metadata checks)
- `aslmt_campaign_v18_algebra_multistep_64_strong_matrix_diagstop_actionz_v3.py`: snapshot + hash runner
- `audit_v18_algebra_multistep_64_strong_v3_algebra.py`: independent algebra audit (exact set laws on `ΔX`)

## Latest solid run (complete)

Run directory:

```text
/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v18_algebra_multistep_64_strong_actionz_v3_solid_20260429_064727_e18711f98bbc
```

Master JSONL (n=64, seeds 0..4):

```text
/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v18_algebra_multistep_64_strong_actionz_v3_solid_20260429_064727_e18711f98bbc/v18_algebra_multistep_64_strong_actionz_v3_solid_master_20260429_064727_e18711f98bbc.jsonl
```

Verifier command (solid, strict, min-seeds=5):

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt
snap_dir="/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/snapshots/aslmt_v18_algebra_multistep_64_strong_actionz_v3_solid_20260429_064727_e18711f98bbc"
run_dir="/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v18_algebra_multistep_64_strong_actionz_v3_solid_20260429_064727_e18711f98bbc"
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  "$snap_dir/verify_aslmt_v18_algebra_multistep_64_strong_matrix_v3.py" \
  --master-jsonl "$run_dir/v18_algebra_multistep_64_strong_actionz_v3_solid_master_20260429_064727_e18711f98bbc.jsonl" \
  --profile solid --min-seeds 5 --n-states-list 64
```

Observed metrics (min/max over 5 seeds):

IID:
- `A_acc`: 1.000 / 1.000
- `B_vis_acc`: 0.483398 / 0.523438
- `B_cue_acc`: 0.470703 / 0.507812
- `A_abl_acc`: 0.520508 / 0.559570
- `A_swap_acc`: 0.518555 / 0.556641
- `swap_action_follow_rate`: 1.000 / 1.000

OOD:
- `A_acc`: 1.000 / 1.000
- `B_vis_acc`: 0.482422 / 0.496094
- `B_cue_acc`: 0.503906 / 0.514648
- `A_abl_acc`: 0.513672 / 0.529297
- `A_swap_acc`: 0.513672 / 0.541992
- `swap_action_follow_rate`: 1.000 / 1.000
