# ASLMT v10 — Phase A1 matrix runner (k-det injected, spaced2 witness)

This is the same Phase A1 matrix protocol as `v10_phaseA1_kdet`, but with a theory-aligned structural tightening
discovered by the faildump:

- `z` is already correct in OOD (cue→z is not the bottleneck).
- remaining misses come from **geometric readout** under the image-barrier because competing targets overlap too much.

So this variant swaps the underlying witness renderer/env to a **spaced hidden-position map** (`stride=2`, fixed hidden thickness),
reducing target overlap and making strict pair-grade closure achievable under `solid`.

Underlying witness pieces (from `v9_unified`):

- `render_v9_unified_paired_ctx_nscalable_spaced2.py`
- `aslmt_env_v9_unified_double_barrier_minlift_nscalable_spaced2.py`
- `aslmt_model_v9_unified_double_barrier_minlift_kdet.py`
- `aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood_posloss_pairrank_nscalable_kdet_spaced2.py`

## Run (solid, CUDA)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u v10_phaseA1_kdet_spaced2/aslmt_campaign_v10_phaseA1_unified_nscalable_posloss_pairrank_kdet_spaced2.py \
  --profile solid \
  --device cuda \
  --seed-from 0 --seed-to 4 \
  --n-classes-list 3,4,5,6 \
  --steps 9000 \
  --w-z 5.0 --w-k 0.0 --w-pos 0.25 \
  --w-rank-img 0.25 --rank-n-ctx 8 --rank-ood-ratio 0.5
```

## Status (current run)

Current run directory:

- `Empirical/aslmt/runs/aslmt_v10_phaseA1_unified_nscalable_posloss_pairrank_kdet_spaced2_20260416_074821_9fcd16977fda/`
- master JSONL: `Empirical/aslmt/runs/aslmt_v10_phaseA1_unified_nscalable_posloss_pairrank_kdet_spaced2_20260416_074821_9fcd16977fda/v10_master_20260416_074821_9fcd16977fda.jsonl`

Observed so far (from the master JSONL, `profile=solid`, `seed=0..4`):

- Phase A1 is **closed** on `n ∈ {3,4,5,6}`:
  - for each `n`, the reference group `z=n` passes on all 5 seeds, in both IID and OOD, with strict barrier checks and strict causal gates;
  - under-capacity groups `z<n` fail on the image-barrier as expected (while keeping baselines at 0 and barrier checks valid).

### A1 summary (publishable spine)

Run: `aslmt_v10_phaseA1_unified_nscalable_posloss_pairrank_kdet_spaced2_20260416_074821_9fcd16977fda`.

Acceptance criteria for the reference group `z=n` (all must hold, IID and OOD, all seeds):

- `obs_image_barrier_ok = true` and `obs_cue_barrier_ok = true`
- `A_both_image_pair_rate = 1.0` and `A_both_cue_pair_rate = 1.0`
- baselines `B_image_only_both_rate = 0.0` and `B_cue_only_both_rate = 0.0`
- ablation `A_ablated_both_image_pair_rate = 0.0`
- swap gate `A_swap_follow_image_pair_rate = 1.0` and `A_swap_orig_both_image_pair_rate = 0.0`

Result: all criteria hold for `n=3,4,5,6` with `seed=0..4`. Under-capacity groups `z<n` fail on the image-barrier with the expected pattern `A_both_image_pair_rate < 1.0`, while the reference `z=n` stays perfect.

### A1 table (min over seeds, both splits)

All rows below are minima over `seed=0..4`. Values are reported for both IID and OOD.

| `n` | `z` | IID `A_img_min` | OOD `A_img_min` | IID `A_cue_min` | OOD `A_cue_min` | Expected |
|---:|---:|---:|---:|---:|---:|:--|
| 3 | 3 | 1.0000 | 1.0000 | 1.0000 | 1.0000 | PASS (`z=n`) |
| 3 | 2 | 0.6719 | 0.6719 | 1.0000 | 1.0000 | FAIL (`z<n`) |
| 4 | 4 | 1.0000 | 1.0000 | 1.0000 | 1.0000 | PASS (`z=n`) |
| 4 | 3 | 0.8281 | 0.7500 | 1.0000 | 1.0000 | FAIL (`z<n`) |
| 4 | 2 | 0.6719 | 0.6719 | 1.0000 | 1.0000 | FAIL (`z<n`) |
| 5 | 5 | 1.0000 | 1.0000 | 1.0000 | 1.0000 | PASS (`z=n`) |
| 5 | 4 | 0.8281 | 0.8906 | 1.0000 | 1.0000 | FAIL (`z<n`) |
| 5 | 2 | 0.5938 | 0.5625 | 1.0000 | 1.0000 | FAIL (`z<n`) |
| 6 | 6 | 1.0000 | 1.0000 | 1.0000 | 1.0000 | PASS (`z=n`) |
| 6 | 5 | 0.9062 | 0.9375 | 1.0000 | 1.0000 | FAIL (`z<n`) |
| 6 | 3 | 0.7812 | 0.7969 | 1.0000 | 0.9688 | FAIL (`z<n`) |

To re-run only the verifier on the current master JSONL:

```bash
python3 -u v10_phaseA1_kdet_spaced2/verify_aslmt_v10_phaseA1_matrix.py \
  --profile solid \
  --n-classes-list 3,4,5,6 \
  --master-jsonl Empirical/aslmt/runs/aslmt_v10_phaseA1_unified_nscalable_posloss_pairrank_kdet_spaced2_20260416_074821_9fcd16977fda/v10_master_20260416_074821_9fcd16977fda.jsonl
```
