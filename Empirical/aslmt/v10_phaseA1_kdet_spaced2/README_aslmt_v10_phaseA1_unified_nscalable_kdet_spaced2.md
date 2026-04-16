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

