# ASLMT v10 — Phase A1 matrix runner (n-scalable, k-det injected)

This is the same Phase A1 matrix idea as `v10_phaseA1`, but with a clean structural fix:

- `k` is **visible** in `image` and is extracted **deterministically**,
- the decoder is explicitly conditioned on `k_hat` (so segmentation cannot ignore `k`),
- `z` remains the finite mediator for the hidden class `h`.

This avoids the observed failure mode where `k_acc=1.0` (aux head) yet the segmentation output does not change with `k`,
causing cue-barrier failures on some seeds.

Underlying witness pieces (from `v9_unified`):

- `render_v9_unified_paired_ctx_nscalable.py`
- `aslmt_env_v9_unified_double_barrier_minlift_nscalable.py`
- `aslmt_model_v9_unified_double_barrier_minlift_kdet.py`
- `aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood_posloss_pairrank_nscalable_kdet.py`

## Run (solid, CUDA)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u v10_phaseA1_kdet/aslmt_campaign_v10_phaseA1_unified_nscalable_posloss_pairrank_kdet.py \
  --profile solid \
  --device cuda \
  --seed-from 0 --seed-to 4 \
  --n-classes-list 3,4,5,6 \
  --steps 9000 \
  --w-z 5.0 --w-k 0.0 --w-pos 0.25 \
  --w-rank-img 0.25 --rank-n-ctx 8 --rank-ood-ratio 0.5
```

