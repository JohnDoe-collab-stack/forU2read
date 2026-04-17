# ASLMT v11 — Phase A2 matrix runner (k-det injected, spaced2, 64x64 witness)

This folder is the **Phase A2** continuation of the universality plan:

- Phase A1 closed the unified witness contract on `n ∈ {3,4,5,6}` (strict `solid`, IID ∪ OOD, seeds `0..4`).
- Phase A2 pushes the same contract to larger `n` (e.g. `n ∈ {8,12,16}`).

To reach `n=16` while keeping the witness **structurally valid** (no collisions, barrier checks true),
this v11 runner switches the underlying witness to a **64×64** spaced2 variant.

Underlying witness pieces (from `v9_unified`):

- `render_v9_unified_paired_ctx_nscalable_spaced2_64.py`
- `aslmt_env_v9_unified_double_barrier_minlift_nscalable_spaced2_64.py`
- `aslmt_model_v9_unified_double_barrier_minlift_kdet.py`
- `aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood_posloss_pairrank_nscalable_kdet_spaced2_64.py`

## Run (solid, CUDA)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u v11_phaseA2_kdet_spaced2_64/aslmt_campaign_v11_phaseA2_unified_nscalable_posloss_pairrank_kdet_spaced2_64.py \
  --profile solid \
  --device cuda \
  --seed-from 0 --seed-to 4 \
  --n-classes-list 8,12,16 \
  --steps 9000 \
  --batch-size 64 \
  --w-z 5.0 --w-k 0.0 --w-pos 0.25 \
  --w-rank-img 0.25 --rank-n-ctx 8 --rank-ood-ratio 0.5
```

## Smoke (fast barrier validity check)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u v11_phaseA2_kdet_spaced2_64/aslmt_campaign_v11_phaseA2_unified_nscalable_posloss_pairrank_kdet_spaced2_64.py \
  --profile smoke \
  --device cuda \
  --seed-from 0 --seed-to 0 \
  --n-classes-list 8,12,16 \
  --steps 300 \
  --batch-size 64 \
  --w-z 5.0 --w-k 0.0 --w-pos 0.25 \
  --w-rank-img 0.25 --rank-n-ctx 2 --rank-ood-ratio 0.5
```

## Expected verifier reading (solid)

Same strict contract as Phase A1:

- Reference group `z=n`: barrier checks hold (image + cue), `A_*_min=1.0` on IID and OOD, baselines `B_*_max=0.0`,
  causal gates pass (ablation breaks; swap follows).
- Any `z<n`: cannot close the image-barrier pair rate to `1.0` on IID and OOD.

