# ASLMT v12 — Phase A2 matrix runner (k-det injected, spaced2, 64x64 witness, image+cue pair-rank)

This folder is a minimal Phase A2 corrective variant that keeps the same unified witness contract as v11,
but strengthens training by adding a **cue-barrier symmetric pair-rank loss**.

Motivation: in v11 A2, `k` is extracted deterministically and injected into the decoder, yet the strict
cue-barrier gate can remain imperfect under the broader 64×64 context distribution. This variant adds a
pair-ranking objective directly on cue-barrier pairs (fixed cue, varying `k` in the image).

## Run (solid, CUDA)

From `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt`:

```bash
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u v12_phaseA2_kdet_spaced2_64_imgcuerank/aslmt_campaign_v12_phaseA2_unified_nscalable_posloss_pairrank_imgcuerank_kdet_spaced2_64.py \
  --profile solid \
  --device cuda \
  --seed-from 0 --seed-to 4 \
  --n-classes-list 8,12,16 \
  --steps 9000 \
  --batch-size 64 \
  --w-z 5.0 --w-k 0.0 --w-pos 0.25 \
  --w-rank-img 0.25 --w-rank-cue 0.25 \
  --rank-n-ctx 8 --rank-ood-ratio 0.5
```

## Files snapshotted by the campaign

- `Empirical/aslmt/v9_unified/aslmt_model_v9_unified_double_barrier_minlift_kdet.py`
- `Empirical/aslmt/v9_unified/aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood_posloss_pairrank_imgcuerank_nscalable_kdet_spaced2_64.py`
- `Empirical/aslmt/v9_unified/aslmt_env_v9_unified_double_barrier_minlift_nscalable_spaced2_64.py`
- `Empirical/aslmt/v9_unified/render_v9_unified_paired_ctx_nscalable_spaced2_64.py`
- `Empirical/aslmt/v12_phaseA2_kdet_spaced2_64_imgcuerank/verify_aslmt_v12_phaseA2_matrix.py`

## Expected verifier reading (solid)

Same strict expectations as v11 Phase A2:

- Reference group (`z=n`) must satisfy strict gates with **min over seeds** equalities on IID and OOD.
- Under-capacity groups (`z<n`) must fail to close the image barrier at least once (min < 1.0).

