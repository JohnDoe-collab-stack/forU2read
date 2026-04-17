# ASLMT v12 — Phase A2 clean 64×64 bundle (self-contained)

This folder is a **self-contained** Phase A2 runner: it does not import the older `v9_unified` files.
It is designed to anticipate the Phase A2 failure mode where only one barrier is explicitly strengthened.

Key design choice: training includes **both** symmetric pair-ranking objectives:

- image-barrier pair-rank (fixed `k`, varying `h`),
- cue-barrier pair-rank (fixed `h`, varying `k`),

in addition to:

- `z` supervision (`h mod z`),
- position loss (center of mass),
- strict barrier checks and strict verifiers.

## Run (solid, CUDA)

From `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt`:

```bash
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u v12_phaseA2_clean64/aslmt_campaign_v12_phaseA2_clean64.py \
  --profile solid \
  --device cuda \
  --seed-from 0 --seed-to 4 \
  --n-classes-list 8,12,16 \
  --steps 9000 \
  --batch-size 64 \
  --w-z 5.0 --w-pos 0.25 \
  --w-rank-img 0.25 --w-rank-cue 0.25 \
  --rank-n-ctx 8 --rank-ood-ratio 0.5
```

## Files (self-contained)

- `render_v12_clean64_paired_ctx.py`
- `aslmt_env_v12_clean64.py`
- `aslmt_model_v12_clean64_kdet.py`
- `aslmt_train_v12_clean64.py`
- `verify_aslmt_v12_phaseA2_clean64_matrix.py`
- `aslmt_campaign_v12_phaseA2_clean64.py`

