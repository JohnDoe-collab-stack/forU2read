# ASLMT v13, Phase A2 (k-det, spaced2_64) with diagnostics and seg calibration

This version is a strict, traceable successor intended to address the remaining A2 failure mode observed in v12:

- barriers are valid and causal gates are mostly correct,
- but a strict `solid` run can miss 1 context out of 64 in the reference block (`63/64`),
- the corresponding `A_iou` can be near zero because BCE on sparse masks admits near empty predictions.

v13 adds two things, without changing the verifier contract:

1. A segmentation calibration loss (positive weighting and Dice) to prevent the near empty mask mode.
2. A mandatory diagnostic path: checkpoint saving and fail dumps for any strict gate miss.

## Run (solid, CUDA)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u v13_phaseA2_kdet_spaced2_64_imgcuerank_poswtdice_diag/aslmt_campaign_v13_phaseA2_unified_nscalable_poswtdice_pairrank_imgcuerank_kdet_spaced2_64_diagstop.py \
  --profile solid \
  --device cuda \
  --seed-from 0 --seed-to 4 \
  --n-classes-list 8,12,16 \
  --steps 9000 \
  --w-z 5.0 --w-k 0.0 \
  --w-pos 0.25 \
  --w-rank-img 0.25 --w-rank-cue 0.25 \
  --rank-n-ctx 8 --rank-ood-ratio 0.5 \
  --w-dice 0.25 --w-bce 1.0 --bce-pos-weight batch
```

Notes:

- This campaign stops early on any strict reference failure (irreversible min or max under `solid`).
- For any strict gate miss, it writes a fail dump JSONL and a model checkpoint into the run directory.

