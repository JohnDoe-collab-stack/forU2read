# ASLMT v14, Phase A2 (k-det, spaced2_64) with contract-aligned ranking

This version is a strict, traceable successor intended to address the remaining A2 failure mode observed in v12:

- barriers are valid and causal gates are mostly correct,
- but a strict `solid` run can miss 1 context out of 64 in the reference block (`63/64`),
- the corresponding `A_iou` can be near zero because BCE on sparse masks admits near empty predictions.

v14 adds a contract-aligned ranking loss, without changing the verifier contract:

1. A segmentation calibration loss (positive weighting and Dice) to prevent the near empty mask mode.
2. A contract-aligned ranking loss that matches the verifier pairing logic and cycles deterministically through the 64 strict contexts.
3. A mandatory diagnostic path: checkpoint saving and fail dumps for any strict gate miss.

## Run (solid, CUDA)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u v14_phaseA2_kdet_spaced2_64_contractrank_poswtdice_diag/aslmt_campaign_v14_phaseA2_unified_nscalable_poswtdice_contractrank_imgcuerank_kdet_spaced2_64_diagstop.py \
  --profile solid \
  --device cuda \
  --seed-from 0 --seed-to 4 \
  --n-classes-list 8,12,16 \
  --steps 9000 \
  --w-z 5.0 --w-k 0.0 \
  --w-pos 0.25 \
  --w-rank-img 0.25 --w-rank-cue 0.25 \
  --rank-n-ctx 8 --rank-margin 1.0 \
  --w-dice 0.25 --w-bce 1.0 --bce-pos-weight batch
```

Notes:

- This campaign stops early on any strict reference failure (irreversible min or max under `solid`).
- For any strict gate miss, it writes a fail dump JSONL and a model checkpoint into the run directory.
- Under `solid`, `rank_n_ctx` must divide 64 (for example 1,2,4,8,16,32,64).
