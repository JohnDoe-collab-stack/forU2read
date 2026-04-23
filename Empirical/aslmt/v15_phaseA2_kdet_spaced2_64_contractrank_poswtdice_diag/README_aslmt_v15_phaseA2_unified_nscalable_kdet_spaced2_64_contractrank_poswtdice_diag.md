# ASLMT v15, Phase A2 (k-det, spaced2_64) with contract-aligned ranking and contract-preserving OOD cue corruption

This version is a strict, traceable successor intended to address the remaining A2 failure mode observed in v14:

- barriers are valid and causal gates are mostly correct,
- but a strict `solid` run can miss 1 context out of 64 in the reference block (`63/64`),
- the corresponding `A_iou` can be near zero because BCE on sparse masks admits near empty predictions.

v15 keeps the same verifier contract and the same contract-aligned ranking loss, and fixes the remaining failure mode at the witness level:

- in v14, OOD cue corruption could destroy the 2x2 cue marker that encodes `h`, making the task structurally impossible on a strict "1.0 everywhere" reference,
- v15 implements contract-preserving OOD cue corruption: the marker is never flipped, and the flip process is non-adjacent so it cannot create a competing 2x2 marker.

This is a witness fix (task validity), not an optimizer trick and not a verifier relaxation.

1. A segmentation calibration loss (positive weighting and Dice) to prevent the near empty mask mode.
2. A contract-aligned ranking loss that matches the verifier pairing logic and cycles deterministically through the 64 strict contexts.
3. A mandatory diagnostic path: checkpoint saving and fail dumps for any strict gate miss.

## Run (solid, CUDA)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u v15_phaseA2_kdet_spaced2_64_contractrank_poswtdice_diag/aslmt_campaign_v15_phaseA2_unified_nscalable_poswtdice_contractrank_imgcuerank_kdet_spaced2_64_diagstop.py \
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

## Reference run (verified)

Run directory:

- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v15_phaseA2_unified_nscalable_poswtdice_contractrank_imgcuerank_kdet_spaced2_64_20260420_082149_5c9bb19a82ab`

Verifier output:

- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v15_phaseA2_unified_nscalable_poswtdice_contractrank_imgcuerank_kdet_spaced2_64_20260420_082149_5c9bb19a82ab/verify_20260420_082149_5c9bb19a82ab.txt`

Re-run the verifier on that run:

```bash
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/snapshots/aslmt_v15_phaseA2_unified_nscalable_poswtdice_contractrank_imgcuerank_kdet_spaced2_64_20260420_082149_5c9bb19a82ab/verify_aslmt_v15_phaseA2_matrix.py \
  --master-jsonl /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v15_phaseA2_unified_nscalable_poswtdice_contractrank_imgcuerank_kdet_spaced2_64_20260420_082149_5c9bb19a82ab/v15_master_20260420_082149_5c9bb19a82ab.jsonl \
  --profile solid \
  --min-seeds 3 \
  --n-classes-list 8,12,16 \
  --z-policy A1
```
