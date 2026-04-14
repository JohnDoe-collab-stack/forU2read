# ASLMT vN3b: Min-Lift Double-Barrier (Pair-Grade, OOD-Required)

vN3b is a standalone refinement of vN3 aimed at making the mediator channel `cue -> z` *reliably* learnable.

Key change vs vN3:

- Replace the learned attention-based marker extractor with a **deterministic 2x2-density argmax**:
  find the 2x2 patch with maximal sum in the cue channel (robust to sparse flip noise), then read out
  the `(x,y)` coordinates from the coordinate channels and pass them through a small MLP to obtain `z_logits`.

Additionally, vN3b writes a `z_acc` audit (IID/OOD) into the JSONL row.

## Smoke (cuda)

```bash
cd /mnt/c/Users/frederick/Documents/Compatibility_Obstructions_in_Fibered_Relational_Systems/Python/private/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u vN3b_descriptive/aslmt_campaign_vN3b_minlift_double_barrier_pair_oodrequired.py \
  --profile smoke --seed 0 --n-classes 4 --z-classes-list 3,4 --device cuda
```

## Solid (cuda)

```bash
cd /mnt/c/Users/frederick/Documents/Compatibility_Obstructions_in_Fibered_Relational_Systems/Python/private/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u vN3b_descriptive/aslmt_campaign_vN3b_minlift_double_barrier_pair_oodrequired.py \
  --profile solid \
  --seed-from 0 --seed-to 4 \
  --n-classes 4 \
  --z-classes-list 3,4 \
  --device cuda
```

## Reference run ([OK], solid, causal-gated minlift at n=4)

Run directory:

- `runs/aslmt_vN3b_minlift_20260414_210841_ec5fdeec7e43`

Re-verify from the frozen snapshot:

```bash
cd /mnt/c/Users/frederick/Documents/Compatibility_Obstructions_in_Fibered_Relational_Systems/Python/private/aslmt
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  runs/snapshots/aslmt_vN3b_minlift_20260414_210841_ec5fdeec7e43/verify_aslmt_vN3b_minlift_double_barrier_pair_oodrequired.py \
  --master-jsonl runs/aslmt_vN3b_minlift_20260414_210841_ec5fdeec7e43/vN3b_master_20260414_210841_ec5fdeec7e43.jsonl \
  --n-classes 4 \
  --profile solid
```

Verifier summary (expected):

- `z=4` closes IID and OOD with ablation and swap gates (all 1.0 / 0.0 as appropriate).
- `z=3` fails the image-barrier (min < 1.0 on IID and OOD).
