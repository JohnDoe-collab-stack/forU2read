# ASLMT v17 — Phase B family (symbolic orbit, 64x64)

This folder prepares **Phase B** by defining a second task family that is structurally different from the occluder witness.

Spine preserved (same strict contract as Phase A runs):

- double barrier (`obs_image_barrier_ok`, `obs_cue_barrier_ok`)
- min-lift via matrix `z ∈ {n, n-1, ⌊n/2⌋}`
- causal gates (ablation + swap-follow) under `profile=solid`
- IID and OOD, multi-seeds, strict verifier

Family difference:

- No occluder.
- The dynamic truth is a **symbolic orbit mask** (affine point orbit) of length `ctx.horizon`.
- `h` is visible only in `cue_image` (start marker).
- `k` is visible only in `image` (present stripe).

OOD changes the horizon distribution and increases background dot noise that does not encode `h`.

## Preflight: render barrier check

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v17_phaseB_symbolic_orbit_64
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u render_v17_symbolic_orbit_paired_ctx_64.py --n-classes 8 --horizon 10
```

## Run (Phase B closure attempt, solid, CUDA)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u v17_phaseB_symbolic_orbit_64/aslmt_campaign_v17_symbolic_orbit_matrix_diagstop.py \
  --profile solid \
  --device cuda \
  --seed-from 0 --seed-to 4 \
  --n-classes-list 3,4,5,6 \
  --steps 9000 \
  --w-z 5.0 --w-k 0.0 \
  --w-pos 0.25 \
  --w-rank-img 0.25 --w-rank-cue 0.25 \
  --rank-n-ctx 8 --rank-margin 1.0 \
  --rank-ood-ratio 0.5 --train-ood-ratio 0.5 \
  --pair-n-ctx 64 --img-size 64 \
  --w-dice 0.25 --w-bce 1.0 --bce-pos-weight batch
```

## Smoke (CPU, end-to-end wiring only)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u v17_phaseB_symbolic_orbit_64/aslmt_campaign_v17_symbolic_orbit_matrix_diagstop.py \
  --profile smoke \
  --device cpu \
  --seed-from 0 --seed-to 0 \
  --n-classes-list 4
```
