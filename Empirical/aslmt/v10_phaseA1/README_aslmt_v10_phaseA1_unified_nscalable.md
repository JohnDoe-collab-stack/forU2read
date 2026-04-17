# ASLMT v10 — Phase A1 matrix runner (n-scalable unified witness)

This folder implements **Phase A1** of `Empirical/aslmt/UNIVERSALITY_PLAN.md`:

- test `n ∈ {3,4,5,6}` (configurable),
- for each `n`, test `z ∈ {n, n-1, ⌊n/2⌋}` (configurable),
- multi-seeds,
- **strict verifier** on **IID ∪ OOD**,
- with **barrier lock** and **anti-collisions** enforced by the **n-scalable v9 renderer**.

Important: this is a **campaign+verifier layer**. The underlying witness is the `v9_unified` **n-scalable** variant:

- `v9_unified/render_v9_unified_paired_ctx_nscalable.py`
- `v9_unified/aslmt_env_v9_unified_double_barrier_minlift_nscalable.py`
- `v9_unified/aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood_posloss_pairrank_nscalable.py`

## Run (smoke, CPU)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

python3 -u v10_phaseA1/aslmt_campaign_v10_phaseA1_unified_nscalable_posloss_pairrank.py \
  --profile smoke \
  --device cpu \
  --seed-from 0 --seed-to 0 \
  --n-classes-list 3,4 \
  --steps 200
```

## Run (solid, CUDA)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u v10_phaseA1/aslmt_campaign_v10_phaseA1_unified_nscalable_posloss_pairrank.py \
  --profile solid \
  --device cuda \
  --seed-from 0 --seed-to 4 \
  --n-classes-list 3,4,5,6 \
  --steps 9000 \
  --w-z 5.0 --w-k 1.0 --w-pos 0.25 \
  --w-rank-img 0.25 --rank-n-ctx 8 --rank-ood-ratio 0.5
```

## Expected output

The campaign writes a single matrix master JSONL and a single strict verifier output in:

`Empirical/aslmt/runs/aslmt_v10_phaseA1_unified_nscalable_posloss_pairrank_<timestamp>_<bundlehash>/`

## Status / recommended driver

Phase A1 is now closed (strict `solid`, IID ∪ OOD, `seed=0..4`) on `n ∈ {3,4,5,6}` using the **k-det + spaced2**
variant of the witness and campaign:

- `Empirical/aslmt/v10_phaseA1_kdet_spaced2/README_aslmt_v10_phaseA1_unified_nscalable_kdet_spaced2.md`

If you are writing a “solid” claim or comparing to later phases (B/C/D), prefer that driver as the reference A1 closure.
