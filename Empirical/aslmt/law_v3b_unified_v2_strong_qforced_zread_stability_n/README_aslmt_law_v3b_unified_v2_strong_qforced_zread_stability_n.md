# law_v3b_unified_v2_strong_qforced_zread_stability_n

Goal: close **v3b stability-in-n** for the `qforced_zread` protocol by running the same strict matrix in `solid`
across multiple `n` values (e.g. `n=12` then `n=16`) under the **same verifier**.

This folder is intentionally small: it only provides a campaign runner that snapshots the already-established
`qforced_zread` sources (model/env/render/train/verifier) and runs them as a reproducible matrix.

Prerequisite (already closed):

- `n=8` reference matrix run (strict verifier PASS):  
  `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_law_v3b_unified_v2_strong_qforced_zread_solid_20260423_102039_9f958bfafaad/`

## Run (solid)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  law_v3b_unified_v2_strong_qforced_zread_stability_n/aslmt_campaign_law_v3b_unified_v2_strong_qforced_zread_stability_n_matrix_diagstop_v1.py \
  --profile solid \
  --device cuda \
  --seed-from 0 --seed-to 4 \
  --n-classes-list 12,16 \
  --steps 9000
```

## Run (solid, poswtdice-stable variant)

The strict matrix verifier for `qforced_zread` uses exact equality on the reference pair-gates
(`A_both_image_pair_rate == 1.0` and `A_swap_follow_image_pair_rate == 1.0`) on `pair_n_ctx=64`.
This makes the reference block sensitive to rare "few-ctx" misses on a particular seed at larger `n`
(e.g. a `61/64 = 0.953125` event).

This does **not** change the protocol or the verifier; it only changes the training loss defaults to
stabilize the final `A` readout:

- `--w-dice 0.25`
- `--bce-pos-weight batch`

Campaign runner:

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  law_v3b_unified_v2_strong_qforced_zread_stability_n/aslmt_campaign_law_v3b_unified_v2_strong_qforced_zread_stability_n_matrix_diagstop_v2_poswtdice.py \
  --profile solid \
  --device cuda \
  --seed-from 0 --seed-to 4 \
  --n-classes-list 12,16 \
  --steps 9000
```

Reference run (n=12 block, strict ref-gates satisfied on all seeds 0..4):

- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_law_v3b_unified_v2_strong_qforced_zread_stability_n_solid_20260424_213134_9f958bfafaad/`

Final verification (strict, all 5 seeds):

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

run_dir="runs/aslmt_law_v3b_unified_v2_strong_qforced_zread_stability_n_solid_20260424_213134_9f958bfafaad"
snap_dir="runs/snapshots/aslmt_law_v3b_unified_v2_strong_qforced_zread_stability_n_solid_20260424_213134_9f958bfafaad"

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  "$snap_dir/verify_aslmt_law_v3b_unified_v2_strong_qforced_matrix.py" \
  --master-jsonl "$run_dir/law_v3b_unified_v2_strong_qforced_zread_stability_n_solid_master_20260424_213134_9f958bfafaad.jsonl" \
  --profile solid \
  --min-seeds 5 \
  --n-classes-list 12 \
  --z-policy explicit \
  --z-classes-list 12
```

Output:
- `runs/aslmt_law_v3b_unified_v2_strong_qforced_zread_stability_n_*` (master jsonl + per-seed logs + final verify)
- `runs/snapshots/aslmt_law_v3b_unified_v2_strong_qforced_zread_stability_n_*` (snapshot bundle)
