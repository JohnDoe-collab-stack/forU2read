# law_v3b_unified_v2_strong_qforced_zread_stability_n

Goal: close **v3b stability-in-n** for the `qforced_zread` protocol by running the same strict matrix in `solid`
across multiple `n` values (e.g. `n=12` then `n=16`) under the **same verifier**.

This folder is intentionally small: it only provides a campaign runner that snapshots the already-established
`qforced_zread` sources (model/env/render/train/verifier) and runs them as a reproducible matrix.

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

Output:
- `runs/aslmt_law_v3b_unified_v2_strong_qforced_zread_stability_n_*` (master jsonl + per-seed logs + final verify)
- `runs/snapshots/aslmt_law_v3b_unified_v2_strong_qforced_zread_stability_n_*` (snapshot bundle)

