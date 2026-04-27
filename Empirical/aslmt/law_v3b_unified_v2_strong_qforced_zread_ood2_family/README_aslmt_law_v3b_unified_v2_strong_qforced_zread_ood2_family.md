# law_v3b_unified_v2_strong_qforced_zread_ood2_family

Goal: add an **additional OOD family** (`ood2`) to the strict `qforced_zread` protocol, as an **orthogonal axis**
to stability-in-`n`.

This folder is self-contained:
- it carries local copies of the `qforced_zread` model/env/render/train logic,
- extends the renderer with `Ctx.ood2` (extra **image** noise that does not depend on `h` or `k`, preserving the image barrier),
- and extends the strict verifier to check **IID + OOD + OOD2**.

Reference closure already achieved (baseline protocol, no OOD2):
- `Empirical/aslmt/runs/aslmt_law_v3b_unified_v2_strong_qforced_zread_solid_20260423_102039_9f958bfafaad/`

## Run (solid)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  law_v3b_unified_v2_strong_qforced_zread_ood2_family/aslmt_campaign_law_v3b_unified_v2_strong_qforced_zread_ood2_matrix_diagstop_v1.py \
  --profile solid \
  --device cuda \
  --seed-from 0 --seed-to 4 \
  --n-classes-list 8 \
  --steps 9000
```

Notes:
- `ood2` is **evaluation-only** by default (`--train-ood2-ratio 0.0` in the trainer).
- The strict verifier checks all three splits (`iid`, `ood`, `ood2`) on the reference group `z=n`.

## Closure achieved (solid)

Reference run:
- `Empirical/aslmt/runs/aslmt_law_v3b_unified_v2_strong_qforced_zread_ood2_solid_20260426_134944_fd96063506f9/`

Verifier output:
- `Empirical/aslmt/runs/aslmt_law_v3b_unified_v2_strong_qforced_zread_ood2_solid_20260426_134944_fd96063506f9/verify_20260426_134944_fd96063506f9.txt` (`[OK]`)
