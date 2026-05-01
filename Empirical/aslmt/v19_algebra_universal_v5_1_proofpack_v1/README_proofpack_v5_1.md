# v19 universal v5.1 — Proof Pack v1 (train → checkpoint → structural certificates)

Goal: make the **final** certificate-based claim executable end-to-end:

1) train a model,
2) export an immutable `modelA_state_dict.pt`,
3) run the **structural certificate verifier** on frozen IID+OOD benchmarks with:
   - response fidelity (P1bis),
   - closure at STOP (P2),
   - unique-branch readout (P3),
   - plus P1/P4/P5.

This is **not** a score-threshold demo. Success means: **zero counterexamples**.

Files:

- `aslmt_train_v19_algebra_universal_v5_1_matrix_diagstop_actionz.py`:
  identical to v5.1 training logic, plus `--save-modelA-state-dict` at the end.
- `certify_struct_aslmt_v19_algebra_universal_v5_1.py`:
  certificate generator (policy=`model` uses a saved checkpoint).
- `verify_struct_aslmt_v19_algebra_universal_v5_1.py`:
  structural verifier with exhaustive counterexample export.
- `aslmt_campaign_v19_algebra_universal_v5_1_proofpack.py`:
  snapshots the pack (timestamp+hash), runs train, then runs certify+verify on IID and OOD.

Run:

```bash
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \\
  /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v19_algebra_universal_v5_1_proofpack_v1/aslmt_campaign_v19_algebra_universal_v5_1_proofpack.py \\
  --python /home/frederick/.venvs/cofrs-gpu/bin/python3 \\
  --device cuda \\
  --profile solid \\
  --seed-from 0 --seed-to 4 \\
  --n-states-list 64 \\
  --episodes 1024 --seed-base 0
```

