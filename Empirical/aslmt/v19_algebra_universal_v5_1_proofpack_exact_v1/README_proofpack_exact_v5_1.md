# v19 universal v5.1 — Proof Pack (Exact STOP + Exact Readout)

Goal: a certificate-based claim aligned with the **closure algebra**:

1) train a model,
2) export an immutable `modelA_state_dict.pt`,
3) certify and structurally verify IID+OOD episodes with **zero counterexamples**.

This pack implements **Option A**:

- the learned model is responsible for choosing **query actions** (which interfaces to probe),
- but **STOP** and the final **readout** are computed *exactly* from the transcript using:
  - `F_τ` (exact candidate set induced by `(base_obs, (a_t,r_t))`),
  - `Amb_σ(F_τ)` (exact ambiguity),
  - `σ*` (the unique value on `F_τ` when `Amb_σ(F_τ)=1`).

Therefore:

- the certifier **never emits STOP early** (STOP is emitted only after exact closure is detected),
- whenever closure is reached, P3 is satisfied by construction (`y_pred := σ*` on the closed candidate set),
- the remaining falsifiable content is: can the learned query policy reach closure within the budget.

Equivalently: any P2 counterexample is a “failed-to-close-within-budget” counterexample, not an early STOP bug.

Note: the intended protocol forbids the base view (`view0`) and forbids repeats; the campaign passes
`--forbid-view0 --forbid-repeats` consistently to both certifier and verifier.

Files:

- `aslmt_train_v19_algebra_universal_v5_1_matrix_diagstop_actionz.py`:
  identical to v5.1 training logic, plus `--save-modelA-state-dict`.
- `certify_struct_aslmt_v19_algebra_universal_v5_1_exact.py`:
  certificate generator with policy=`model_exact` (exact STOP + exact readout).
- `verify_struct_aslmt_v19_algebra_universal_v5_1.py`:
  structural verifier (P1/P1bis/P2/P3/P4/P5), exhaustive counterexample export.
- `aslmt_campaign_v19_algebra_universal_v5_1_proofpack_exact.py`:
  snapshots the pack (timestamp+hash), runs train, then runs certify+verify on IID and OOD.

Run (single seed, N=64):

```bash
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v19_algebra_universal_v5_1_proofpack_exact_v1/aslmt_campaign_v19_algebra_universal_v5_1_proofpack_exact.py \
  --python /home/frederick/.venvs/cofrs-gpu/bin/python3 \
  --device cuda \
  --profile solid \
  --seed-from 0 --seed-to 0 \
  --n-states-list 64 \
  --episodes 1024 --seed-base 0
```
