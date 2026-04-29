# ASLMT v19 — Algebra Universal v1 (stop-on-closure, multi-family)

Goal: build a **universal** (testable) closure protocol that removes fixed-step assumptions:

- the solver runs a query loop until **closure is reached**, or until a max budget,
- the generator samples **multiple task families** (different closure structures),
- the verifier remains **strict** (barriers + baselines + ablation/swap + IID/OOD + multi-seeds).

This is a new protocol family (v19) and does not modify historical scripts/runs.

## Universal meaning (operational)

“Universal” here means:

- for a wide class of finite instances encoded as `(tables, σ, base_obs, responses)`,
- if the target is **not closed** on the base view but becomes **closable** after composing allowed views,
- then a solver can learn a policy that drives the residual to 0 and stops.

## Protocol sketch (v1)

Episode provides:

- `tables`: (V,N) view tables on a finite latent space `X={0..N-1}`
- `sigma`: (N,) target signature
- `x`: hidden latent index
- `base_obs`: `tables[base_view, x]`
- `max_steps`: query budget (variable)
- `stop_action`: a distinguished action meaning “stop now”

At each step, the policy chooses:

- either a view index `a ∈ {0..V-1}` to query, receiving `r = tables[a, x]`,
- or `stop_action` to stop; decision is then produced from transcript.

The generator labels:

- `opt_actions`: an oracle policy sequence that closes as fast as possible
- `opt_stop_t`: earliest t where closure holds (so stopping is correct)

## Status

This folder is a scaffold. It defines the target protocol and strict verifier shape.
Implementation lives in the accompanying `aslmt_env_*`, `aslmt_model_*`, `aslmt_train_*`, `verify_*`, `campaign_*`.

## Validity constraints (v1)

To guarantee the **base barrier** (base-only is never closed), v1 enforces an internal factorization:

```text
X ≅ Base × {0,1}^M × {0,1} ,  where M := max_steps
```

Therefore the generator requires:

```text
n_states divisible by 2^(max_steps+1)
```

If the constraint is violated, the episode generator raises an error.

## Smoke (end-to-end)

Example smoke (CPU, 1 seed):

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  v19_algebra_universal_v1/aslmt_campaign_v19_algebra_universal_matrix_diagstop_actionz.py \
  --profile smoke --device cpu \
  --seed-from 0 --seed-to 0 \
  --n-states-list 32 \
  --n-views 8 --y-classes 2 --obs-vocab 16 --max-steps 3
```

Example smoke verifier:

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt
run_dir="/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/<RUN_TAG>"
snap_dir="/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/snapshots/<RUN_TAG>"
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  "$snap_dir/verify_aslmt_v19_algebra_universal_matrix.py" \
  --master-jsonl "$run_dir/<MASTER>.jsonl" \
  --profile smoke --min-seeds 1 --n-states-list 32 --max-steps 3
```

Independent algebra audit:

```bash
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v19_algebra_universal_v1/audit_v19_algebra_universal_algebra.py \
  --n-states 32 --n-views 8 --episodes 50 --obs-vocab 16 --max-steps 3
```
