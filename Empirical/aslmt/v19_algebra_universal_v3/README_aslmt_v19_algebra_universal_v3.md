# ASLMT v19 — Algebra Universal v3 (strict barrier, strict audit/verify, learned policy)

v3 fixes the core v2 issues:

- v2 had a closure fragility when `n_base > obs_vocab` because `σ` depended on `base_raw` while the
  observable base label was `base_obs = base_lbl = base_raw mod obs_vocab`.
- v2's independent audit checked a tautological meet identity instead of protocol invariants.
- v2's verifier tolerated corrupted / incomplete master JSONL rows.
- v2's model embedded the oracle in the policy computation; v3 removes the oracle from the policy.

This folder is a new protocol variant (v3). It does **not** modify v1/v2 scripts or historical run snapshots.

## Protocol (unchanged at high level)

Episode provides:

- `tables`: (V,N) views on finite latent space `X={0..N-1}`
- `sigma`: (N,) target signature
- `x`: hidden latent index
- `base_obs`: `tables[0, x]`
- `max_steps`: query budget
- `stop_action`: distinguished action id (=V)

Policy loop:

- choose `a ∈ {1..V-1}` to query, observe `r=tables[a,x]`,
- or choose `STOP=V` to stop; the decision is computed from transcript.

## Oracle (v3)

Let `τ_t` be the transcript prefix (base observation + queried view/response pairs),
and let `F_{τ_t}` be the candidate set consistent with `τ_t`.

Define the horizon value function (expected final ambiguity):

```text
V_0(τ) := Amb_σ(F_τ)              # number of σ-values on the candidate set

Q_h(a | τ) :=
  E_{r ~ O_a | F_τ} [ V_{h-1}( τ ∪ {(a,r)} ) ]

V_h(τ) := min_a Q_h(a | τ)
```

The oracle action set at time `t` is:

```text
Opt_h(τ_t) := argmin_a Q_h(a | τ_t)   where h := (max_steps - t)
```

STOP is allowed iff `Amb_σ(F_{τ_t}) == 1` (closure already holds).

## Smoke (end-to-end)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  v19_algebra_universal_v3/aslmt_campaign_v19_algebra_universal_v3_matrix_diagstop_actionz.py \
  --profile smoke --device cpu \
  --seed-from 0 --seed-to 0 \
  --n-states-list 64 \
  --n-views 8 --y-classes 2 --obs-vocab 16 --max-steps 3
```

Verifier:

```bash
run_dir="/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/<RUN_TAG>"
snap_dir="/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/snapshots/<RUN_TAG>"
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  "$snap_dir/verify_aslmt_v19_algebra_universal_v3_matrix.py" \
  --master-jsonl "$run_dir/<MASTER>.jsonl" \
  --profile smoke --min-seeds 1 --n-states-list 64 --max-steps 3
```

Independent algebra audit:

```bash
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v19_algebra_universal_v3/audit_v19_algebra_universal_v3_algebra.py \
  --n-states 64 --n-views 8 --episodes 50 --obs-vocab 16 --max-steps 3
```
