# ASLMT v19 — Algebra Universal v2 (horizon-consistent oracle, stop-on-closure)

v2 fixes the core v1 misalignment:

- v1 **trained** the query policy with a *myopic* (1-step) allowed-set oracle,
  while the protocol intent (and the non-trivial families) require a **horizon** oracle.
- v2 makes the oracle and the supervision **horizon-consistent** with the remaining query budget,
  so the model can learn the correct first action even when all 1-step scores tie.

This folder is a new protocol variant (v2). It does **not** modify v1 scripts or historical run snapshots.

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

## Oracle (v2)

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

### Oracle objective (precise, matches code)

The implementation optimizes a lexicographic triple:

```text
(expected_steps_to_closure,
 expected_final_ambiguity,
 expected_final_candidate_size)
```

So:

```text
Opt_h(τ) := argmin_a lex(
  E[steps_to_closure],
  E[final_ambiguity],
  E[final_candidate_size]
)
```

## Smoke (end-to-end)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  v19_algebra_universal_v2/aslmt_campaign_v19_algebra_universal_v2_matrix_diagstop_actionz.py \
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
  "$snap_dir/verify_aslmt_v19_algebra_universal_v2_matrix.py" \
  --master-jsonl "$run_dir/<MASTER>.jsonl" \
  --profile smoke --min-seeds 1 --n-states-list 64 --max-steps 3
```

Independent algebra audit:

```bash
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v19_algebra_universal_v2/audit_v19_algebra_universal_v2_algebra.py \
  --n-states 64 --n-views 8 --episodes 50 --obs-vocab 16 --max-steps 3
```

## Solid results (n=64, seeds 0..4, IID+OOD)

Run directory:

- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v19_algebra_universal_actionz_v2_solid_20260429_103226_a7792f68e826`

Master JSONL:

- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v19_algebra_universal_actionz_v2_solid_20260429_103226_a7792f68e826/v19_algebra_universal_actionz_v2_solid_master_20260429_103226_a7792f68e826.jsonl`

Aggregates (5 seeds):

```text
IID:
  A_acc  : min=1.0000 max=1.0000 mean=1.0000
  B_vis  : min=0.4775 max=0.5273 mean=0.4982
  B_cue  : min=0.5049 max=0.5518 mean=0.5256
  A_abl  : min=0.6631 max=0.6875 mean=0.6727
  A_swap : min=0.6660 max=0.6865 mean=0.6752
  follow : min=1.0000 max=1.0000 mean=1.0000

OOD:
  A_acc  : min=1.0000 max=1.0000 mean=1.0000
  B_vis  : min=0.4805 max=0.5400 mean=0.5068
  B_cue  : min=0.4961 max=0.5439 mean=0.5098
  A_abl  : min=0.6504 max=0.6748 mean=0.6617
  A_swap : min=0.6426 max=0.6631 mean=0.6539
  follow : min=1.0000 max=1.0000 mean=1.0000
```

Interpretation note:

- v2 is an **oracle-wrapper** baseline: policy logits are computed from oracle features, and `y`
  is predicted exactly from the candidate mask. So this run validates protocol/oracle closure,
  but does not yet force the “learned internal invariant” claim.
