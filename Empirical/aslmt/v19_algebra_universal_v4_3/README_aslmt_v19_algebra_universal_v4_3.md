# ASLMT v19 — Algebra Universal v4.3 (learned encoder policy, strict protocol)

v4.3 builds on v4.1 and applies a training-schedule fix without changing the intended protocol or audits.

- v3 fixed closure fragility when `n_base > obs_vocab` because `σ` depended on `base_raw` while the
  observable base label was `base_obs = base_lbl = base_raw mod obs_vocab`.
- v3 replaced tautological audit with strict protocol invariants and hardened the verifier.

New in v4:
- policy logits are produced by a learned encoder over raw inputs (no oracle calls, no ambiguity/count features).

New in v4.1:
- fixes a verifier robustness bug (invalid JSON lines are handled without crashing);
- aligns the README oracle description with the actual lexicographic oracle objective.

New in v4.3:
- teacher forcing is applied at the **trajectory** level (per example), instead of per step.

This folder is a new protocol variant (v4.3). It does **not** modify v1/v2/v3/v4.1 scripts or historical run snapshots.

## Solid (end-to-end)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
v19_algebra_universal_v4_3/aslmt_campaign_v19_algebra_universal_v4_3_matrix_diagstop_actionz.py \
  --profile solid --device cuda \
  --seed-from 0 --seed-to 4 \
  --n-states-list 64 \
  --steps 4000 --batch-size 64 --lr 3e-4 \
  --n-views 8 --y-classes 2 --obs-vocab 16 --max-steps 3 --tf-decay-frac 0.8
```

Universal `tail -f` for the latest run log:

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs
run_dir="$(ls -1dt aslmt_v19_algebra_universal_actionz_v4_3_solid_* | head -n 1)"
log_file="$(ls -1t "$run_dir"/train_*.txt | head -n 1)"
echo "$log_file"
tail -f "$log_file"
```

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

## Oracle (v4.3)

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
  v19_algebra_universal_v4_3/aslmt_campaign_v19_algebra_universal_v4_3_matrix_diagstop_actionz.py \
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
  "$snap_dir/verify_aslmt_v19_algebra_universal_v4_3_matrix.py" \
  --master-jsonl "$run_dir/<MASTER>.jsonl" \
  --profile smoke --min-seeds 1 --n-states-list 64 --max-steps 3
  ```

Independent algebra audit:

```bash
  /home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v19_algebra_universal_v4_3/audit_v19_algebra_universal_v4_3_algebra.py \
  --n-states 64 --n-views 8 --episodes 50 --obs-vocab 16 --max-steps 3
  ```

## Current status (2026-04-30)

As of 2026-04-30, the v4.3 `solid` runs below were **valid** (protocol/audit/verifier ran) but **fail** the `solid` threshold because `A_acc < 0.85` on `n_states=64` (seed 0). The campaign stops after seed 0 when partial verification fails.

| run tag suffix | seed | iid `A_acc` | ood `A_acc` | verifier |
| --- | ---: | ---: | ---: | --- |
| `20260430_120843_830b99d7790f` | 0 | 0.5342 | 0.5283 | FAIL (`A_acc`) |
| `20260430_121302_830b99d7790f` | 0 | 0.5342 | 0.5283 | FAIL (`A_acc`) |
| `20260430_121540_830b99d7790f` | 0 | 0.6602 | 0.6611 | FAIL (`A_acc`) |
