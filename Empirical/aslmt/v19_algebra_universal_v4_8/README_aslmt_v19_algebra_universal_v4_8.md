# ASLMT v19 — Algebra Universal v4.8 (learned encoder policy, strict protocol)

v4.8 builds on v4.6/v4.7 and adds a **closed-only** readout loss on autonomous rollouts.

- v3 fixed closure fragility when `n_base > obs_vocab` because `σ` depended on `base_raw` while the
  observable base label was `base_obs = base_lbl = base_raw mod obs_vocab`.
- v3 replaced tautological audit with strict protocol invariants and hardened the verifier.
- v4 removed oracle-derived policy features: policy logits are produced by a learned encoder over raw inputs
  (no oracle calls, no ambiguity/count features).
- v4.3 applied teacher forcing at the **trajectory** level (per example), instead of per step.

New in v4.4:
- add `y_loss_roll`: a y-loss on **autonomous rollouts** (same distribution as evaluation);
- extend defaults to `--steps 6000` and `--tf-decay-frac 0.65` (longer autonomous phase);
- print rollout closure diagnostics in training logs;
- campaign writes **timestamps on every log line** (stdout+stderr).

New in v4.5:
- add a candidate-consistency loss on autonomous rollouts:
  `candidate_nll = -log(Σ_{s∈F_τ} b(s))` where `b(s)` is the model belief and `F_τ` is the exact candidate set.
- log internalization metrics:
  `belief_mass_on_candidate`, `belief_mass_on_candidate_given_closed`, `A_acc_given_closed`.

New in v4.6:
- save rollout closure + internalization diagnostics into `metrics` in the master JSONL (IID and OOD splits):
  `closed_rate_roll`, `final_ambiguity_mean`, `stop_rate`, `stop_when_closed_rate`, `mean_stop_t`,
  `belief_mass_on_candidate`, `belief_mass_on_candidate_given_closed`, `A_acc_given_closed`.

New in v4.7:
- change defaults to run with `--w-cand 1.0` (stronger belief→candidate consistency).

New in v4.8:
- add `y_loss_closed` on autonomous rollouts, **only** on objectively closed transcripts
  (`Amb_σ(F_τ) == 1` under the oracle candidate semantics);
- introduce `--w-y-closed` (default `2.0`);
- set `--w-cand` default to `0.0` (candidate-consistency is optional again).

This folder is a new protocol variant (v4.8). It does **not** modify v1/v2/v3/v4.1/v4.3/v4.4/v4.5/v4.6/v4.7 scripts or historical run snapshots.

## Solid (end-to-end)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
v19_algebra_universal_v4_8/aslmt_campaign_v19_algebra_universal_v4_8_matrix_diagstop_actionz.py \
  --profile solid --device cuda \
  --seed-from 0 --seed-to 4 \
  --n-states-list 64 \
  --steps 6000 --batch-size 64 --lr 3e-4 \
  --n-views 8 --y-classes 2 --obs-vocab 16 --max-steps 3 --tf-decay-frac 0.65 \
  --w-y-closed 2.0 --w-cand 0.0
```

Universal `tail -f` for the latest run log:

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs
run_dir="$(ls -1dt aslmt_v19_algebra_universal_actionz_v4_8_solid_* | head -n 1)"
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

## Oracle (v4.8)

Let `τ_t` be the transcript prefix (base observation + queried view/response pairs),
and let `F_{τ_t}` be the candidate set consistent with `τ_t`.

The implementation optimizes a lexicographic triple:

```text
(expected_steps_to_closure,
 expected_final_ambiguity,
 expected_final_candidate_size)
```

STOP is allowed iff `Amb_σ(F_{τ_t}) == 1` (closure already holds).

## Smoke (end-to-end)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
v19_algebra_universal_v4_8/aslmt_campaign_v19_algebra_universal_v4_8_matrix_diagstop_actionz.py \
  --profile smoke --device cpu \
  --seed-from 0 --seed-to 0 \
  --n-states-list 64 \
  --n-views 8 --y-classes 2 --obs-vocab 16 --max-steps 3 --w-y-closed 2.0 --w-cand 0.0
```

Independent algebra audit:

```bash
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v19_algebra_universal_v4_8/audit_v19_algebra_universal_v4_8_algebra.py \
  --n-states 64 --n-views 8 --episodes 50 --obs-vocab 16 --max-steps 3
```
