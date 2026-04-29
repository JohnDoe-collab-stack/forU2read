# ASLMT v18 — Algebra Multistep (64)

This family is a **synthetic, deterministic** benchmark whose goal is to make the following object *operational*:

- a finite state space `X` of size `n`
- a target “truth” / signature `σ : X → Y`
- a set of observation interfaces (“views”) `O_i : X → V_i`
- a query loop that selects views sequentially

The task is constructed so that:

- `σ` is **not closed** on the initial visible interface (the base view alone),
- `σ` becomes **closed** after a small number of query steps,
- the protocol audits that success depends on the query loop and its internal mediator.

## What is tested

For each episode:

- `σ` and all `O_i` are provided as a **cue table** (problem definition).
- the latent element `x ∈ X` is provided only via the **base observation** `O_base(x)` (initial interface).
- the model must pick a sequence of views `i₁, …, i_T` and receives responses `O_{i_t}(x)`.
- the model must output `σ(x)` after the query loop.

This enforces the regime:

- visible-only is insufficient,
- closure is achieved by composing views (meet) through action/query.

## Audits (no parasite channel)

The verifier checks, per `n` and over multiple seeds, for both IID and OOD:

- **barriers**: the base observation alone is insufficient by construction
- **baselines**: a visible-only baseline and a cue-only baseline remain at chance level
- **ablation**: zeroing the mediator used by the query policy collapses performance
- **swap**: swapping the mediator between paired contexts swaps the chosen query behavior and collapses correctness
- **IID + OOD + multi-seeds**: stability of the regime

## Files

- `aslmt_env_v18_algebra_multistep_64.py`: episode generator + optimal policy labels
- `aslmt_model_v18_algebra_multistep_64.py`: mediator (`z`) + query policy (`zread`) + classifier
- `aslmt_train_v18_algebra_multistep_64_matrix_diagstop.py`: trainer producing master JSONL rows
- `aslmt_train_v18_algebra_multistep_64_matrix_diagstop_rollout.py`: rollout-aligned trainer (recommended for `solid`)
- `aslmt_model_v18_algebra_multistep_64_actionz.py`: model variant where the discrete mediator `z` is the action code (recommended)
- `aslmt_train_v18_algebra_multistep_64_matrix_diagstop_actionz.py`: trainer for the action-as-`z` model (recommended for `solid`)
- `verify_aslmt_v18_algebra_multistep_64_matrix.py`: strict verifier for `solid`
- `aslmt_campaign_v18_algebra_multistep_64_matrix_diagstop.py`: snapshot + hash runner
- `aslmt_campaign_v18_algebra_multistep_64_matrix_diagstop_rollout.py`: snapshot + hash runner for rollout-aligned trainer
- `aslmt_campaign_v18_algebra_multistep_64_matrix_diagstop_actionz.py`: snapshot + hash runner for the action-as-`z` model

## Smoke vs solid

`smoke` is wiring-only (quick run, light thresholds).

`solid` is strict (multi-seeds + IID/OOD thresholds).

## Strong variant

The folder `../v18_algebra_multistep_64_strong_v2/` defines a **strong** variant that removes the shortcut:

> “pick the two views with `uniq>1` in the base fiber”.

In the strong variant, distractor views also vary inside the base fiber but do not help close `σ`, so
view selection must track **closure**, not just local refinement.

The `*_strong_v2` folder also includes two correctness fixes that make the `steps=2` supervision well-posed:

- set-valued query target at `t=0` (intrinsic tie between the two bit views),
- horizon-consistent scoring (2-step lookahead only when 2 steps remain).

## Run tracking

To follow a run log:

```bash
tail -f Empirical/aslmt/runs/<run_dir>/train_<...>.txt
```

To re-check a master JSONL:

```bash
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u Empirical/aslmt/v18_algebra_multistep_64/verify_aslmt_v18_algebra_multistep_64_matrix.py \
  --master-jsonl Empirical/aslmt/runs/<run_dir>/<master>.jsonl \
  --profile solid --min-seeds 5 --n-states-list 8
```

## Results (solid)

Completed solid run (n=8, seeds 0..4):
- Run dir: `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v18_algebra_multistep_64_actionz_solid_20260428_155907_579302681f91/`
- Master JSONL: `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v18_algebra_multistep_64_actionz_solid_20260428_155907_579302681f91/v18_algebra_multistep_64_actionz_solid_master_20260428_155907_579302681f91.jsonl`
- Snapshot verifier: `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/snapshots/aslmt_v18_algebra_multistep_64_actionz_solid_20260428_155907_579302681f91/verify_aslmt_v18_algebra_multistep_64_matrix.py`
- Verifier status: `[OK] v18 algebra multistep matrix checks passed.`
