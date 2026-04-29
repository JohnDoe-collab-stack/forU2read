# ASLMT v18 — Algebra Multistep (64) **STRONG v2**

This folder defines a “strong” variant of `v18_algebra_multistep_64` whose purpose is to **exercise multi-step closure selection** rather than a local refinement heuristic.

**Naming note:** the `..._64...` substring is a legacy label in this family name; the actual latent size is controlled by the run argument `--n-states` and is recorded per row as `n_states` in the master JSONL.

## v2 fixes (required for validity)

Two correctness fixes make the protocol well-posed:

- **Set-valued supervision at t=0**: the first query has an intrinsic tie between the two bit views. v2 trains with an allowed-set target `{bit1_idx, bit2_idx}` (multi-positive CE), not an arbitrary ordering by index.
- **Horizon-consistent scoring**: when only one query step remains, the policy scores views with a 1-step expected ambiguity (no extra lookahead).

## What changes vs the base v18

In the base v18 constructive core (`steps=2`), distractor views are **base-only** (constant inside the base fiber). This makes a simple local rule sufficient:

- “pick the two views with `uniq>1` in the base fiber”.

The strong variant removes that shortcut:

- distractor views **also vary inside the base fiber** (they look locally useful),
- yet they do **not** help close `σ`,
- so closure requires identifying the **right conjonction of views**, not a local uniqueness test.

## Construction (steps=2, n divisible by 8)

The latent space is:

```text
X ≅ Base × {0,1} × {0,1} × {0,1}
         base   bit1   bit2   noise
```

- base view reveals `Base`
- two useful views reveal `bit1` and `bit2` (their indices are permuted per episode)
- distractor views reveal only `noise`
- `σ` depends only on `(bit1, bit2)` (XOR/XNOR per base bucket)

So:

- base-only is not closed
- any single query is not closed
- querying both useful views closes `σ`

### Validity constraints

This construction assumes:

- `n_base := n_states / 8` satisfies `n_base <= obs_vocab` (otherwise `O_base` collisions can break the intended fiber structure).

Distractor views are sampled per base bucket; some buckets may draw `a0 == a1`, making that distractor locally constant in that bucket. This is allowed by the protocol, but the strong property relies on having enough varying distractors overall.

## Audits (no parasite channel)

Same audit shape as v18:

- baselines: visible-only and cue-only are near chance
- ablation: zeroing the mediator collapses performance (query loop fails)
- swap: swapping mediator swaps query behavior and collapses correctness
- IID + OOD + multi-seeds: stability

## Files

- `aslmt_env_v18_algebra_multistep_64_strong.py`: strong episode generator + dataset
- `aslmt_model_v18_algebra_multistep_64_strong_actionz.py`: action-as-`z` model (strong policy head)
- `aslmt_train_v18_algebra_multistep_64_strong_matrix_diagstop_actionz.py`: trainer producing master JSONL rows
- `verify_aslmt_v18_algebra_multistep_64_strong_matrix.py`: strict verifier for `solid`
- `aslmt_campaign_v18_algebra_multistep_64_strong_matrix_diagstop_actionz.py`: snapshot + hash runner

## Results (solid)

Completed solid run (n=8, seeds 0..4):
- Run dir: `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v18_algebra_multistep_64_strong_actionz_v2_solid_20260428_220027_5c0ed07ec8b5/`
- Master JSONL: `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v18_algebra_multistep_64_strong_actionz_v2_solid_20260428_220027_5c0ed07ec8b5/v18_algebra_multistep_64_strong_actionz_v2_solid_master_20260428_220027_5c0ed07ec8b5.jsonl`
- Snapshot verifier: `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/snapshots/aslmt_v18_algebra_multistep_64_strong_actionz_v2_solid_20260428_220027_5c0ed07ec8b5/verify_aslmt_v18_algebra_multistep_64_strong_matrix.py`
- Verifier status: `[OK] v18 algebra multistep STRONG matrix checks passed.`

## Model status (what is proven here)

The current `action-as-z` strong model computes an **explicit algebraic planner signal** inside `logits_query`
(horizon-aware expected ambiguity / candidate-set size from `tables`, `σ`, and transcript), and learns only the final
mapping from those computed features to query logits.

So the clean reading is:

- **constructive demonstration**: an internal algebraic planner can causally drive a query loop via a discrete mediator `z`.

Upgrading this into a “learned discovery” claim requires replacing that exact planner computation with a learned encoder
and then auditing that the same invariant structure emerges internally.
