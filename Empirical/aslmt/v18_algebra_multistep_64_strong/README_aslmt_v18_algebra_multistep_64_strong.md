# ASLMT v18 — Algebra Multistep (64) **STRONG**

This folder defines a “strong” variant of `v18_algebra_multistep_64` whose purpose is to **exercise multi-step closure selection** rather than a local refinement heuristic.

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

