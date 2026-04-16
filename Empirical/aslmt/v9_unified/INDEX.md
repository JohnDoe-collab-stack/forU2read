# `v9_unified` — what to run (and what is legacy)

This folder contains the **v9 unified witness** plus several **training/campaign variants** added during closure work.
Because we follow strict traceability rules, older scripts are kept rather than overwritten.

## Recommended entrypoints (use these)

### A) `n = 4` (closed reference witness)

- Campaign (snapshots code, runs seeds, writes master JSONL, runs strict verifier):
  - `aslmt_campaign_v9_unified_double_barrier_minlift_pair_oodrequired_posloss_pairrank.py`
- Training used by that campaign:
  - `aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood_posloss_pairrank.py`
- Strict verifier:
  - `verify_aslmt_v9_unified_double_barrier_minlift_pair_oodrequired.py`

This is the variant that achieved strict closure in the known passing run documented in
`README_aslmt_v9_unified_double_barrier_minlift.md`.

### B) `n > 4` (structurally valid witness: n-scalable renderer + sampling)

For `n=5,6,...`, the original renderer can become **structurally invalid** in IID (collisions in the `h ↦ position`
map when too few distinct positions exist). Use the n-scalable variant:

- Campaign:
  - `aslmt_campaign_v9_unified_double_barrier_minlift_pair_oodrequired_posloss_pairrank_nscalable.py`
- Training:
  - `aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood_posloss_pairrank_nscalable.py`
- Environment + renderer:
  - `aslmt_env_v9_unified_double_barrier_minlift_nscalable.py`
  - `render_v9_unified_paired_ctx_nscalable.py`

### C) Phase A1 matrix runs (recommended driver)

If your goal is “close the law in `n`” as a matrix over `n`, `z`, and seeds, use the dedicated Phase A1 runner:

- `../v10_phaseA1_kdet/README_aslmt_v10_phaseA1_unified_nscalable_kdet.md`

That runner reuses the v9 witness but enforces a clean modeling constraint: `k` is **visible** and is injected
deterministically into the decoder so the segmentation cannot ignore it.

## Core components (conceptual roles)

- Renderer (paired contexts, double barrier):
  - `render_v9_unified_paired_ctx.py` (original; valid for `n=4`)
  - `render_v9_unified_paired_ctx_nscalable.py` (required for `n>4`)
- Environments (context sampling):
  - `aslmt_env_v9_unified_double_barrier_minlift.py` (original)
  - `aslmt_env_v9_unified_double_barrier_minlift_nscalable.py` (required for `n>4`)
- Models:
  - `aslmt_model_v9_unified_double_barrier_minlift.py` (baseline model)
  - `aslmt_model_v9_unified_double_barrier_minlift_kdet.py` (k-deterministic injection; used by `v10_phaseA1_kdet`)

## Variants kept for traceability (not recommended for new “solid” claims)

- Baseline (no posloss/pairrank):
  - `aslmt_campaign_v9_unified_double_barrier_minlift_pair_oodrequired.py`
  - `aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood.py`
- `posloss` only (helpful diagnostically; weaker than pairrank for strict closure):
  - `aslmt_campaign_v9_unified_double_barrier_minlift_pair_oodrequired_posloss.py`
  - `aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood_posloss.py`
- v2 scripts (historical iteration; kept for reproducibility):
  - `aslmt_campaign_v9_unified_double_barrier_minlift_pair_oodrequired_v2.py`
  - `aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood_v2.py`
  - `aslmt_model_v9_unified_double_barrier_minlift_v2.py`

## Generated artifacts

- `__pycache__/` is Python bytecode cache. It is safe to delete locally, but it is not required for correctness and
should not be treated as a “result”.

