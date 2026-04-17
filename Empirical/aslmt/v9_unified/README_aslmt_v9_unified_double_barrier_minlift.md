# ASLMT v9 (Unified) — Double-Barrier + Min-Lift (Pair-Grade, OOD-Required)

`v9_unified` is a **single, consistent** empirical witness intended to simultaneously cover the key properties isolated by:

- `v7_descriptive`: **image-only no-go** (obs-only barrier).
- `v8_descriptive`: **double barrier** (image-only **and** cue-only no-go).
- `vN3b_descriptive`: **min-lift / capacity** (success at `z=n`, failure at `z<n`), with causal gates.

Concretely, `v9_unified` enforces:

1. **Image-only barrier**: fix `k`, vary `h` → same `image`, different `hidden_target`.
2. **Cue-only barrier**: fix `h`, vary `k` → same `cue_image`, different `hidden_target`.
3. **Min-lift**: for a chosen `n`, a mediator of capacity `z=n` is sufficient, while `z<n` is insufficient (under the strict verifier).
4. **Causal gates (binary swap/ablation)** on the image-barrier pair.

## Training note (important)

To avoid the failure mode “`z` is sharp but not semantic”, the training uses an explicit supervised attachment
`h → z` exactly as in `vN3b_descriptive`:

- `lossA_z = cross_entropy(z_logits, h mod z)`
- `lossA = lossA_seg + w_z * lossA_z`

Additionally, to harden the cue-barrier closure, the training also adds a small auxiliary head on `image` to
predict the present bit `k`:

- `lossA_k = cross_entropy(k_logits(image), k)`
- `lossA = ... + w_k * lossA_k`

and logs `z_acc` and `k_acc` (IID/OOD) into the JSONL row.

## Closure note (what actually closes)

In practice, getting **strict closure** on the **image-barrier pair-grade** (`A_img_min=1.0` on IID+OOD across seeds)
requires not only “semantic” correctness (`h → z`, `k` readout), but also **geometric selectivity** in the produced mask.

Two training variants are provided to enforce that selectivity while keeping the benchmark unchanged:

- **`posloss`**: adds a centroid loss on `A` (`center_of_mass`) to improve placement.
- **`posloss + pairrank`**: adds an explicit **pair-grade ranking loss** on the image-barrier to force “beat the competitor bar”
  (this is the strictest and currently the recommended variant).

This folder is designed to be the base witness for the “universality” roadmap in `Empirical/aslmt/UNIVERSALITY_PLAN.md`.

## Files

For a quick “what should I run?” view (and which scripts are legacy), see `v9_unified/INDEX.md`.

- Environment + renderer:
  - `aslmt_env_v9_unified_double_barrier_minlift.py`
  - `render_v9_unified_paired_ctx.py`
- Models:
  - `aslmt_model_v9_unified_double_barrier_minlift.py`
- Training (writes a master JSONL row per `(seed,z)`):
  - `aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood.py`
  - `aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood_posloss.py`
  - `aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood_posloss_pairrank.py`
- Strict verifier:
  - `verify_aslmt_v9_unified_double_barrier_minlift_pair_oodrequired.py`
- Campaign runner (snapshots scripts with hash):
  - `aslmt_campaign_v9_unified_double_barrier_minlift_pair_oodrequired.py`
  - `aslmt_campaign_v9_unified_double_barrier_minlift_pair_oodrequired_posloss.py`
  - `aslmt_campaign_v9_unified_double_barrier_minlift_pair_oodrequired_posloss_pairrank.py`

## Run (cuda)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u v9_unified/aslmt_campaign_v9_unified_double_barrier_minlift_pair_oodrequired.py \
  --profile solid \
  --seed-from 0 --seed-to 4 \
  --n-classes 4 \
  --z-classes-list 3,4 \
  --device cuda
```

## Run (cuda, recommended: posloss + pairrank)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u v9_unified/aslmt_campaign_v9_unified_double_barrier_minlift_pair_oodrequired_posloss_pairrank.py \
  --profile solid \
  --seed-from 0 --seed-to 4 \
  --n-classes 4 \
  --z-classes-list 3,4 \
  --device cuda \
  --w-z 5.0 --w-k 1.0 --w-pos 0.25 \
  --w-rank-img 0.25 --rank-n-ctx 8 --rank-ood-ratio 0.5
```

## Expected verifier reading (solid)

- Reference group `z=n`:
  - barrier checks hold (image + cue),
  - `A_*_min=1.0` on IID and OOD,
  - baselines `B_*_max=0.0`,
  - causal gates pass (ablation breaks; swap follows).
- Any `z<n`:
  - cannot close the **image-barrier** pair rate to `1.0` on IID and OOD.

## Known passing run (reference)

The following run passes the strict verifier (`solid`) with `n=4` and seeds `0..4`:

- Run directory:
  - `Empirical/aslmt/runs/aslmt_v9_unified_posloss_pairrank_minlift_20260415_102415_816648957b45`
- Verifier output:
  - `Empirical/aslmt/runs/aslmt_v9_unified_posloss_pairrank_minlift_20260415_102415_816648957b45/verify_20260415_102415_816648957b45.txt`

## Phase A1 matrix runner (v10)

If you want to execute **Phase A1** (“close the law in `n`”) as a **single strict matrix** over:

- `n ∈ {3,4,5,6}` (configurable),
- `z ∈ {n, n-1, ⌊n/2⌋}` (configurable),
- multi-seeds,

use the dedicated campaign+verifier layer:

- `Empirical/aslmt/v10_phaseA1/README_aslmt_v10_phaseA1_unified_nscalable.md`

This keeps `v9_unified` as the witness definition, and moves the “Phase A1 closure protocol” into v10.

### Closed A1 reference (recommended)

The best-documented strict A1 closure currently uses:

- the k-deterministic decoder conditioning (`k-det`), and
- the spaced2 witness variant (reduced overlap; strict pair-grade closure is achievable).

Entry point:

- `Empirical/aslmt/v10_phaseA1_kdet_spaced2/README_aslmt_v10_phaseA1_unified_nscalable_kdet_spaced2.md`

Run:

- `Empirical/aslmt/runs/aslmt_v10_phaseA1_unified_nscalable_posloss_pairrank_kdet_spaced2_20260416_074821_9fcd16977fda/`

## Scaling note (`n > 4`)

The original `v9_unified` renderer uses a modulo position map for the hidden class `h`. In IID contexts, the number of
available distinct positions can drop to **4** (e.g. when `occ_half=5`), so for `n=5` the image-barrier can become
structurally invalid (collisions in `h` → identical targets for distinct `h`).

For `n>4`, use the **n-scalable** variant that:

- constrains context sampling as a function of `n` so the witness remains valid in IID and OOD, and
- makes the `h ↦ position` map injective within the inner region.

Files:
- `render_v9_unified_paired_ctx_nscalable.py`
- `aslmt_env_v9_unified_double_barrier_minlift_nscalable.py`
- `aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood_posloss_pairrank_nscalable.py`
- `aslmt_campaign_v9_unified_double_barrier_minlift_pair_oodrequired_posloss_pairrank_nscalable.py`

Example (cuda, `n=5`, test `z=4,5`):
```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u v9_unified/aslmt_campaign_v9_unified_double_barrier_minlift_pair_oodrequired_posloss_pairrank_nscalable.py \
  --profile solid --device cuda \
  --seed-from 0 --seed-to 4 \
  --n-classes 5 --z-classes-list 4,5 \
  --w-z 5.0 --w-k 1.0 --w-pos 0.25 \
  --w-rank-img 0.25 --rank-n-ctx 8 --rank-ood-ratio 0.5
```

Note: the n-scalable variant ensures the **barrier lock** remains valid when `n` grows. It does not guarantee
that the learner achieves strict `A_*_min=1.0` at larger `n` without additional closure engineering. In practice,
the `k-det` and `spaced2` refinements were introduced specifically to close Phase A1 strictly through `n=6`
under `profile=solid`.
