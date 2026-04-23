# COFRS-style upgrade path for V-JEPA2 (turning JEPA into a solver)

Source read: `facebookresearch/vjepa2` (V-JEPA 2 / 2.1 / 2-AC). In this repo, V-JEPA2 pretraining is a masked **latent feature prediction** scheme with:
- `encoder` (context encoder),
- `target_encoder` (EMA / momentum teacher),
- `predictor` (predict masked target features from context features),
- `MaskCollator` producing `(masks_enc, masks_pred)` for multi-sequence training.

Canonical forward path in `app/vjepa/train.py`:
- `h := target_encoder(clips)` (no-grad teacher features, layer-normed),
- `z := encoder(clips, masks_enc)` then `predictor(z, masks_enc, masks_pred)` (student predicted features),
- JEPA loss: `|z - h|^p` on the masked tokens.

This document specifies a **minimal, explicit set of additions** that upgrade this family from “representation/prediction” to a **solver** whose admissible mechanisms are stratified by **closure regime**.

---

## 0) Core objects (interface, truth, closure)

Let:
- `X` = underlying states (video/world trajectories, or task states).
- `q : X → V` = the **visible interface** actually fed into the solver at a given stage (e.g. V-JEPA2 context tokens, or a chosen masking/observation policy).
- `T : X → Y` = the **truth to be decided** (a target property, decision, compatibility predicate, etc.).

**Closure on the visible** means:
- `T` factorizes through `q`: there exists `f : V → Y` such that `T(x) = f(q(x))` for all `x`.

**Non-closure** means:
- there exist `x₁, x₂` with `q(x₁) = q(x₂)` but `T(x₁) ≠ T(x₂)`.

The upgrade below makes this dichotomy **operational** inside the model/training protocol, rather than implicit.

---

## 1) What V-JEPA2 already gives you (useful substrate)

From the repo:
- A high-capacity **visible interface** `V` = encoder features over masked context tokens.
- A predictor that learns **structure in representation space** under masks (`VisionTransformerPredictor`).
- An action-conditioned variant (`VisionTransformerPredictorAC`) that already accepts explicit `actions/states/extrinsics`.
- A mask system (`MaskCollator`, multi-block masks) that can be reinterpreted as a *queryable interface* (choose which tokens become visible).

These are good building blocks for a solver, but the solver upgrade requires new *contracts* and *audits*.

---

## 2) Additions: closure monitor + mediator + (optional) query loop + audit

### 2.1 `ClosureMonitor` (the closure/diagonalization layer)

Add a module that attempts to decide `T` from the current interface alone:

**Inputs**
- `v = q(x)` encoded as V-JEPA2 context features (e.g. post-encoder tokens, pooled tokens, or a small set of “decision tokens”).

**Outputs**
- `ŷ_visible` = attempted decision from the visible interface.
- `closure_score` = calibrated confidence that the decision is *closed on the current interface*.
- `diag_witness` (operational) = a mechanism to *surface* non-closure cases, e.g. by producing pairs / counterexamples within the same visible fiber.

**Operationalization**
- In synthetic/controlled tasks, you can build `diag_witness` directly: same visible `v`, different hidden cause affecting `T`.
- In real video, you approximate with invariance tests: augmentations, counterfactual crops, or alternative tokenizations that preserve the interface while varying candidate futures.

Goal: this module makes “closure vs non-closure” a first-class **measured regime**, not a hidden assumption.

### 2.2 `Mediator z` (explicit non-marginal mediation)

Add an explicit internal mediator `z` intended to carry what is missing when closure fails.

**Contract**
- Predictions that are correct in non-closure regimes must be *structure-dependent* on `z`, not only on visible tokens.

**Implementation choices (compatible with V-JEPA2)**
- Introduce a small number of dedicated latent tokens `z_tokens` that:
  - are produced by the student (encoder/predictor),
  - are stable under the same invariances as the JEPA features,
  - are exposed for audit (swap/ablation).
- Alternatively, treat a designated slice of the predictor output as `z` (but keep it explicitly named and interventionable).

### 2.3 `QueryPolicy` + `Response` (autoreflexive upgrade, optional but decisive)

When non-closure is detected/expected, the solver may require reconfiguring its access to information.

Add:
- `a = π(z, v)` a query/action chosen from the internal state (at minimum: `a ∈ {0,1}` like “request interface B vs A”, or “reveal mask block family i”).
- A **response channel** determined by the environment/data interface: `r = env(x, a)`.
  - In video, `env` can be: an additional view, an additional time slice, a different modality tokenizer, or extra unmasked tokens chosen by `a`.
  - In V-JEPA2-native terms: `a` selects a mask / token subset to reveal (changing `masks_enc`), yielding new visible tokens as `r`.

Then define a post-query state:
- `s_post = update(v, z, r)` (explicitly stored).
- Final decision `ŷ = decide(s_post)`.

This enforces the causal chain:
`(internal mediator) → (query) → (action-conditioned response) → (post-state) → (decision)`.

### 2.4 Intervention audit (must be part of the acceptance criteria)

To qualify as a solver with explicit mediation, require intervention tests:

- **Ablation**: set `z := 0` (or replace `z_tokens` by constant) and measure a strict performance collapse on non-closure tasks.
- **Swap**: permute `z` across batch items; require “swap-follow” behavior (decision tracks swapped mediator) and “swap-orig” collapse where appropriate.
- **Forced action**: compare `runUnder(a=0)` vs `runUnder(a=1)` on the same underlying `x` (counterfactual branch), and require a decision difference when the query is operationally necessary.

This is not “extra analysis”; it is the gate that prevents “good score, wrong mechanism”.

---

## 3) How to realize the query mechanism using existing V-JEPA2 machinery

There are two clean integration routes in their codebase:

### Route A: Query-as-mask-selection (native JEPA view)

Use `MaskCollator` as the “interface generator”.

- Let `a` select among a small family of mask generators / mask parameters.
  - Example: `a=0` reveals only “interface A” tokens; `a=1` reveals “interface B” tokens.
- The “response” `r` is the additional revealed token set induced by the chosen mask.
- `ClosureMonitor` decides whether interface A is closed; if not, it forces `a=1`.

Benefits:
- Minimal disturbance to the V-JEPA2 training/eval loops.
- Keeps everything inside the token/mask algebra they already use.

### Route B: Use V-JEPA2-AC as the query loop carrier (world-model view)

Use `VisionTransformerPredictorAC`:
- Feed `(actions, states, extrinsics)` as the explicit query/action stream.
- Treat the predicted future features as the “post-query state”.

Benefits:
- Action-conditioning is explicit and already implemented in the repo.
- Clean place to encode `runUnder` (forced actions) for causal audit.

---

## 4) Minimal stratified solver spec (what must exist, and what must be proven by tests)

### Regime 1: closure holds on the visible interface

Required:
- `ClosureMonitor` reports closure, and `ŷ_visible` is correct.

Admissible solver class:
- “visible-only” decision head over current interface features.

### Regime 2: closure fails on the visible interface

Required:
- `diag_witness` exists (operationally) and closure monitor flags non-closure.
- A mediator `z` exists and is required by audit (ablation_drop, swap_follow).

Admissible solver class:
- autoreferential mediation (decision depends on non-marginal mediator).

### Regime 3: closure fails and the required mediator is only accessible via reconfigured access

Required:
- query loop exists: `a = π(z, v)` and `r = env(x, a)` with a true action-conditioned effect.
- forced-action audit shows `runUnder` differs on the same `x` when necessary.

Admissible solver class:
- autoreflexive (query-driven access reconfiguration).

---

## 5) Acceptance metrics (what the upgraded V-JEPA2 must report)

Add a “solver acceptance” report alongside standard JEPA losses:

- `closure_acc` on tasks where closure should hold.
- `diag_witness_rate` (or explicit witness success rate) on tasks where non-closure should be exposed.
- `ablation_drop` and `swap_follow / swap_orig` scores for the mediator.
- `forced_action_effect` and `counterfactual_decision_effect` for the query loop.
- Optional: `mediator_capacity` (dimension / number of `z_tokens`) as a minimality axis.

---

## 6) Minimal implementation plan (in their repo terms)

This section is intentionally concrete in terms of *where* the hook points are:

1. Start from `app/vjepa/train.py`:
   - They already compute `(h := target_encoder(clips), z := predictor(encoder(clips)))`.
2. Add `ClosureMonitor(z_context)` that predicts a task truth `T` (or a proxy task) and logs closure/non-closure.
3. Add explicit `z_tokens` (or a named `z`) and route the decision head through it.
4. For autoreflexive mode:
   - implement `a = QueryPolicy(z, context_features)`,
   - define `env` as “additional tokens revealed / additional view loaded / additional modality tokens”,
   - implement `runUnder` for forced-action branches.
5. Add an audit harness that runs `ablation/swap/forced-action` and fails the run if the audit does not match the intended regime.

---

## 7) Summary (one sentence)

V-JEPA2 already provides strong predictive representations; the solver upgrade is to make **closure** explicit and to force (and audit) the correct **mediator** and (when needed) an **autoreflexive query loop** driven by the internal state.

