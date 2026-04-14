# Project explanation (COFRS / compat_obstructions)

This file explains what the repository is doing **mathematically**, how the pieces fit together, and how to read the code.

The short thesis sentence the development is built to make _checkable_ is:

> Diagonalization destroys the static regime of closed global decisions, forces their factorization through a mediator, and makes causality the testable signature of that forced factorization.

The entire development is intended to remain **constructive** (no `Classical`, no axioms), with per-file `AXIOM_AUDIT` blocks.

## Problem Solved

When a diagonalization exhibits that the observable interface `obs : S → V` is insufficient to decide a dynamic truth—future compatibility along a chosen `step` (formalized as `Compatible sem obs target_obs step x`)—the repository resolves three sub-problems end-to-end:

1. **certify the failure of any obs-only rule** (in the precise sense of `ObsPredictsStep`, i.e. a decision rule depending only on `V`);
2. **identify and quantify the minimal missing information** as a finite supplement `Fin n` (compatibility dimension on the observable fiber);
3. **provide an intervention-testable signature** that the decision truly depends on this supplement (causal mediation, not mere correlation).

## Resolution in the repository (Lean names)

- **Obstruction (intra-fiber diagonalization).** A witness `LagEvent` exhibits two states that are indistinguishable by `obs` yet separated by the targeted dynamic truth; the development derives `LagEvent → ¬ ObsPredictsStep` (see `COFRS/Dynamics.lean`, `PrimitiveHolonomy.not_obsPredictsStep_of_lagEvent`).
- **Minimal finite mediator (capacity).** The required extra information is measured by `CompatDimLe n` / `CompatDimEq n` and realized canonically by a mediation witness `RefiningLiftData`/`RefiningLift`, with the central equivalence `CompatDimLe … n ↔ RefiningLift … n` (see `COFRS/Dynamics.lean`, `PrimitiveHolonomy.compatDimLe_iff_refiningLift`). The proven “minimality” is a minimality of **dimension/capacity** (size of `Fin n`), not ontological uniqueness of a latent.
- **Testable causal signature (ablation + permutation).** Mediation is not treated as mere factorization: it is made intervention-testable via `CausalSignature2`, linked to intra-fiber separation together with the existence of a finite lift (see `COFRS/Examples/DiagonalizationMediationCausalityThesis.lean`, notably `causalSignature2_of_stepSeparatesFiber_of_refiningLift2` and `diagonalization_yields_causalSignature2`).
- **Terminology.** Here, “diagonalization” means: “against any visible-only rule in the sense of `ObsPredictsStep`, exhibit a fiber where it fails”. The “diagonalization by code” instance is handled separately in `COFRS/Examples/GodelByCode.lean`.

## Chain (quick reading)

`LagEvent` → `¬ ObsPredictsStep` → `CompatDim* n` → `RefiningLift* n` → `CausalSignature2`

---

## 0. The core idea in one paragraph

The development models “histories” as a minimal 2-dimensional combinatorial structure (prefixes, paths, and admissible commutations), and interprets paths by a **relational** semantics on a state space `S`. An **observable** `obs : S → V` induces fibers of microstates that are indistinguishable at a given prefix `h`. A _lag event_ (`LagEvent`) is a witness that two distinct microstates in the same fiber are holonomy-related now, but diverge on future compatibility along a chosen step. This single witness is strong enough to forbid any “obs-only” predictor. The key step is that the repository then **quantifies** the amount of extra information needed to recover predictability via a finite mediator `Fin n` (`CompatDim` / `RefiningLift`), and turns that forced mediation into a **testable intervention signature** (permutation/ablation) on the mediator.

---

## 1. The framework (Primitive Holonomy)

### 1.1 Minimal 2-structure of histories

A history world is given by `HistoryGraph`:

- objects `P` (prefixes),
- 1-morphisms `Path : P → P → Type` (schedules/paths),
- 2-morphisms `Deformation` witnessing admissible commutations,
- identity and composition of paths.

This is deliberately _not_ a full-blown category-theory development: it is a minimal interface tuned to what the rest of the project needs.

### 1.2 Relational semantics

A `Semantics P S` assigns to each path a binary relation on states:

- `sem : Path h k → (S → S → Prop)`,
- plus compatibility with identity/composition (as _relational equalities_).

The choice of relations (not functions) is essential: it naturally supports nondeterminism and partial information.

### 1.3 Observation, fibers, and holonomy

Given an observation map `obs : S → V` and a target observation `target_obs : P → V`, the **fiber** above a prefix `h` is:

- `FiberPt obs target_obs h := { x : S // obs x = target_obs h }`.

Transport along a path is simply the semantics restricted to fibers. Holonomy is defined from a deformation witness by composing transport along one path with the converse transport along the other.

**Where:** `COFRS/Foundations.lean`.

---

## 2. Dynamics: compatibility, lag, and no-go for obs-only prediction

### 2.1 Compatibility

For a future step `step : Path h k`, and a microstate `x` in the fiber at `h`,

- `Compatible sem obs target_obs step x` means: there exists a fiber point at `k` reachable from `x` via transport along `step`.

This is a deliberately local notion: compatibility is defined **per microstate on a fiber**, not as a global predicate.

### 2.2 LagEvent (the obstruction witness)

A `LagEvent` packages the key obstruction:

- two distinct microstates `x ≠ x'` in the same fiber at `h`,
- related by holonomy now,
- but only one remains compatible along a chosen future step.

From a `LagEvent` one obtains `StepSeparatesFiber` for that step.

### 2.3 No visible predictor (and no obs-only predictor)

Two notions of “predictor” are defined for a fixed future step:

- `VisiblePredictsStep`: there exists some summary `σ` that factors through `obs` (i.e. depends only on visible data) and predicts compatibility.
- `ObsPredictsStep`: the strongest special case where the predictor is a predicate directly on `V`.

Main no-go chain:

- `LagEvent → ¬ VisiblePredictsStep` (via `StepSeparatesFiber`).
- `LagEvent → ¬ ObsPredictsStep` (since `ObsPredictsStep → VisiblePredictsStep`).

**Where:** `COFRS/Dynamics.lean` (notably theorems `not_visiblePredictsStep_of_lagEvent` and `not_obsPredictsStep_of_lagEvent`).

Intuitively: any summary that factors through `obs` is constant on the fiber, so it cannot predict a property that genuinely varies inside a single fiber.

---

## 3. Forced factorization through a finite mediator (CompatDim / RefiningLift)

The project does not stop at a no-go statement. It introduces an internal, quantitative notion of forced mediation.

### 3.1 Internal (not visible) compatibility dimension

`CompatDimLe sem obs target_obs step n` says:

- there exists a finite index `σ : fiber(h) → Fin n` and a predicate on `Fin n` such that
- `Compatible step x` depends only on `σ x`.

Crucially, `CompatDimLe` does _not_ require factoring through `obs`; it measures hidden information needed to decide compatibility.

`CompatDimEq` / `CompatDimEqTwo` package **exactness/minimality**.

### 3.2 Canonical lift: RefiningLiftData

A `RefiningLiftData` is an explicit witness living **on the fiber**:

- `extObs : fiber(h) → V × Fin n`,
- it refines the visible observation on the first component,
- and compatibility factors only through the `Fin n` component.

There is a key canonical equivalence:

- `CompatDimLe … n ↔ RefiningLift … n`.

This is the repository’s formal notion of:

> “factorization through a mediator”

where the mediator is finite (`Fin n`) and the refinement keeps the original visible interface intact.

**Where:** `COFRS/Dynamics.lean` (`CompatDimLe`, `RefiningLiftData`, `compatDimLe_iff_refiningLift`).

---

## 4. Regulation and obstruction (gauges)

A gauge is a fiber-preserving “repair” mechanism applied at targets of transport.

- `CorrectedTransport` applies transport then gauge;
- `CorrectedHolonomy` is holonomy computed from corrected transports.

Two key global notions are defined on sets of cells:

- `AutoRegulatedWrt OK J`: there exists an admissible gauge (`OK φ`) such that corrected holonomy is diagonal on `J`.
- `ObstructionWrt OK J`: every admissible gauge fails, by producing a twisted corrected holonomy witness.

This layer is what enables expressing “repairability vs obstruction” inside the same fiber/holonomy language.

**Where:** `COFRS/RegulationAndReduction.lean`.

---

## 5. Causality as a testable signature (permutation + ablation)

The repository defines a concrete “intervention-style” signature for a forced `Fin 2` mediator:

- **Permutation**: swapping the `Fin 2` class changes the induced readout on some fiber point.
- **Ablation**: collapsing the mediator to a constant readout cannot remain correct if the step separates the fiber.

These are packaged as:

- `CausalSignature2`.

Core theorem (Lean):

- `causalSignature2_of_stepSeparatesFiber_of_refiningLift2` proves `StepSeparatesFiber … step → RefiningLift … step 2 → CausalSignature2 … step`.

So, once factorization through a finite mediator is forced (and the fiber is dynamically separated), **causality becomes the testable signature** of that forced factorization.

**Where:** `COFRS/Examples/DiagonalizationMediationCausalityThesis.lean`.

---

## 6. The diagonal-by-code instance (why `GodelByCode` exists)

`COFRS/Examples/GodelByCode.lean` is a _concrete instance generator_ inside the COFRS framework.

It builds:

- a minimal `HistoryGraph` on `Nat` with a single non-trivial deformation (`p ⇒ q`),
- a relational semantics on states `LagState Nat Bool`,
- two explicit diagonal fiber points `x` and `x'` (same visible, different hidden bit),
- and then proves:
  - a diagonal lag witness `lagEvent_at_diag`,
  - an internal dimension upper bound `diag_compatDimLe_two_step`,
  - and exactness `diag_compatDimEqTwo_step`.

This instance is then used by the “thesis spine” to derive:

- `diagonalization_yields_causalSignature2`.

The point is not “classical Gödel logic”; it is to realize, inside the project’s holonomy/fiber semantics, a diagonal mechanism that **forces**:

- no obs-only decision regime,
- a minimal finite mediator (exactly `Fin 2`),
- and therefore the causal signature.

---

## 7. Independence: geometry vs dynamics

`COFRS/Examples/GeometryDynamicsIndependence.lean` demonstrates that:

- “geometric coherence” (existence of a non-trivial holonomy witness), and
- “dynamic truth” (visible predictability of compatibility)

are logically independent in this framework.

This isolates an important message: geometric alignment proxies do not imply dynamic correctness, and dynamic correctness can occur without non-trivial holonomy.

---

## 8. How to read the repository

Recommended order:

1. `COFRS/Foundations.lean` (framework: fibers, transport, holonomy)
2. `COFRS/Dynamics.lean` (lag/no-go, compat dimension, refining lift)
3. `COFRS/RegulationAndReduction.lean` (gauges, regulation/obstruction)
4. `COFRS/Examples/DiagonalizationMediationCausalityThesis.lean` (signature causale)
5. `COFRS/Examples/GodelByCode.lean` (diagonal instance)
6. `COFRS/Examples/GeometryDynamicsIndependence.lean` (independence)

---

## 9. Constructivity and axiom audit

The repo is designed to remain constructive:

- no `axiom`
- no `Classical` / `open Classical`
- no `propext`
- no `Quot.sound`

Relevant `.lean` files contain a final `AXIOM_AUDIT` block (`#print axioms …`).

## Collaboration note

This `Project` was written mainly in collaboration with **ChatGPT Codex** (OpenAI).
