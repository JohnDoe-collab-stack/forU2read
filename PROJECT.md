# Project explanation (`COFRS` / `compat_obstructions`)

This file explains what the repository is doing mathematically, how the pieces fit together, and how to read the code.

The short thesis sentence the development is built to make checkable is:

> Diagonalization destroys the static regime of closed global decisions, forces their factorization through a mediator, and makes causality the testable signature of that forced factorization.

The entire development is intended to remain constructive: no `Classical`, no axioms, with per-file `AXIOM_AUDIT` blocks.

## Problem solved

When a diagonalization shows that the observable interface `obs : S → V` is insufficient to decide a dynamic truth, namely future compatibility along a chosen `step` as formalized by `Compatible sem obs target_obs step x`, the repository resolves three problems in one formal chain:

1. it certifies the failure of any `obs`-only decision rule, in the precise sense of `ObsPredictsStep`;
2. it identifies and quantifies the minimal missing information as a finite supplement `Fin n` on the observable fiber;
3. it provides an intervention-testable signature showing that the decision genuinely depends on this supplement, as causal mediation rather than mere correlation.

## Resolution in the repository

The formal resolution is organized by three linked ingredients.

- **Obstruction by intra-fiber diagonalization.** A witness `LagEvent` exhibits two states that are indistinguishable by `obs` yet separated by the targeted dynamic truth. From this, the development derives `LagEvent → ¬ ObsPredictsStep`; see `COFRS/Dynamics.lean`, theorem `PrimitiveHolonomy.not_obsPredictsStep_of_lagEvent`.

- **Minimal finite mediator.** The missing information is measured by `CompatDimLe n` and `CompatDimEq n`, and realized canonically by `RefiningLiftData` and `RefiningLift`. The central equivalence is `CompatDimLe … n ↔ RefiningLift … n`; see `COFRS/Dynamics.lean`, theorem `PrimitiveHolonomy.compatDimLe_iff_refiningLift`. The minimality proved here is a minimality of dimension or capacity, that is, the size of `Fin n`, not an ontological uniqueness claim about a latent variable.

- **Testable causal signature.** Mediation is not treated as a mere factorization statement. It is made intervention-testable through `CausalSignature2`, linked to intra-fiber separation together with the existence of a finite lift; see `COFRS/Examples/DiagonalizationMediationCausalityThesis.lean`, especially `causalSignature2_of_stepSeparatesFiber_of_refiningLift2` and `diagonalization_yields_causalSignature2`.

Throughout this document, “diagonalization” means: against any visible-only rule in the sense of `ObsPredictsStep`, exhibit a fiber where it fails. The separate “diagonalization by code” instance is handled in `COFRS/Examples/GodelByCode.lean`.

## Chain of results

The repository’s central chain is:

`LagEvent` → `¬ ObsPredictsStep` → `CompatDim* n` → `RefiningLift* n` → `CausalSignature2`

This should be read as the structural spine of the development: diagonal obstruction yields visible impossibility; visible impossibility is overcome only by a finite mediator; and, in the binary case, this forced mediation acquires an intervention-testable causal signature.

In short:

**diagonalization → no obs-only prediction → minimal finite mediation → causal intervention signature**

## Impact

The thesis of the repository is realized as a concrete three-level pipeline:

- **From diagonal obstruction to system-level impossibility.** A lag witness yields a fiber separation and forbids any closed `obs`-only decision regime in the formal sense of `ObsPredictsStep`; see `COFRS/Dynamics.lean`, notably `not_obsPredictsStep_of_lagEvent`.

- **From impossibility to forced factorization through a finite mediator.** The amount of hidden information required for recovery is quantified by `CompatDimEq n`, and made canonical by the equivalence `CompatDimLe … n ↔ RefiningLift … n`, with explicit witness `RefiningLiftData` and finite mediator `Fin n` on the observable fiber; see `COFRS/Dynamics.lean`.

- **From forced mediation to causal testability.** When a separating step is paired with a forced mediator, notably `Fin 2` in the diagonal instance, intervention-style effects become provable consequences and are packaged as `CausalSignature2`; see `COFRS/Examples/DiagonalizationMediationCausalityThesis.lean`.

### Two-interface strengthening: an irreducible relational term

The development also supports a strictly stronger pattern than “one interface is insufficient”.
Fix two partial interfaces (two “margins”) `A : S → VA` and `B : S → VB`, and consider the joint interface `AB : S → VA × VB`.

The strong situation of interest is:

1. **Each margin is insufficient on its own.** One can certify `¬ ObsPredictsStep` for `obs := A` and for `obs := B`.
2. **The joint dynamic truth is recoverable only through a finite supplement.** On the fiber of `AB`, the truth factorizes through a minimal finite mediator `Fin n` (via `CompatDimEq n` / `RefiningLift n`).
3. **The mediator is irreducible to either margin.** Even when `A` (resp. `B`) is held fixed on the joint fiber, the joint truth is not predictable from `A` alone (resp. `B` alone); equivalently, the mediator does not “descend” to a function of `A` alone or `B` alone.

This makes precise the claim that what closes the decision is not any single margin, but a genuinely relational term carried only at the joint level (and, in the binary case, audit-able by interventions).

The corresponding spine is packaged and proved constructively in `COFRS/Examples/IndependenceRelationMediationChain.lean`, notably:

- marginal no-go: `double_noGo_of_lagEvent`;
- constructive extraction of separation + minimal joint lift: `double_noGo_to_separation_and_minimalJointLift`;
- explicit “not predictable from left/right margin” forms: `LeftObsPredictsJointStep`, `RightObsPredictsJointStep` and their negations from `StepSeparatesFiber`;
- explicit “mediator does not descend to left/right” forms: `MediatorDescendsLeft`, `MediatorDescendsRight` and their negations;
- end-to-end wrappers: `endToEnd_joint`, `endToEnd_full`, and the binary causal closure `endToEnd_full_with_causalSignature2`.

Scope note: `endToEnd_full` / `endToEnd_full_with_causalSignature2` are the “full story” wrappers that include marginal diagonal certification and constructive extraction of marginal separation; the joint-only invariant layer is isolated separately in `COFRS/Synthesis.lean` as `JointIrreducibleMediationProfile`.

## Diagonalization, factorization, and causal mediation

In this repository, diagonalization is used as a general adversarial pattern: for any candidate rule claiming to close a decision at the level of a given observable interface, a counter-construction produces a point, typically a fiber point, where that rule fails. Concretely, the critical interface is a projection `obs : S → V`. The diagonal pattern produces a situation in which the same visible value supports multiple internal states that cannot simultaneously satisfy the targeted dynamic truth.

The mathematical reading of the repository is organized by three statements, each made explicit in Lean.

### 1. Destruction of the static regime

If there exist `x ≠ x'` with `obs x = obs x'` while the relevant future property distinguishes them, formalized by compatibility along a chosen step, then no `obs`-only rule in the sense of `ObsPredictsStep` can be correct on both. Operationally, this is exactly the content of `LagEvent → ¬ ObsPredictsStep`.

This is the precise sense in which diagonalization destroys the static regime of closed global decisions.

### 2. Forced factorization through a mediator

To go beyond this obstruction, any correct policy must depend on information not contained in `obs` at the critical stage. At the level of interpretation, this extra information is carried by an internal state `z`, understood as cue, memory, or latent state, that summarizes the relevant hidden differentiation. In this reading, the decision factorizes through a mediator of the form

`history → z → decision`

rather than

`obs → decision`.

In the formal development, this is captured by `CompatDimLe`, `CompatDimEq`, and `RefiningLiftData`: compatibility on the observable fiber factors through a finite supplement `Fin n`, with exactness and minimality when `CompatDimEq n` is available.

### 3. Causality as a testable signature

The factorization is not treated as a metaphor. If success genuinely depends on the mediator, then two intervention principles must hold: ablating the mediator must destroy correctness, and permuting the mediator between examples must make the decision follow the mediator. This is the experimental form of the claim that the mediator is load-bearing, and it prevents confusion between genuine mediation and shortcut behavior.

In the code, this is packaged as `CausalSignature2`.

## Core idea in one paragraph

The development models histories as a minimal two-dimensional combinatorial structure of prefixes, paths, and admissible commutations, and interprets paths by a relational semantics on a state space `S`. An observable `obs : S → V` induces fibers of microstates that are indistinguishable at a given prefix. A `LagEvent` witnesses that two distinct microstates in the same fiber are holonomy-related now but diverge on future compatibility along a chosen step. This is enough to forbid any `obs`-only predictor. The decisive move is then to quantify the extra information required to recover predictability by a finite mediator `Fin n`, via `CompatDim` and `RefiningLift`, and to turn that forced mediation into a testable intervention signature, via permutation and ablation, on the mediator itself.

## 1. Formal framework

### 1.1 Histories as a minimal 2-structure

A history world is given by `HistoryGraph`:

- objects `P`, interpreted as prefixes;
- 1-morphisms `Path : P → P → Type`, interpreted as schedules or paths;
- 2-morphisms `Deformation`, witnessing admissible commutations;
- identity and composition of paths.

This is a minimal interface tailored to the development. It is not a full category-theoretic formalization.

### 1.2 Relational semantics

A `Semantics P S` assigns to each path a binary relation on states:

- `sem : Path h k → (S → S → Prop)`,
- together with compatibility with identity and composition as relational equalities.

The use of relations rather than functions is essential: it supports nondeterminism and partial information directly.

### 1.3 Observation, fibers, transport, holonomy

Given an observation map `obs : S → V` and a target observation `target_obs : P → V`, the observable fiber above `h` is

`FiberPt obs target_obs h := { x : S // obs x = target_obs h }`.

Transport along a path is the semantics restricted to fibers. Holonomy is defined from a deformation witness by composing transport along one path with the converse transport along the other.

This framework is developed in `COFRS/Foundations.lean`.

## 2. Dynamics: compatibility, lag, and no-go for `obs`-only prediction

### 2.1 Compatibility as the dynamic truth

For a future step `step : Path h k` and a microstate `x` in the fiber at `h`,

`Compatible sem obs target_obs step x`

means that there exists a fiber point at `k` reachable from `x` along `step`.

Compatibility is deliberately local: it is defined per microstate on a given observable fiber.

### 2.2 `LagEvent` as obstruction witness

A `LagEvent` packages the obstruction that drives the theory:

- two distinct microstates `x ≠ x'` in the same fiber at `h`;
- related by holonomy at the present stage;
- but differing in future compatibility along a chosen step.

Equivalently, the same visible value supports multiple internal states with incompatible futures. From a `LagEvent`, the development derives `StepSeparatesFiber`.

### 2.3 No visible predictor and no `obs`-only predictor

Two notions of prediction are defined for a fixed future step:

- `VisiblePredictsStep`: there exists a summary `σ` factoring through `obs` that predicts compatibility;
- `ObsPredictsStep`: the special case in which the predictor is directly a predicate on `V`.

The main no-go chain is:

- `LagEvent → ¬ VisiblePredictsStep`,
- `LagEvent → ¬ ObsPredictsStep`.

The corresponding results are proved in `COFRS/Dynamics.lean`, notably `not_visiblePredictsStep_of_lagEvent` and `not_obsPredictsStep_of_lagEvent`.

The point is exact: any rule depending only on the observable interface is constant on the fiber, and therefore cannot decide a property that varies inside a single fiber.

## 3. Forced factorization through a finite mediator

The development does not stop at impossibility. It quantifies the hidden information required to recover correct decision.

### 3.1 Compatibility dimension

`CompatDimLe sem obs target_obs step n` asserts that there exist:

- a finite index `σ : fiber(h) → Fin n`,
- a predicate on `Fin n`,

such that `Compatible ... step x` depends only on `σ x`.

This is an internal notion: it does not require factoring through `obs`. It measures the finite amount of hidden information needed to decide compatibility correctly.

`CompatDimEq` and `CompatDimEqTwo` package exactness and minimality.

### 3.2 Canonical mediation witness

A `RefiningLiftData` is an explicit witness on the observable fiber:

- `extObs : fiber(h) → V × Fin n`,
- whose first component refines the visible observation,
- and whose `Fin n` component carries exactly the information through which compatibility factors.

The central theorem is the equivalence

`CompatDimLe … n ↔ RefiningLift … n`.

This is the repository’s formal realization of factorization through a mediator: the mediator is finite, and the refined interface preserves the original visible interface.

These constructions are developed in `COFRS/Dynamics.lean`.

## 4. Regulation and obstruction

`COFRS/RegulationAndReduction.lean` develops a parallel layer expressing repairability and obstruction through gauges.

A gauge is a fiber-preserving correction applied at transport targets.

- `CorrectedTransport` applies transport followed by a gauge;
- `CorrectedHolonomy` is holonomy computed from corrected transports.

Two global notions are then defined on sets of cells:

- `AutoRegulatedWrt OK J`: there exists an admissible gauge making corrected holonomy diagonal on `J`;
- `ObstructionWrt OK J`: every admissible gauge fails, witnessed by twisted corrected holonomy.

This layer expresses repairability versus obstruction in the same fiber and holonomy language as the main development.

## 5. Causality as an intervention-testable signature

In the repository, mediation is not left at the level of factorization. In the binary case, it is given an intervention-testable causal form.

`COFRS/Examples/DiagonalizationMediationCausalityThesis.lean` defines `CausalSignature2`, which packages two intervention principles:

- **Permutation:** exchanging the two `Fin 2` classes changes the induced readout on a fiber point;
- **Ablation:** collapsing the mediator to a constant readout cannot preserve correctness when the step separates the fiber.

The key theorem is:

`StepSeparatesFiber … step → RefiningLift … step 2 → CausalSignature2 … step`

formalized as `causalSignature2_of_stepSeparatesFiber_of_refiningLift2`.

The conceptual conclusion is sharp: once a dynamically separating step forces mediation through a finite binary supplement, causality appears as the testable signature of that forced factorization.

## 6. Concrete instances and structural files

### 6.1 `GodelByCode`

`COFRS/Examples/GodelByCode.lean` provides a concrete diagonal instance internal to the framework.

It builds:

- a minimal `HistoryGraph` on `Nat` with one non-trivial deformation, written `p ⇒ q`;
- a relational semantics on `LagState Nat Bool`;
- two explicit diagonal fiber points with the same visible value and different hidden bit.

It then proves:

- `lagEvent_at_diag`,
- `diag_compatDimLe_two_step`,
- `diag_compatDimEqTwo_step`.

This instance is used by the thesis spine to derive `diagonalization_yields_causalSignature2`.

The point is not classical Gödel logic as an external excursus. The point is to realize, inside the holonomy and fiber semantics of the repository itself, a diagonal mechanism that forces:

- failure of any `obs`-only decision regime;
- a minimal finite mediator of size `2`;
- and therefore the binary causal signature.

### 6.2 `DynamicCompatDimN`

`COFRS/Examples/DynamicCompatDimN.lean` develops a parametric family in arbitrary finite dimension. It shows how compatibility dimension behaves uniformly in `n`, and supplies the scalable counterpart to the binary diagonal instance.

### 6.3 `Synthesis`

`COFRS/Synthesis.lean` packages the main results into synthetic profiles, making the core theorem chain easier to reuse and read at a higher level.

### 6.4 `FinCompression`

`COFRS/Combinatorics/FinCompression.lean` provides constructive combinatorial tools on finite types that support the finite-mediator layer of the development.

### 6.5 Geometry versus dynamics

`COFRS/Examples/GeometryDynamicsIndependence.lean` proves that:

- geometric coherence, understood as the existence of non-trivial holonomy structure;
- dynamic truth, understood as visible predictability of compatibility,

are logically independent in this framework.

This isolates an important consequence: geometric alignment does not imply dynamic correctness, and dynamic correctness can occur without non-trivial holonomy.

## 7. Reading guide

A good order of reading is:

1. `COFRS/Foundations.lean` — framework: fibers, transport, holonomy
2. `COFRS/Dynamics.lean` — lag/no-go, compatibility dimension, refining lift
3. `COFRS/RegulationAndReduction.lean` — gauges, regulation, obstruction
4. `COFRS/Synthesis.lean` — synthetic profiles of the main chain
5. `COFRS/Examples/DynamicCompatDimN.lean` — parametric finite-mediator family
6. `COFRS/Examples/DiagonalizationMediationCausalityThesis.lean` — causal signature
7. `COFRS/Examples/GodelByCode.lean` — diagonal instance
8. `COFRS/Examples/GeometryDynamicsIndependence.lean` — independence

This order moves from framework, to dynamic obstruction, to finite mediation, to causal packaging, and finally to concrete instances and independence results.

## 8. Constructivity and axiom audit

The repository is designed to remain constructive:

- no `axiom`,
- no `Classical` or `open Classical`,
- no `propext`,
- no `Quot.sound`.

Relevant `.lean` files end with an `AXIOM_AUDIT` block using `#print axioms ...`.

## Collaboration note

This project was written mainly in collaboration with **ChatGPT Codex** (OpenAI).
