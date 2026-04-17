# COFRS / compat_obstructions (Lean 4)

A **constructive**, axiom-audited Lean formalization of a “Primitive Holonomy / COFRS” framework connecting:

> Diagonalization destroys the static regime of closed global decisions, forces their factorization through a mediator, and makes causality the testable signature of that forced factorization.

This repository is intended to stay **axiom-free** and **non-classical**.

## What this formalizes (high level)

### 1) Static regime is destroyed (no closed obs-only decisions)

A `LagEvent` yields a separation inside a single observable fiber, hence forbids even the strongest obs-only decision interface:

- `LagEvent … → ¬ ObsPredictsStep …` (`COFRS/Dynamics.lean`, theorem `not_obsPredictsStep_of_lagEvent`)
- and therefore `¬ VisiblePredictsStep …` as well.

### 2) Forced factorization through a finite mediator

The project introduces an _internal_ (not necessarily visible) finite mediation measure:

- `CompatDimLe … step n` : compatibility along `step` is decidable from a finite index `Fin n` on the observable fiber.

This is made canonical via an explicit “refining lift” living **on the observable fiber**:

- `CompatDimLe … n ↔ RefiningLift … n` (`COFRS/Dynamics.lean`, theorem `compatDimLe_iff_refiningLift`)
- the witness is `RefiningLiftData` with an `extObs : fiber(h) → V × Fin n` such that compatibility factors through the `Fin n` component.

### 3) Causality becomes a testable signature

When separation forces mediation (notably `Fin 2` in the diagonal instance), the project derives an intervention-style signature:

- `CausalSignature2` packages “permutation changes readout” and “ablation breaks correctness” on the fiber.
- `StepSeparatesFiber + RefiningLift 2 → CausalSignature2` (`COFRS/Examples/DiagonalizationMediationCausalityThesis.lean`, theorem `causalSignature2_of_stepSeparatesFiber_of_refiningLift2`).

## Key instance: diagonalization by code

`COFRS/Examples/GodelByCode.lean` provides a concrete, constructive diagonal instance inside the COFRS framework:

- `lagEvent_at_diag` : a diagonal `LagEvent` witness.
- `diag_compatDimLe_two_step` and `diag_compatDimEqTwo_step` : internal dimension is (at most / exactly) `2`.

This feeds the “thesis spine”:

- `diagonalization_yields_causalSignature2` (`COFRS/Examples/DiagonalizationMediationCausalityThesis.lean`).

## Independence result

`COFRS/Examples/GeometryDynamicsIndependence.lean` isolates that geometric coherence (holonomy/commutation-style alignment) and dynamic truth (visible predictability of future compatibility) are logically independent in this framework.

## Code organization

- Entry points: `COFRS.lean`, `COFRS/Main.lean`
- Core framework:
  - `COFRS/Foundations.lean`
  - `COFRS/Dynamics.lean`
  - `COFRS/RegulationAndReduction.lean`
  - `COFRS/Synthesis.lean`
- Combinatorics:
  - `COFRS/Combinatorics/FinCompression.lean`
- Examples:
  - `COFRS/Examples/*.lean`

## Empirical status (Phase A1)

The empirical A1 milestone (“stability in `n` under a single unified witness with a strict verifier”) is closed on
`n ∈ {3,4,5,6}` with `seed=0..4` under `profile=solid` in:

- `Empirical/aslmt/v10_phaseA1_kdet_spaced2/README_aslmt_v10_phaseA1_unified_nscalable_kdet_spaced2.md`
- `Empirical/aslmt/runs/aslmt_v10_phaseA1_unified_nscalable_posloss_pairrank_kdet_spaced2_20260416_074821_9fcd16977fda/`

## Build

- Lean toolchain: see `lean-toolchain` (currently `leanprover/lean4:v4.30.0-rc1`).
- Dependencies: `lakefile.lean` pins `mathlib4`.

Typical commands:

- `lake build`
- `lake env lean COFRS.lean`

## Constructivity + axiom audit

Project rules:

- no `axiom`
- no `Classical` / `open Classical`
- no `propext`
- no `Quot.sound`

Each relevant `.lean` file ends with an `AXIOM_AUDIT` block (`#print axioms …`) intended to report **no axioms**.

## Collaboration note

This `Project` was written mainly in collaboration with **ChatGPT Codex** (OpenAI).
