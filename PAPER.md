# Canonical Mediator Compression and Irreducible Joint Mediation

This document is a paper-style explanation of the repository’s mathematical core, written to be readable before reading any Lean code.

The development is constructive throughout (no `Classical`, no axioms), with `AXIOM_AUDIT` blocks in key `.lean` files.

## Abstract

We develop a constructive, mechanized theory of dynamic decision problems in which a given observable interface is insufficient to decide a truth determined by future compatibility along admissible continuations. The central object is a canonical future mediator: the full future-compatibility signature `Sig`, which assigns to each admissible future whether a micro-state remains compatible with it. We prove a universal respect property: any summary that correctly decides future compatibility must respect `Sig`; in particular, it cannot identify micro-states with different future signatures. When exact finite mediation exists, it is not an ad hoc latent: it is an exact finite compression of `Sig`. We formalize global compressibility and capacity-minimality via global signature dimension (`CompatSigDimLe/Eq`) and relate it to step-local prediction and canonical fiber lifts. In the two-interface setting, we isolate irreducible joint mediation: the information required for correctness can be genuinely relational and fail to descend to either marginal interface. In the binary case, forced mediation yields an intervention-auditable signature (swap/ablation). All results are mechanized in Lean without classical axioms.

## One-sentence claim

The discovery is the canonical future mediator `Sig` together with its universal respect property: exact finite mediators are capacity-minimal finite compressions of `Sig`, and in the two-interface setting the resulting joint mediation can be irreducible to either marginal interface, with a binary intervention-auditable signature when the forced mediator has size `2`.

## Introduction

Many modern systems are evaluated under a visible-only closure contract: correctness is treated as a function of what is visibly provided at decision time (tokens, pixels, or other interface-level observations). This contract can fail for genuinely dynamic truths: the truth to be decided may depend on whether a micro-state remains compatible with admissible futures, and that dependence can vary inside a single observable fiber. The question is then not merely whether prediction fails, but what it means, structurally and quantitatively, for prediction to be repaired.

This work isolates a canonical object that makes missing information explicit. For a micro-state on a fiber, the canonical future mediator `Sig` records, for every admissible future, whether the micro-state remains compatible with that future. This object is canonical in a strong sense: any summary that correctly decides future compatibility must respect `Sig`, and therefore must separate any pair of micro-states with different future signatures. Missing information is therefore not treated as an architectural intuition but as an explicit mathematical object.

From this canonical core, the framework develops two further layers. First, when a finite mediator exists, it is not arbitrary: it is an exact finite compression of `Sig`. The repository defines global signature compressibility (`CompatSigDimLe`) and exact minimality (`CompatSigDimEq`), and relates these notions to step-local prediction and canonical lifting on fibers. Second, in the two-interface setting, the framework isolates irreducible joint mediation: although both marginals may be individually insufficient, the joint mediator may fail to descend to either margin, showing that correctness-relevant information is genuinely relational. In the binary case, forced mediation yields an intervention-auditable signature (swap/ablation), providing a precise bridge from structural necessity to testable mediated dependence rather than a slogan.

## Problem setup (dynamic truth and interfaces)

- States: `S`.
- Prefixes (histories): `P`, with a `HistoryGraph` structure.
- Semantics: `sem : Path h k → (S → S → Prop)` (relations, not functions).
- Observable interface: `obs : S → V`, with a per-prefix target observation `target_obs : P → V`.
- Fiber at `h`: `FiberPt obs target_obs h`.

For a fixed future step `step : Path h k`, the step-local dynamic truth is compatibility:

- `Compatible sem obs target_obs step x`

Intuitively: from micro-state `x` on the fiber at `h`, there exists an admissible continuation along `step` reaching some fiber point at `k`.

## Visible-only closure and diagonal obstruction

The visible-only closure regime is formalized by `ObsPredictsStep`:

- `ObsPredictsStep sem obs target_obs step` means there exists a decision rule depending only on the visible interface value (`V`) that decides `Compatible … step x` correctly for all fiber points at `h`.

Diagonal obstruction is packaged by `LagEvent`. Operationally, it exhibits a pair of micro-states in the same observable fiber that disagree on the step-local truth. From this, the development derives:

- `LagEvent → ¬ ObsPredictsStep`

This is the destruction of the visible-only closure regime: any interface-only rule is constant on a fiber and therefore cannot decide a truth that varies inside that fiber.

## The canonical future mediator: `Sig`

At a fixed prefix `h`, the repository packages the full set of future-compatibility truths into a single canonical object:

- `Future h` is the type of admissible futures starting at `h`.
- `Sig x : Future h → Prop` maps each admissible future to the truth value of compatibility from `x` along that future.

The canonical point is the universal respect property:

- any summary that is correct for future compatibility must respect `Sig`;
- equivalently, it cannot identify micro-states with different `Sig`.

This turns missing information into a canonical mathematical object rather than an architectural guess.

## Exact finite mediation as compression (global and local)

The repository separates two levels of finiteness.

### Global: compressing the canonical mediator

Global signature compression is expressed by `CompatSigDimLe` and `CompatSigDimEq`:

- `CompatSigDimLe … n` means there exists a finite summary `σ : fiber → Fin n` that can correctly decide compatibility for every admissible future (equivalently, `σ` respects `Sig`).
- `CompatSigDimEq … n` adds capacity-minimality: no strictly smaller `m < n` can do the same.

In this sense, an exact finite mediator is a finite compression of `Sig`.

### Local: step-specific shadows and canonical lifts

Step-local compatibility dimension and canonical lifts are expressed by `CompatDimLe/Eq` and `RefiningLift`:

- `CompatDimLe … step n` is step-local finite predictability for a fixed `step`.
- `CompatDimEq … step n` adds step-local minimality.
- `RefiningLift … step n` provides a canonical finite lift on the fiber for that fixed `step`.

The repository relates global and local levels: a global compression of `Sig` yields step-local finite predictability and a step-local lift for any chosen `step`.

## Two interfaces and irreducible joint mediation (non-descent)

Now consider two marginal interfaces:

- `A : S → VA`
- `B : S → VB`

and the joint interface:

- `AB : S → VA × VB`

There are three distinct claims one can make, and the repository separates them:

1. Marginal no-go: `A` alone cannot close the step-local truth, and `B` alone cannot close it.
2. Joint repairability: on the joint interface `AB`, there exists a finite mediator that repairs correctness.
3. Irreducibility (non-descent): even though the repair exists jointly, the joint mediator does not descend to either marginal interface.

Non-descent is the strong structural claim: the information needed for correctness can live in an irreducible relation rather than in either margin alone.

## Binary intervention-auditable signature (swap/ablation)

In the binary case (`n = 2`), the repository packages a specific intervention-auditable signature (`CausalSignature2`):

- Ablation: collapsing the mediator breaks correctness when the step separates the fiber.
- Swap: swapping the two mediator classes makes decisions follow the mediator (and not remain fixed to the original input).

This makes mediated dependence checkable by interventions in the binary forced-mediation setting.

## Where to find the results (Lean map)

The core results are organized into three files:

- `COFRS/Dynamics.lean`
  - Defines `Future`, `Sig`, `SigFactorsThrough`, `CompatSigDimLe/Eq`.
  - Relates global signature compression to step-local notions (`CompatDim*`, `RefiningLift`).
  - Contains the main visible-only no-go layer (`LagEvent`, `ObsPredictsStep`, separation).

- `COFRS/Examples/GodelByCode.lean`
  - A concrete diagonal instance internal to the framework.
  - Exhibits a binary exact compression of the canonical mediator on the diagonal fiber (a hidden bit realizes the canonical partition).

- `COFRS/Examples/IndependenceRelationMediationChain.lean`
  - Two-interface spine: marginal no-go, joint repair, and non-descent.
  - Includes a canonical-mediator layer that rules out marginal reconstructions at the level of `Sig` (not only step-local prediction).

For the binary intervention-auditable layer:

- `COFRS/Examples/DiagonalizationMediationCausalityThesis.lean`

For the finitary “correlation regime” appendix (explicit mistakes and positive error counts on finite fibers):

- `COFRS/Examples/CorrelationRegimeAppendix.lean`

## Constructivity and audit discipline

All `.lean` files in this repository are intended to remain constructive. Key files end with an `AXIOM_AUDIT` block using `#print axioms` to ensure:

- no axioms are introduced,
- no classical dependencies are required,
- and forbidden principles do not appear.

## Collaboration note

This project was written mainly in collaboration with ChatGPT Codex (OpenAI).
