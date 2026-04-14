# COFRS unified statement (formal spine + empirical analogue)

This repository contains:

- a constructive Lean development (`COFRS/`) formalizing the spine:
  diagonal obstruction → no obs-only decision → finite mediator (compatibility dimension / lift) → intervention signature;
- an empirical suite (`Empirical/aslmt/`) implementing protocol-grade witnesses that mirror the same structure.

## Formal spine (Lean)

At a high level (see `PROJECT.md` and the referenced Lean files):

- `LagEvent` witnesses intra-fiber separation for a decision-time observable.
- This yields `¬ ObsPredictsStep` (no obs-only closure).
- Recovering correctness factors through a finite supplement (`Fin n`) captured by `CompatDim*` and `RefiningLift*`.
- For the binary case, forced mediation yields an intervention-style signature (`CausalSignature2`).

## Empirical analogue (ASLMT)

The empirical witnesses mirror the same three ingredients:

1. **Fiber barrier at decision time**: paired contexts with identical decision-time observation but different hidden truth.
2. **Mediator-based recovery**: models that must route the missing information through an internal state/latent.
3. **Intervention audits**: ablation and swap/permutation checks that the mediator is load-bearing.

The v7 “pair-grade OOD-required” witness is the cleanest protocol-grade instantiation in this repo:
`Empirical/aslmt/v7_descriptive/`.

This note is a *routing document*: it does not add claims beyond what is mechanically audited by the Lean theorems and by the empirical verifiers.
