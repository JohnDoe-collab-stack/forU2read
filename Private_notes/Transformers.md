# Transformers in the COFRS sense: three system classes (A/B/C) and the rupture they separate

This note is for readers who already know Transformers, but who want a precise, professional statement of what COFRS adds *as a class of systems*, not as a superficial architectural tweak.

COFRS is built around a checkable spine:

`diagonal obstruction` → `no interface-only closure` → `minimal finite mediator` → `intervention audit`.

The clean way to present the rupture is to state **three classes** and then show where the repository closes the separation.

## 0) Minimal setup (what the class labels talk about)

COFRS talks about *decisions at an interface*.

- State space: `S`.
- Observable interface: `obs : S → V`.
- A local dynamic truth to decide, for a chosen `step`, written in the repo as:
  `Compatible sem obs target_obs step x`.

“Interface-only” is not a probabilistic claim. It is a closure claim: *does the interface value `V` determine the correct decision?*

In Lean, that closure regime is captured by `ObsPredictsStep`.

## 1) The three classes (what distinguishes systems, not architectures)

### Class A — visible-only closure (the historical regime)

Definition (operational):

> A system is in Class A (for a chosen interface `obs`) if its decision depends only on the interface value `V` at the decision time, i.e. it is an `obs`-only predictor in the precise sense captured by `ObsPredictsStep`.

Consequence (hard, structural):

> If the dynamic truth varies inside a single `obs`-fiber, then no Class A system can be correct everywhere on that fiber.

In the repo this is exactly the content of:

- `LagEvent → ¬ ObsPredictsStep` in `COFRS/Dynamics.lean` (`PrimitiveHolonomy.not_obsPredictsStep_of_lagEvent`).

This is the “destruction of the static regime”: a global closed decision rule from `V` is impossible when the truth varies at fixed `V`.

Mapping to standard Transformers (why this is not an opinion):

- Standard autoregressive inference is a function from *visible context* (tokens; plus any provided visible retrieved text) to an output.
- Relative to the interface “what is provided to the model at decision time”, that is exactly a Class A regime: the decision is a function of `V`.
- Internal activations exist, but there is no separately specified mediator whose semantics/capacity/irreducibility are part of the contract.

So the statement is not “Transformers are weak”. The statement is:

> **standard inference is interface-only relative to its provided interface.**

### Class B — stateful systems (memory/latent), but not certified

Definition (operational):

> A system is in Class B if it carries internal state (memory, latent, cache, recurrent state, tool state), so it is not necessarily interface-only, but it is **not** accompanied by the COFRS invariants: minimal capacity, non-descend irreducibility, and intervention audit of load-bearing mediation.

Class B can succeed or fail; what matters is that its *success* is not characterized by the invariants that COFRS isolates.

This is why “Transformer + memory” does not automatically move you to the COFRS regime. It often moves you from A to B, but B is still missing the defining closure package.

### Class C — mediated, minimal, irreducible, auditable (the COFRS object)

Definition (operational):

> A system is in Class C if it closes a full package of invariants:
> 1) a certified obstruction against interface-only closure (a separating witness),
> 2) a quantified *minimal* finite mediator capacity (`Fin n` via compatibility dimension),
> 3) irreducibility of the mediator to each marginal interface (non-descend),
> 4) and (in the binary case) an intervention audit showing the decision follows the mediator (swap/ablation).

This is the rupture: Class C is not “a stronger model”. It is a **different contract**: the repair is measured, forced, and auditable.

## 2) Where the repo closes the class separation (Lean spine)

This section is what makes the A/B/C story professional: it points to explicit declarations.

### 2.1 Class A is killed by obstruction

In `COFRS/Dynamics.lean`:

- `PrimitiveHolonomy.not_obsPredictsStep_of_lagEvent` proves `LagEvent → ¬ ObsPredictsStep`.

This is the formal statement that an interface-only closure regime cannot survive a diagonal separation inside a fiber.

### 2.2 Minimal mediation is quantified and made canonical

In `COFRS/Dynamics.lean`:

- missing information is quantified by `CompatDimLe` / `CompatDimEq`,
- and realized canonically by `RefiningLiftData` / `RefiningLift`,
- with the central equivalence:
  `PrimitiveHolonomy.compatDimLe_iff_refiningLift` proving `CompatDimLe … n ↔ RefiningLift … n`.

This is not “add a latent”. It is “add exactly `Fin n` in a way that preserves the original interface and makes the decision factor through the supplement”.

### 2.3 Binary intervention audit (causal gates)

In `COFRS/Examples/DiagonalizationMediationCausalityThesis.lean`:

- `CausalSignature2` packages the swap/ablation audit,
- and `causalSignature2_of_stepSeparatesFiber_of_refiningLift2` proves that separation + a `2`-lift entails this audit.

This is the point where “mediation” becomes operationally testable, not just a factorization claim.

### 2.4 Two interfaces: “two insufficiencies → irreducible relation” in the strong sense

The Class C story is strongest when you have **two marginal interfaces** `A : S → VA` and `B : S → VB` and you are isolating a third term that is irreducible to each margin.

This is exactly the kind of spine that lives in:

- `COFRS/Examples/IndependenceRelationMediationChain.lean`

where the joint truth is fixed on a joint interface and then:

- each marginal interface is proved insufficient (no closure),
- a minimal joint mediator is produced (capacity),
- and irreducibility is strengthened by **non-descend** statements about the mediator (not only “the truth is not predictable from a margin”).

This is the precise formalization of “the relation becomes a third term”.

## 3) Empirical mapping (protocols as witnesses of Class C)

The empirical side is not “another definition”; it is an operational witness that your solver training actually instantiates the same contract.

Very compact mapping (as used in the repo’s experimental suite):

- v7/v8: barrier-style obstructions + stateful solvers + intervention hooks (these witness the obstruction layer and parts of the audit, but do not yet close the full min-lift contract in `n`).
- vN3b/v9: explicit finite mediator `z` with min-lift structure (`z = n` succeeds, `z < n` fails) plus swap/ablation gates.
- v10 Phase A1: scaling the same closure package across `n` (Phase A1 is exactly the “stability in `n`” closure).

This is what separates Class B from Class C empirically: **min-lift + gates + stability as `n` varies**.

## 4) In scope: closure failure vs repairable mediation failure

Within this repository’s scope, the failure mode of interest is:

- a system outputs a decision from an interface,
- but the target dynamic truth is not closed by that interface,
- so there exist states in the same fiber where any interface-only rule must fail.

COFRS’s remedy in scope is not “bigger model”. It is:

1) certify non-closure (obstruction witness),
2) quantify missing information (minimal `Fin n`),
3) enforce a mediator that carries it (refining lift),
4) audit that the decision follows the mediator (swap/ablation in the binary case).

This is a claim about a concrete closure class: it is identified, quantified, and repairable by a forced mediator with auditable dependence.

## 5) Professional bottom line (the rupture statement, precisely)

The rupture is not “attention vs GRU”, and it is not “we added memory”.

The rupture is that Class C systems are defined and validated by a *closed package*:

- diagonal obstruction that kills interface-only closure,
- minimal finite mediation (`Fin n`) with exact capacity statements,
- irreducibility of that mediator to the marginal interfaces (non-descend),
- and an intervention audit (swap/ablation) that certifies the mediator is load-bearing.

That package is what the repository is designed to make checkable, and it is what separates Class C from the historical visible-only regime (Class A) and from stateful-but-uncertified systems (Class B).
