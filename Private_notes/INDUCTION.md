# Induction in the COFRS sense

This document formalizes what "induction" means in this project.
It is not an induction on natural numbers by default.
It is a disciplined way to iterate referentials, where each step is forced by a diagonal obstruction and repaired by a mediator that becomes part of the next referential.

No implementation is assumed.
This is a design level and proof level specification.

## 0) Objects

Fix a state space `S`.

A referential `R` is a framing that fixes:
- a decision interface `obs_R : S -> V_R`
- a targeted dynamic truth `T_R : S -> Prop`
- the induced indiscernibility relation `~_R` given by `x ~_R x'` iff `obs_R x = obs_R x'`

In COFRS, the common targeted truth is step local:
`T_R(x) := Compatible sem obs_R target_obs step x`.
When needed, the targeted truth is family scoped, by fixing a family of admissible futures and targeting a signature over that family.

A mediator for `R` is an internal supplement `z : S -> W` such that the correct decision for `T_R` factorizes through `z` rather than through `obs_R` alone.
In the finite capacity contract, `W = Fin n`.

Non descent, as a strengthening, means that the mediator used to repair `R` cannot be reconstructed from `obs_R` alone on the domain relevant to `T_R`.

## 1) Subject and expressivity

Diagonalization and diagonal obstruction are not absolute properties of `S` alone.
They are properties of a referential.

In this document, a referential is called a subject when it is sufficiently expressive to make the following formulable within that framing:
- the indiscernibility classes induced by `obs_R`
- the targeted dynamic truth `T_R`
- the possibility of a diagonal separation of `T_R` at fixed `obs_R`

This is a prerequisite for the induction schema below.

## 2) Diagonal obstruction as an operator on a referential

Given a referential `R`, define the diagonal witness set:

`Diag(R) := { (x, x') in S × S | obs_R x = obs_R x' and T_R x != T_R x' }`.

Two cases:

- Closed case
  `Diag(R)` is empty.
  The targeted truth does not vary inside a visible class for `R`.
  In that sense, `R` closes for `T_R`.

- Obstructed case
  `Diag(R)` is non empty.
  Any rule that depends only on `obs_R` fails to decide `T_R` correctly everywhere on the relevant fiber.
  This is the diagonal destruction of visible only closure.

In the repository, this obstructed case is witnessed constructively by objects like `LagEvent` and expressed by separation notions like `StepSeparatesFiber` and no go notions like `ObsPredictsStep`.

## 3) Forced mediation as the repair of a diagonal obstruction

The forced mediation claim is the following contract:

If `Diag(R)` is non empty, then any correct decision procedure must factor through a supplement not contained in `obs_R` alone.

When finite exact mediation exists, the repair is quantified:
- there exists a finite mediator `z_R : S -> Fin n`
- `n` is minimal among finite mediators that repair the targeted decision

In the repository, this is the layer captured by `CompatDimLe`, `CompatDimEq`, and their canonical lift formulations.
In the global signature layer, this is expressed as finite compression of the canonical mediator signature.

## 4) The extension step

Define an extension operator that builds the next referential from a repaired one.

Given:
- a referential `R`
- a mediator `z_R : S -> W_R` that repairs `R` for `T_R`

Define a new interface:
`obs_{R+} : S -> (V_R × W_R)` by `obs_{R+}(x) := (obs_R(x), z_R(x))`.

Then define a next referential:
- `R+ := Extend(R, z_R, T_{R+})`

where `T_{R+}` is a new targeted dynamic truth on `S` selected at the next stage.
Typical choices include:
- a refined version of the same decision problem with stricter audit requirements
- a coupling truth about coherence between multiple views
- a new truth that becomes formulable only after the extension

The key point is not the particular choice of `T_{R+}`.
The key point is that the diagonal obstruction of `R` forces the existence of a mediator, and the induction step reuses that mediator as part of the next visible interface.

## 5) Referential induction as a construction schema

A referential induction is:
- an initial referential `R_0`
- for each stage `n`, either a closure result for `R_n`, or a diagonal witness and a repair mediator producing `R_{n+1}`

In other words:

At stage `n`:
- either `Diag(R_n)` is empty, and the chain stops for the targeted truth of that stage
- or `Diag(R_n)` is non empty, a mediator `z_n` is produced under the chosen mediation contract, and `R_{n+1} := Extend(R_n, z_n, T_{n+1})`

This is the sense in which the project uses the word induction:
an iterative sequence of forced extensions driven by diagonal obstructions.

## 6) Induction as a proof principle

In this project, induction is not "on natural numbers".
The diagonal step is not provided by an index.
It is provided by explicit witnesses inside each stage of the chain.

The strict proof principle that matches the procedure is:
induction on the derivation tree of a chain, where each constructor carries the data of the step:
- a closure certificate for the current stage, or
- a diagonal witness, a mediator satisfying the chosen contract, and the construction of the next stage

It is possible to number stages by `Nat` for bookkeeping, for example when recording a finite prefix of a chain.
This numbering does not create diagonalization, and it does not replace the need to carry the witnesses.
Any proof that forgets the witnesses and keeps only an index loses the procedure.

## 7) What is preserved across stages

What this induction is designed to preserve is not a global conservation law of information.
It preserves a verified chain of obligations.

At each stage, the intended preserved structure is:
- the referential is explicit, meaning `obs` and `T` are fixed and auditable
- diagonal obstruction is either closed or witnessed
- when obstructed, mediation is constructed under an explicit capacity contract
- minimality and non descent are tracked when they are part of the stage contract
- when the stage is binary, an interventional audit clause can be added as a check that the decision truly follows the mediator

## 8) Checklist to verify an actual chain

To verify that a concrete development follows this induction schema:

1. Stage definition
   Check that each stage fixes a referential, meaning an interface and a targeted dynamic truth.

2. Subject condition
   Check that the stage is sufficiently expressive to state its diagonal obstruction.

3. Obstruction or closure
   Check that the stage either proves closure, or exhibits a diagonal witness.

4. Forced mediation under contract
   Check that the stage constructs a mediator with the chosen capacity and the required properties.

5. Extension
   Check that the next stage extends the interface by the constructed mediator, or passes to a joint interface that contains it.

6. Re application
   Check that the next stage targets a truth that is explicitly fixed and actually uses the new referential.

## 9) Relation to the core repository objects

This document is design level, but it corresponds directly to the repository structure:
- diagonal obstruction and no go are formalized by `LagEvent`, `StepSeparatesFiber`, and `ObsPredictsStep`
- forced mediation and its minimality are formalized by `CompatDimLe`, `CompatDimEq`, and canonical lifts
- the canonical mediator principle is expressed by the signature object `Sig`
- global finite compressions are expressed by `CompatSigDimLe` and `CompatSigDimEq`
- joint irreducibility and non descent are packaged by the end to end joint chain

The term induction refers to iterating this package, stage by stage, by extending the visible interface with the forced mediator and moving to the next targeted truth.
