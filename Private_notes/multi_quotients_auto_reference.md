# Multi quotients in one system

Purpose
Define, at the design level, how several quotients can coexist on one state space, each quotient being sufficiently expressive to support a diagonalization, and how diagonal witnesses produced relative to one quotient can be re used to test the others.

This file is definitions and contracts. No implementation assumptions.

## 0) Objects

- A state space `S`.
- An index set `I` of quotients.
- For each `i : I`, an interface `obs_i : S -> V_i`.
- For each `i : I`, a targeted dynamic truth `T_i : S -> Prop` to decide.
  In COFRS, a common instance is step local:
  `T_i(x) := Compatible sem obs_i target_obs step x`.
  When needed, the truth can be family scoped by fixing a family of admissible futures.

For any finite tuple `(i1, ..., ik)`, define a joint interface:
`obs_joint : S -> (V_i1 × ... × V_ik)` by `obs_joint x = (obs_i1 x, ..., obs_ik x)`.

## 1) Referential and subject

A referential is the framing that fixes:
- a decision interface `obs`
- a targeted dynamic truth `T`
- the induced indiscernibility classes, meaning the quotient by `obs`

In this file, a quotient is called a subject in the referential sense when it is sufficiently expressive to make the following formulable in that framing:
- what it means for two states to be visibly indiscernible
- the targeted dynamic truth
- the possibility of a diagonal separation of that truth at fixed visible class

This matches the intended point:
a diagonalization exists only relative to a quotient that is sufficiently expressive to support the statement it is trying to certify.

## 2) Quotient independence in one system

Two quotients `i` and `j` can be called independent when neither interface subsumes the other as a partition of `S`.
One minimal, non probabilistic way to state this is:

- there exist `x, x'` with `obs_i x != obs_i x'` but `obs_j x = obs_j x'`
- and there exist `y, y'` with `obs_j y != obs_j y'` but `obs_i y = obs_i y'`

This says that each quotient has discriminations that the other quotient cannot express.

## 3) Diagonal witness relative to one quotient

Fix a quotient `i` and its targeted truth `T_i`.

A diagonal witness for `i` is a pair of states in the same system:
there exist `x, x' : S` such that
- `obs_i x = obs_i x'`
- and `T_i(x) != T_i(x')`

This is the clean, object level statement of visible non closure relative to `obs_i`.

In COFRS, this is the content of intra fiber separation for the chosen interface, and it can be produced constructively from an obstruction witness (for example `LagEvent`).

## 4) How one diagonal witness is re used across quotients

Assume we have two quotients `i` and `j` in the same system, and a diagonal witness `(x, x')` for `i`, meaning:
- `obs_i x = obs_i x'`
- `T_i(x) != T_i(x')`

The same pair `(x, x')` can be evaluated against quotient `j` without any additional construction, by checking:
- whether it is intra fiber or inter fiber for `j`, meaning `obs_j x = obs_j x'` or `obs_j x != obs_j x'`
- whether it is separating for the truth targeted by `j`, meaning `T_j(x) != T_j(x')`

This yields a clean trichotomy:

- intra fiber for `j` and separating for `T_j`
  the same pair is a diagonal witness for `j`

- inter fiber for `j`
  the same pair is a visible distinction for `j`

- intra fiber for `j` and not separating for `T_j`
  the pair is not a diagonal witness for `j`, but it remains a concrete test case inside `S`

This is the precise sense in which diagonalizations relative to one quotient can impact the others in one shared system:
they produce concrete separating pairs in `S` that can be re used as diagnostics under other interfaces and other targeted truths.

## 5) Couplings and joint diagonalization

In a multi quotient design, one often targets truths about coherence between views.
Given quotients `i` and `j`, define a coupling truth `T_ij : S -> Prop` that depends on how the two views relate.

A joint diagonal witness for the coupling is a pair `x, x' : S` such that:
- `obs_joint x = obs_joint x'`
- and `T_ij(x) != T_ij(x')`

This captures the strong situation:
even after making both views jointly visible, the coupling truth can still vary inside one joint visible class.

This is the multi quotient analogue of joint non descent:
the missing structure is not contained in either marginal, and may not be contained in their joint visible interface either.

## 6) Local mediators, coupling mediators, and autoreflexive policies

For each quotient `i`, a local finite mediation contract is carried by a mediator `z_i : S -> Fin n_i` through which the decision for `T_i` factorizes.

For a coupling truth `T_ij`, there are two design outcomes:

- stacked mediation
  there exists a coupling mediator computed from the local mediators, `z_ij = g(z_i, z_j)`

- irreducible joint mediation
  any mediator that repairs `T_ij` fails to descend to either marginal interface, and cannot be computed as a function of `z_i` alone or `z_j` alone

When access is reconfigurable by queries or interventions, an autoreflexive policy can choose which quotient to query next, based on internal state, before producing the final decision.

## 7) Alignment with the COFRS theory objects

This file is design level, but its clauses map directly to the repository objects:

- visible only closure is `ObsPredictsStep` for `obs := obs_i`
- diagonal witness is intra fiber separation (`StepSeparatesFiber`) or a diagonal event (`LagEvent`)
- finite mediation capacity is `CompatDimLe` and its canonical lift form `RefiningLift`
- the canonical future mediator is the signature object `Sig`
- global compressions of the canonical mediator are `CompatSigDimLe` and `CompatSigDimEq`
- joint irreducibility is expressed by joint non descent conditions, and packaged in the end to end joint chain

The key structural point for multi quotient systems is:
diagonalization produces concrete separating pairs inside `S`, and those pairs can be evaluated against any other quotient or joint quotient in the same system.
