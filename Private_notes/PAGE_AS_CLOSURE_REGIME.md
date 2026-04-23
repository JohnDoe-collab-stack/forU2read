# Page as a closure regime (interface relative truth)

This note reformulates the Page viewpoint in the language of interface relative closure.
It avoids "computation" framing and focuses on what is decidable from a given interface.

## 0) Lean map (where this structure already lives)

The structural content of this note is already encoded in Lean in two layers:

Canonical mediator and closure layer:
- `CompatibleFuture`, `Sig`, `SigFactorsThrough` live in `/mnt/c/Users/frederick/Documents/forU2read/COFRS/Dynamics.lean:72`
- global signature compression is `CompatSigDimLe` and `CompatSigDimEq` in `/mnt/c/Users/frederick/Documents/forU2read/COFRS/Dynamics.lean:157`
- step separation (a diagonal witness for a single future step) is `StepSeparatesFiber` in `/mnt/c/Users/frederick/Documents/forU2read/COFRS/Dynamics.lean:340`

Abstract quotient and induction layer:
- a generic interface and truth target are a `ReferentialProblem` in `/mnt/c/Users/frederick/Documents/forU2read/COFRS/Examples/ReferentialInduction.lean:46`
- closure is `ReferentialProblem.Closes` in `/mnt/c/Users/frederick/Documents/forU2read/COFRS/Examples/ReferentialInduction.lean:54`
- a diagonal witness is `ReferentialProblem.DiagonalWitness` in `/mnt/c/Users/frederick/Documents/forU2read/COFRS/Examples/ReferentialInduction.lean:57`
- a forced finite mediation step is `InductionStep` in `/mnt/c/Users/frederick/Documents/forU2read/COFRS/Examples/ReferentialInduction.lean:143`
- re targetable chains are `StageTransition` and `ReferentialDerivation` in `/mnt/c/Users/frederick/Documents/forU2read/COFRS/Examples/ReferentialInduction.lean:241`
- disciplined re targeting is `DisciplinedStageTransition` and `DisciplinedReferentialDerivation` in `/mnt/c/Users/frederick/Documents/forU2read/COFRS/Examples/ReferentialInduction.lean:285`

This note is therefore not adding new primitives. It is a semantic reading of the above Lean structure in the Page setting.

## 1) Referential setup: micro states, interface, truth

Fix a global system with a decomposition into two subsystems:
- `R`: the accessible subsystem (for example, the radiation collected so far)
- `B`: the remainder (for example, the black hole interior plus whatever is not in `R`)

Micro state space:
- micro states are global pure states `psi` on `R x B`

Interface (what is visible):
- the interface observation is the reduced state on `R`
- define `obs(psi) = rho_R(psi)` where `rho_R(psi)` is the partial trace over `B`

Truth target:
- a truth target is a predicate `T(psi)` that is not assumed to be "full state identification"
- `T` can be any decision problem, for example a single bit of information about correlations

Closure on the interface:
- `T` is closed on `obs` if `T` factors through `rho_R`
- equivalently: whenever `rho_R(psi1) = rho_R(psi2)`, we must have `T(psi1) = T(psi2)`

In this form, "visible only suffices" means exactly: `T` is closed on the interface.

## 2) Diagonal witness: why closure can fail on reduced data

Key structural fact (purification non uniqueness):
- fixing a reduced state `rho_R` does not fix a unique global pure state
- there are many `psi` with the same `rho_R`

Therefore, for many truth targets `T`, closure fails:
- there exist `psi1, psi2` with `rho_R(psi1) = rho_R(psi2)` but `T(psi1) != T(psi2)`

This is a diagonal witness in the strict sense:
- it exhibits a separation of `T` inside an `obs` fiber
- it implies that no rule that reads only `rho_R` can be correct for `T` on that fiber

This is the non closure regime in its cleanest form.

Lean reading:
- "closure on an interface" is exactly `ReferentialProblem.Closes` when `q` is the interface observation.
- "diagonal witness" is exactly `ReferentialProblem.DiagonalWitness`.
- in the dynamics instantiation, "diagonal witness for a step local truth" is `StepSeparatesFiber` for `Compatible sem obs target_obs step`.

## 3) What the Page viewpoint adds: a typicality regime, not a new definition

The diagonal witness above is purely structural and does not use probability.

The Page theorem adds a typicality statement:
- for a random global pure state, if `R` is not larger than `B`, then `rho_R` is typically close to maximally mixed
- equivalently: the accessible subsystem typically looks "featureless" even when the global state is pure

In closure language:
- before the accessible interface is large enough, many truth targets that depend on global correlations are generically not closed on `rho_R`
- the interface does not carry enough structure to decide them

This is not a claim that "nothing is computable".
It is a claim about which truths are closed on a given interface.

## 4) Page time as an interface transition

In an evaporating black hole story, the accessible subsystem `R` grows with time.

The Page time corresponds to a regime change in the size relation between `R` and `B`:
- early: `R` is smaller than `B`
- late: `R` becomes comparable to or larger than `B`

In closure terms:
- early regime: many correlation dependent truths are not closed on `rho_R`
- late regime: for suitable truth targets, closure on the radiation interface can become possible

So the Page curve is naturally read as an interface relative closure transition, under a unitarity assumption.

## 5) Why this is directly connected to a solver architecture

Once closure fails on the current interface, a correct solver cannot be visible only relative to that interface.

There are only two structural ways out:

1) Mediation without changing the interface
- the solver carries a mediator that refines what the interface identifies
- in finite settings, this corresponds to a finite compression that is sufficient to decide `T`

2) Extension of the interface
- the solver changes what becomes visible by acquiring additional data
- physically: collect more of `R`, or join additional subsystems, or perform an interaction that produces new accessible records
- architecturally: a query loop where an internal state chooses an action that conditions the response stream, then decides after update

In both cases, the diagonal witness is not only a no go:
- it is an operational signal that the present interface is insufficient for the present truth target
- it forces either a mediator or an interface extension

Lean reading:
- the canonical mediator that must be respected is `Sig` in `/mnt/c/Users/frederick/Documents/forU2read/COFRS/Dynamics.lean:77`.
- "respect of Sig" is `SigFactorsThrough` in `/mnt/c/Users/frederick/Documents/forU2read/COFRS/Dynamics.lean:133`.
- finite exact compression at the global layer is `CompatSigDimLe` and `CompatSigDimEq`.
- the abstract forced step that packages "diagonal witness plus finite mediator" is `InductionStep` in `ReferentialInduction.lean`.
- if you want a stage by stage notion that is not mere indexing, the core object is `DisciplinedReferentialDerivation`, which forces re targeting to use the extension via `UsesExtension`.

## 6) Induction viewpoint (stage by stage, interface by interface)

Given a current stage specified by `(obs, T)`:
- if `T` is closed on `obs`, the stage stops
- if not, a diagonal witness exists, and the stage must be repaired by mediation or interface extension
- the next stage can then retarget a new truth target on the extended interface

This makes Page like transitions a special case of a general closure driven progression:
- not an iteration by index
- an iteration forced by non closure witnesses and repaired by controlled extensions
