# Ordinals as bookkeeping (checklist)

This file is a strict checklist for using ordinals to index a COFRS style referential induction without changing its meaning.
The ordinal never generates diagonalization. It only indexes an already witnessed derivation.

See also: `Private_notes/INDUCTION.md` (Appendix A).

## 0) What an ordinal index is allowed to do

Allowed:
- provide stable names for stages
- allow transfinite staging when you explicitly construct successor and limit steps
- support addressing and referencing of previously constructed mediators and witnesses

Not allowed:
- replace witnesses by an index
- claim a successor step exists without carrying its diagonal obstruction and repair data
- claim a limit step exists without an explicit integration construction

## 1) Stage record (what each ordinal stage must carry)

For each index `alpha`, a stage must fix:
- a decision interface `obs_alpha`
- a targeted dynamic truth `T_alpha` (step local or family scoped)
- the relevant fiber (the indiscernibility classes induced by `obs_alpha`)

And it must carry one of:
- a closure certificate for `T_alpha` at fixed `obs_alpha`, or
- a diagonal obstruction witness plus a mediator satisfying the stage contract

If a stage does not explicitly carry this, the ordinal index is empty bookkeeping.

## 2) Successor stage validity (`beta + 1`)

A successor stage is valid only if the transition from `beta` to `beta + 1` carries:
1) obstruction at stage `beta`
   - an explicit diagonal witness or an equivalent object in the codebase
2) forced mediation at stage `beta`
   - a mediator satisfying the chosen contract (capacity, minimality if required, non descent if required)
3) extension construction
   - a new interface `obs_{beta+1}` that exposes the repaired mediator (or an explicitly defined joint interface that contains it)
4) a newly fixed truth `T_{beta+1}`
   - explicitly stated at the new stage, not implied by the index

If any of (1) to (4) is missing, then `beta + 1` is not a successor stage in the COFRS sense.

## 3) Limit stage validity (`lambda`)

A limit stage is valid only if you give an explicit construction that integrates a cofinal prefix.
Examples of acceptable constructions:
- expose a tuple of accumulated mediators in the interface
- expose a controlled joint interface, then fix a new truth that only becomes formulable in that joint view

Unacceptable by default:
- defining `obs_lambda` as a pointwise limit without specifying what is integrated and how it is made observable
- treating the limit index itself as an integration operator

The practical rule is simple:
no limit stage without an explicit interface level integration construction.

## 4) Failure modes to anticipate (operational)

1) Index without derivation
   - you can write down ordinal stages, but you cannot replay the chain because witnesses are missing

2) Local versus global confusion
   - step local mediation facts are used as if they implied global signature compression
   - fix by using explicit global objects when needed (canonical signature and its compression)

3) Ill formed coupling at limits
   - a joint stage is claimed, but the joint truth and its fiber are not fixed and audited

4) Silent contract drift
   - capacity, minimality, or non descent assumptions change across stages without being stated

## 5) Minimal correctness statement for an ordinal indexed chain

An ordinal indexed chain is acceptable in this project if and only if:
- every successor index corresponds to a witnessed obstruction plus a witnessed repair plus an explicit extension
- every limit index corresponds to an explicit integration construction
- the chain can be replayed as a derivation that does not use the ordinal index to create any step
