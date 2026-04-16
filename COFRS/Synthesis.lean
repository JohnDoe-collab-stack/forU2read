import COFRS.RegulationAndReduction
import COFRS.Dynamics

/-!
# Primitive Holonomy (curated): minimal synthesis wrappers

This module defines small “paper-friendly” predicates (no new structure) that bundle the
load-bearing qualitative properties used across examples.
-/

universe u v w uQ

namespace PrimitiveHolonomy

section WithHistoryGraph

variable {P : Type u} [HistoryGraph P]

/--
A compact qualitative profile for a dynamic diagonal cell:

- twisted holonomy on a 2-cell `c`,
- a lag event for some future step `step`,
- no visible predictor for `step`,
- and failure of admissible (GaugeRefl) auto-regulation for the singleton `{c}`.
-/
def DynamicNoGoProfile
    {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {k' : P} (c : Cell (P := P)) (step : HistoryGraph.Path (CellSrc (P := P) c) k') : Prop :=
  match c with
  | ⟨h, k, p, q, ⟨α⟩⟩ =>
      TwistedHolonomy (P := P) sem obs target_obs (h := h) (k := k) (p := p) (q := q) α
      ∧ LagEvent (P := P) sem obs target_obs
          (h := h) (k := k) (k' := k') (p := p) (q := q) α step
      ∧ ¬ VisiblePredictsStep (P := P) sem obs target_obs (h := h) (k := k') step
      ∧ ¬ AutoRegulatedWrt (P := P) sem obs target_obs
          (fun φ => GaugeRefl (P := P) obs target_obs φ)
          (Set.singleton (⟨h, k, p, q, ⟨α⟩⟩ : Cell (P := P)))


/-- Same qualitative profile plus an exact compatibility dimension `n` for that step. -/
def DynamicNoGoProfileDim
    {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {k' : P} (c : Cell (P := P)) (step : HistoryGraph.Path (CellSrc (P := P) c) k')
    (n : Nat) : Prop :=
  DynamicNoGoProfile (P := P) sem obs target_obs c step ∧
    CompatDimEq (P := P) sem obs target_obs step n

/-- Same profile plus the quantitative claim “dimension exactly 2” for the chosen step. -/
def DynamicNoGoProfileDim2
    {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k)
    {k' : P} (c : Cell (P := P)) (step' : HistoryGraph.Path (CellSrc (P := P) c) k') : Prop :=
  DynamicNoGoProfile (P := P) sem obs target_obs c step' ∧ CompatDimEqTwo (P := P) sem obs target_obs step

/-!
## Two-interface strengthening: joint truth, marginal irreducibility, and finite mediation

Many examples in this repository naturally come with two partial interfaces (“margins”)
`A : S → VA` and `B : S → VB`. The joint interface is their product
`AB : S → VA × VB`.

The point of the two-interface layer is to keep the **joint dynamic truth**
`Compatible sem AB targetAB step x` fixed, and ask what can (or cannot) be decided from
either marginal projection alone.

The definitions below are intentionally lightweight predicates meant for documentation and
high-level theorems; detailed constructions and end-to-end wrappers live in
`COFRS/Examples/IndependenceRelationMediationChain.lean`.
-/

/-!
### Scope note

The predicate `JointIrreducibleMediationProfile` below is intentionally a **joint-level** profile:
it packages separation and repairability *on the joint interface*.

It does **not** include the marginal diagonal certification data (e.g. `LagEvent` witnesses on
`obsA` and `obsB`) nor the constructive extraction of marginal separating witnesses for `obsA`
and `obsB` from marginal no-go statements. Those stronger “full story” wrappers are provided in
`COFRS/Examples/IndependenceRelationMediationChain.lean` (see `endToEnd_full` and
`endToEnd_full_with_causalSignature2`).
-/

def obsAB {S : Type w} {VA : Type w} {VB : Type w} (obsA : S → VA) (obsB : S → VB) : S → VA × VB :=
  fun s => (obsA s, obsB s)

def targetAB {VA : Type w} {VB : Type w} (targetA : P → VA) (targetB : P → VB) : P → VA × VB :=
  fun p => (targetA p, targetB p)

def LeftObsPredictsJointStep
    {S : Type w} {VA : Type w} {VB : Type w}
    (sem : Semantics P S) (obsA : S → VA) (obsB : S → VB)
    (targetA : P → VA) (targetB : P → VB)
    {h k : P} (step : HistoryGraph.Path h k) : Prop :=
  ∃ pred : VA → Prop,
    ∀ x : FiberPt (P := P) (obsAB obsA obsB) (targetAB (P := P) targetA targetB) h,
      Compatible (P := P) sem (obsAB obsA obsB) (targetAB (P := P) targetA targetB) step x ↔
        pred (obsA x.1)

def RightObsPredictsJointStep
    {S : Type w} {VA : Type w} {VB : Type w}
    (sem : Semantics P S) (obsA : S → VA) (obsB : S → VB)
    (targetA : P → VA) (targetB : P → VB)
    {h k : P} (step : HistoryGraph.Path h k) : Prop :=
  ∃ pred : VB → Prop,
    ∀ x : FiberPt (P := P) (obsAB obsA obsB) (targetAB (P := P) targetA targetB) h,
      Compatible (P := P) sem (obsAB obsA obsB) (targetAB (P := P) targetA targetB) step x ↔
        pred (obsB x.1)

def MediatorDescendsLeft
    {S : Type w} {VA : Type w} {VB : Type w}
    (sem : Semantics P S) (obsA : S → VA) (obsB : S → VB)
    (targetA : P → VA) (targetB : P → VB)
    {h k : P} (step : HistoryGraph.Path h k) {n : Nat}
    (L : RefiningLiftData (P := P) sem (obsAB obsA obsB) (targetAB (P := P) targetA targetB) h step n) : Prop :=
  ∃ ρA : VA → Fin n, ∀ x, (L.extObs x).2 = ρA (obsA x.1)

def MediatorDescendsRight
    {S : Type w} {VA : Type w} {VB : Type w}
    (sem : Semantics P S) (obsA : S → VA) (obsB : S → VB)
    (targetA : P → VA) (targetB : P → VB)
    {h k : P} (step : HistoryGraph.Path h k) {n : Nat}
    (L : RefiningLiftData (P := P) sem (obsAB obsA obsB) (targetAB (P := P) targetA targetB) h step n) : Prop :=
  ∃ ρB : VB → Fin n, ∀ x, (L.extObs x).2 = ρB (obsB x.1)

/--
The core “joint relation” profile: the joint dynamic truth varies within the joint fiber
(so neither margin suffices), yet it is recoverable through an exact finite supplement
(`CompatDimEq n` / equivalently a `RefiningLift n`).

This predicate is intended as a reusable “invariant name” for statements of the form:

* marginal irreducibility for the joint truth (left and right),
* plus a minimal finite mediator at the joint level.

Precise end-to-end theorems proving this profile are provided in
`COFRS/Examples/IndependenceRelationMediationChain.lean`.
-/
def JointIrreducibleMediationProfile
    {S : Type w} {VA : Type w} {VB : Type w}
    (sem : Semantics P S) (obsA : S → VA) (obsB : S → VB)
    (targetA : P → VA) (targetB : P → VB)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) : Prop :=
  StepSeparatesFiber (P := P) sem (obsAB obsA obsB) (targetAB (P := P) targetA targetB) step
    ∧ ¬ LeftObsPredictsJointStep (P := P) sem obsA obsB targetA targetB step
    ∧ ¬ RightObsPredictsJointStep (P := P) sem obsA obsB targetA targetB step
    ∧ CompatDimEq (P := P) sem (obsAB obsA obsB) (targetAB (P := P) targetA targetB) step n

end WithHistoryGraph

end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
Auto-generated: `#print axioms` for each non-private `theorem`/`lemma` in this file.
-/
-- (no theorems/lemmas in this file)
#print axioms PrimitiveHolonomy.JointIrreducibleMediationProfile
/- AXIOM_AUDIT_END -/
