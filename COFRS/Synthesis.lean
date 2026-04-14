import COFRS.RegulationAndReduction

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

end WithHistoryGraph

end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
Auto-generated: `#print axioms` for each non-private `theorem`/`lemma` in this file.
-/
-- (no theorems/lemmas in this file)
/- AXIOM_AUDIT_END -/
