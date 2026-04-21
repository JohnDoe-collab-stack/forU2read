import COFRS.Examples.DynamicCompatDimN

/-!
# GeometryDynamicsIndependence

This file isolates the non-trivial point that motivated the experiments:

- a commutation-style geometric alignment can hold while dynamic truth still fails;
- conversely, dynamic truth can hold in a flat example with no geometric recombination.

So geometric coherence and dynamic truth are logically independent.
-/

universe u v w uQ

namespace PrimitiveHolonomy
namespace Examples
namespace GeometryDynamicsIndependence

open DynamicCompatDimN

/-- In this file, "geometric coherence" means existence of a non-trivial holonomy witness. -/
abbrev GeometricCoherence
    {P : Type u} [HistoryGraph P] {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q) : Prop :=
  TwistedHolonomy (P := P) sem obs target_obs α

/--
In experiments, a common *proxy* for "geometric alignment" is a same-source commutation / recombination
criterion: starting from the *same* micro-state `x`, the two paths `p` and `q` can be recombined into a
common `y`.

This is strictly weaker than `TwistedHolonomy`: it does not require *two distinct* sources `x ≠ x'`.

It corresponds more closely to training-time losses of the form "make `p_hat(x)` and `q_hat(x)` match".
-/
abbrev SameSourceRecombination
    {P : Type u} [HistoryGraph P] {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (p q : HistoryGraph.Path h k) : Prop :=
  ∀ x : FiberPt (P := P) obs target_obs h,
    ∃ y : FiberPt (P := P) obs target_obs k,
      Transport sem obs target_obs p x y ∧ Transport sem obs target_obs q x y

/-- Here "dynamic truth" means that visible data already predicts the future step compatibility. -/
abbrev DynamicTruth
    {P : Type u} [HistoryGraph P] {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) : Prop :=
  VisiblePredictsStep (P := P) sem obs target_obs step

/-- The dynamic binary witness from `DynamicCompatDimN` at `n = 2`. -/
def biasPred : Fin 2 → Prop := by
  intro i
  exact i = i0 2 (by decide)

theorem biased_commutation_geometric_without_dynamic_truth :
    GeometricCoherence
        (dSemantics (n := 2) (hn := by decide) biasPred)
        (dObs (n := 2))
        dTargetObs
        α_pq
      ∧
      ¬ DynamicTruth
        (dSemantics (n := 2) (hn := by decide) biasPred)
        (dObs (n := 2))
        dTargetObs
        (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) := by
  have hProfile :
      DynamicNoGoProfile (P := DPrefix)
        (dSemantics (n := 2) (hn := by decide) biasPred)
        (dObs (n := 2))
        dTargetObs
        cell_pq
        (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) := by
    refine
      profile_of_Pi0_notPi1
        (n := 2)
        (hn := by decide)
        biasPred
        ?_
        ?_
    · change i0 2 (by decide) = i0 2 (by decide)
      rfl
    · intro hEq
      exact (i0_ne_i1 (n := 2) (hn := by decide)) hEq.symm
  exact ⟨hProfile.1, hProfile.2.2.1⟩

/--
Same-source recombination holds in the biased commutation witness: `p` and `q` both erase hidden
information to the same canonical value, so they can be recombined from the same source.

Crucially, this does **not** restore dynamic truth (see `biased_commutation_geometric_without_dynamic_truth`).
-/
theorem biased_commutation_same_source_recombination :
    SameSourceRecombination
      (dSemantics (n := 2) (hn := by decide) biasPred)
      (dObs (n := 2))
      dTargetObs
      (DPath.p : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid)
      (DPath.q : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid) := by
  intro x
  refine ⟨dX (n := 2) DPrefix.mid (i0 2 (by decide)), ?_, ?_⟩
  · rfl
  · rfl

/-
Flat counterexample: the step is dynamically correct from visible data, but the
holonomy cell is completely flat, so there is no non-trivial geometric coherence.
-/

inductive FlatPrefix where
  | base (b : Bool)
  | mid  (b : Bool)
  | fut  (b : Bool)
  deriving DecidableEq

inductive FlatPath : FlatPrefix → FlatPrefix → Type where
  | id (h : FlatPrefix) : FlatPath h h
  | p    (b : Bool) : FlatPath (FlatPrefix.base b) (FlatPrefix.mid b)
  | q    (b : Bool) : FlatPath (FlatPrefix.base b) (FlatPrefix.mid b)
  | step (b : Bool) : FlatPath (FlatPrefix.base b) (FlatPrefix.fut b)

inductive FlatDef : {h k : FlatPrefix} → FlatPath h k → FlatPath h k → Prop where
  | pq (b : Bool) : FlatDef (FlatPath.p b) (FlatPath.q b)

def flatComp : {h k l : FlatPrefix} → FlatPath h k → FlatPath k l → FlatPath h l
  | _, _, _, r, s => by
      cases r with
      | id _ => exact s
      | p b => cases s with | id _ => exact FlatPath.p b
      | q b => cases s with | id _ => exact FlatPath.q b
      | step b => cases s with | id _ => exact FlatPath.step b

instance : HistoryGraph FlatPrefix where
  Path h k := FlatPath h k
  Deformation {_ _} pathLeft pathRight := FlatDef pathLeft pathRight
  idPath h := FlatPath.id h
  compPath := flatComp

/-!
Non-trivial "flat" witness (dynamic truth without geometric coherence).

We keep a *non-trivial* hidden space (`Bool`) so there are distinct micro-states in the fiber,
but we choose a step whose compatibility depends only on the *visible* coordinate.

This avoids the degenerate witness where the predictor is the constant predicate `True` on `Unit`:
the predictor is now a boolean predicate on the observable `Bool`.
-/
abbrev FlatState : Type := LagState Bool Bool

def flatObs : FlatState → Bool := lagObs (Y := Bool) (B := Bool)

def flatTargetObs : FlatPrefix → Bool
  | FlatPrefix.base b => b
  | FlatPrefix.mid b  => b
  | FlatPrefix.fut b  => b

def flatRel : {h k : FlatPrefix} → FlatPath h k → Relation FlatState FlatState
  | _, _, FlatPath.id _ => relId
  -- Non-trivial transports to `mid`: flip the hidden bit while preserving the visible.
  | _, _, FlatPath.p _ => fun x y => y.visible = x.visible ∧ y.hidden = Bool.not x.hidden
  | _, _, FlatPath.q _ => fun x y => y.visible = x.visible ∧ y.hidden = Bool.not x.hidden
  | _, _, FlatPath.step _ => fun x y => x = y ∧ x.visible = false

theorem flatRel_comp
    {h k l : FlatPrefix} (r : FlatPath h k) (s : FlatPath k l) (x y : FlatState) :
    flatRel (flatComp r s) x y ↔ relComp (flatRel r) (flatRel s) x y := by
  cases r with
  | id _ =>
      cases s <;>
        exact ⟨(fun hxy => ⟨_, rfl, hxy⟩), (fun ⟨_, rfl, hxy⟩ => hxy)⟩
  | p _ =>
      cases s with
      | id _ => exact ⟨(fun hxy => ⟨_, hxy, rfl⟩), (fun ⟨_, hxy, rfl⟩ => hxy)⟩
  | q _ =>
      cases s with
      | id _ => exact ⟨(fun hxy => ⟨_, hxy, rfl⟩), (fun ⟨_, hxy, rfl⟩ => hxy)⟩
  | step _ =>
      cases s with
      | id _ => exact ⟨(fun hxy => ⟨_, hxy, rfl⟩), (fun ⟨_, hxy, rfl⟩ => hxy)⟩

def flatSemantics : Semantics FlatPrefix FlatState where
  sem := fun {h k} path => flatRel path
  sem_id := by
    intro h x y
    cases h <;> rfl
  sem_comp := by
    intro h k l pathLeft pathRight x y
    exact flatRel_comp pathLeft pathRight x y

theorem flat_holonomy_eq
    (b : Bool)
    (x x' : FiberPt (P := FlatPrefix) flatObs flatTargetObs (FlatPrefix.base b)) :
    HolonomyRel (P := FlatPrefix)
      flatSemantics
      flatObs
      flatTargetObs
      (FlatDef.pq b)
      x
      x' →
      x = x' := by
  intro hHol
  rcases (holonomy_def (P := FlatPrefix) (sem := flatSemantics) (obs := flatObs)
      (target_obs := flatTargetObs) (α := FlatDef.pq b) (x := x) (x' := x')).1 hHol with
    ⟨y, hp, hq⟩
  -- Unfold transports: along `p` and `q` we preserve the visible bit and apply `Bool.not` to the hidden bit.
  cases x with
  | mk xs hxmem =>
    cases xs with
    | mk xv xh =>
      cases x' with
      | mk xs' hxmem' =>
        cases xs' with
        | mk xv' xh' =>
          have hp' : y.1.visible = xv ∧ y.1.hidden = Bool.not xh := hp
          have hq' : y.1.visible = xv' ∧ y.1.hidden = Bool.not xh' := hq
          have hvis : xv = xv' := (hp'.1).symm.trans hq'.1
          have hnot : Bool.not xh = Bool.not xh' := hp'.2.symm.trans hq'.2
          have hhid : xh = xh' := by
            cases xh <;> cases xh' <;> cases hnot <;> rfl
          apply Subtype.ext
          cases hvis
          cases hhid
          rfl

theorem flat_not_geometric_coherence :
    ∀ b : Bool,
      ¬ GeometricCoherence
        flatSemantics
        flatObs
        flatTargetObs
        (FlatDef.pq b) := by
  intro b
  intro hGeo
  rcases hGeo with ⟨x, x', hne, hHol⟩
  exact hne (flat_holonomy_eq b x x' hHol)

theorem flat_compatible_step_iff
    (b : Bool)
    (x : FiberPt (P := FlatPrefix) flatObs flatTargetObs (FlatPrefix.base b)) :
    Compatible (P := FlatPrefix)
        flatSemantics
        flatObs
        flatTargetObs
        (FlatPath.step b : HistoryGraph.Path (P := FlatPrefix) (FlatPrefix.base b) (FlatPrefix.fut b))
        x ↔ b = false := by
  have hxvis : x.1.visible = b := by
    have hxmem : flatObs x.1 = flatTargetObs (FlatPrefix.base b) := x.2
    -- Unfold `flatObs` and `flatTargetObs` in the fiber witness.
    dsimp [flatObs, flatTargetObs, PrimitiveHolonomy.lagObs] at hxmem
    exact hxmem
  constructor
  · rintro ⟨y, hy⟩
    -- `step` compatibility requires `x.visible = false`; on the base fiber we also have `x.visible = b`.
    have hxFalse : x.1.visible = false := by
      have : x.1 = y.1 ∧ x.1.visible = false := hy
      exact this.2
    cases b with
    | false =>
        rfl
    | true =>
        exact hxvis.symm.trans hxFalse
  · intro hb
    -- If `b = false`, choose `y := x` (reused as a point of the `fut` fiber) and satisfy the step predicate.
    cases b with
    | false =>
        refine ⟨⟨x.1, ?_⟩, ?_⟩
        · -- Need `flatObs x.1 = flatTargetObs (fut false)`, i.e. `x.visible = false`.
          have hxmem : flatObs x.1 = flatTargetObs (FlatPrefix.base false) := x.2
          -- The base and fut targets agree when `b = false`.
          -- Unfold both targets to the same boolean value.
          dsimp [flatTargetObs] at hxmem
          change flatObs x.1 = false
          exact hxmem
        · refine ⟨rfl, ?_⟩
          exact hxvis
    | true =>
        cases hb

theorem flat_dynamic_truth :
    ∀ b : Bool,
    DynamicTruth
      flatSemantics
      flatObs
      flatTargetObs
      (FlatPath.step b : HistoryGraph.Path (P := FlatPrefix) (FlatPrefix.base b) (FlatPrefix.fut b)) := by
  intro b
  refine ⟨Bool, (fun x => flatObs x.1), (fun v => v = false), ?_, ?_⟩
  · refine ⟨(fun v => v), ?_⟩
    intro x
    rfl
  · intro x
    constructor
    · intro hCompat
      -- Compatibility forces `b = false`, hence the visible predicate holds.
      have hb : b = false := (flat_compatible_step_iff b x).1 hCompat
      -- `σ x = obs x = b`, so `pred (σ x)` reduces to `b = false`.
      have hxvis : flatObs x.1 = b := by
        have hxmem : flatObs x.1 = flatTargetObs (FlatPrefix.base b) := x.2
        dsimp [flatObs, flatTargetObs, PrimitiveHolonomy.lagObs] at hxmem
        exact hxmem
      cases hb
      exact hxvis
    · intro hPred
      -- From `pred (σ x)` we get `obs x = false`, hence `b = false` on the base fiber.
      have hxvis : flatObs x.1 = b := by
        have hxmem : flatObs x.1 = flatTargetObs (FlatPrefix.base b) := x.2
        dsimp [flatObs, flatTargetObs, PrimitiveHolonomy.lagObs] at hxmem
        exact hxmem
      have hb : b = false := by
        -- hPred : flatObs x.1 = false
        exact hxvis.symm.trans hPred
      exact (flat_compatible_step_iff b x).2 hb

theorem flat_dynamic_truth_without_geometric_coherence :
    ∃ b : Bool,
      DynamicTruth
        flatSemantics
        flatObs
        flatTargetObs
        (FlatPath.step b : HistoryGraph.Path (P := FlatPrefix) (FlatPrefix.base b) (FlatPrefix.fut b))
      ∧
      ¬ GeometricCoherence
        flatSemantics
        flatObs
        flatTargetObs
        (FlatDef.pq b) := by
  refine ⟨false, ?_, ?_⟩
  · exact flat_dynamic_truth false
  · exact flat_not_geometric_coherence false

/--
Dynamic truth does not imply geometric coherence (flat family witness).

This is the second direction needed to read "independence" in the standard sense:
we exhibit a dynamically correct step while the corresponding commutation witness is flat.
-/
theorem dynamic_truth_does_not_imply_geometric_coherence :
    ¬ (∀ b : Bool,
      DynamicTruth
        flatSemantics
        flatObs
        flatTargetObs
        (FlatPath.step b : HistoryGraph.Path (P := FlatPrefix) (FlatPrefix.base b) (FlatPrefix.fut b)) →
      GeometricCoherence
        flatSemantics
        flatObs
        flatTargetObs
        (FlatDef.pq b)) := by
  intro hImp
  rcases flat_dynamic_truth_without_geometric_coherence with ⟨b, hDyn, hNotGeo⟩
  exact hNotGeo (hImp b hDyn)

theorem geometric_coherence_and_dynamic_truth_independent :
    (GeometricCoherence
        (dSemantics (n := 2) (hn := by decide) biasPred)
        (dObs (n := 2))
        dTargetObs
        α_pq
      ∧
      ¬ DynamicTruth
        (dSemantics (n := 2) (hn := by decide) biasPred)
        (dObs (n := 2))
        dTargetObs
        (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut))
      ∧
      (∃ b : Bool,
        DynamicTruth
          flatSemantics
          flatObs
          flatTargetObs
          (FlatPath.step b : HistoryGraph.Path (P := FlatPrefix) (FlatPrefix.base b) (FlatPrefix.fut b))
        ∧
        ¬ GeometricCoherence
          flatSemantics
          flatObs
          flatTargetObs
          (FlatDef.pq b)) := by
  exact ⟨biased_commutation_geometric_without_dynamic_truth, flat_dynamic_truth_without_geometric_coherence⟩

/--
The naive statement "aligned holonomy implies dynamic truth" is false: the biased
commutation witness is geometrically coherent while still dynamically wrong.
-/
theorem holonomy_aligned_does_not_imply_dynamic_truth :
    ¬ (
      GeometricCoherence
        (dSemantics (n := 2) (hn := by decide) biasPred)
        (dObs (n := 2))
        dTargetObs
        α_pq →
      DynamicTruth
        (dSemantics (n := 2) (hn := by decide) biasPred)
        (dObs (n := 2))
        dTargetObs
        (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut)
    ) := by
  intro hImp
  exact
    biased_commutation_geometric_without_dynamic_truth.2
      (hImp biased_commutation_geometric_without_dynamic_truth.1)

/--
This packages the strengthened theorem-shape we should aim for next:
geometric coherence plus an extra dynamic criterion `X` should imply dynamic truth.
-/
def StrengthenedReconstructionTarget
    {P : Type u} [HistoryGraph P] {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    {k' : P} (step : HistoryGraph.Path h k') (X : Prop) : Prop :=
  (GeometricCoherence sem obs target_obs α ∧ X) → DynamicTruth sem obs target_obs step

theorem not_strengthenedReconstructionTarget_true_for_biased_commutation :
    ¬ StrengthenedReconstructionTarget
      (dSemantics (n := 2) (hn := by decide) biasPred)
      (dObs (n := 2))
      dTargetObs
      α_pq
      (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut)
      True := by
  intro hTarget
  have hGeo : GeometricCoherence
      (dSemantics (n := 2) (hn := by decide) biasPred)
      (dObs (n := 2))
      dTargetObs
      α_pq :=
    biased_commutation_geometric_without_dynamic_truth.1
  have hDyn : DynamicTruth
      (dSemantics (n := 2) (hn := by decide) biasPred)
      (dObs (n := 2))
      dTargetObs
      (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) :=
    hTarget ⟨hGeo, True.intro⟩
  exact biased_commutation_geometric_without_dynamic_truth.2 hDyn

theorem strengthenedReconstructionTarget_iff
    {P : Type u} [HistoryGraph P] {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    {k' : P} (step : HistoryGraph.Path h k') (X : Prop) :
    StrengthenedReconstructionTarget sem obs target_obs α step X ↔
      (X → GeometricCoherence sem obs target_obs α → DynamicTruth sem obs target_obs step) := by
  constructor
  · intro hTarget hX hGeo
    exact hTarget ⟨hGeo, hX⟩
  · intro hCurried hPair
    exact hCurried hPair.2 hPair.1

end GeometryDynamicsIndependence
end Examples
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.Examples.GeometryDynamicsIndependence.biased_commutation_geometric_without_dynamic_truth
#print axioms PrimitiveHolonomy.Examples.GeometryDynamicsIndependence.biased_commutation_same_source_recombination
#print axioms PrimitiveHolonomy.Examples.GeometryDynamicsIndependence.flat_holonomy_eq
#print axioms PrimitiveHolonomy.Examples.GeometryDynamicsIndependence.flat_not_geometric_coherence
#print axioms PrimitiveHolonomy.Examples.GeometryDynamicsIndependence.flat_compatible_step_iff
#print axioms PrimitiveHolonomy.Examples.GeometryDynamicsIndependence.flat_dynamic_truth
#print axioms PrimitiveHolonomy.Examples.GeometryDynamicsIndependence.flat_dynamic_truth_without_geometric_coherence
#print axioms PrimitiveHolonomy.Examples.GeometryDynamicsIndependence.dynamic_truth_does_not_imply_geometric_coherence
#print axioms PrimitiveHolonomy.Examples.GeometryDynamicsIndependence.geometric_coherence_and_dynamic_truth_independent
#print axioms PrimitiveHolonomy.Examples.GeometryDynamicsIndependence.holonomy_aligned_does_not_imply_dynamic_truth
#print axioms PrimitiveHolonomy.Examples.GeometryDynamicsIndependence.not_strengthenedReconstructionTarget_true_for_biased_commutation
#print axioms PrimitiveHolonomy.Examples.GeometryDynamicsIndependence.strengthenedReconstructionTarget_iff
/- AXIOM_AUDIT_END -/
