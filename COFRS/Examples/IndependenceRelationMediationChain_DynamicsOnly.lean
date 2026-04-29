import COFRS.Dynamics

/-!
# Independence → relation → mediator (two interfaces) — Dynamics-only variant

This file is a **self-contained** (single-import) rewrite of:

* `COFRS/Examples/IndependenceRelationMediationChain.lean`

with the explicit goal that the module depends on **nothing** beyond:

* `COFRS.Dynamics`

It preserves the same mathematical content (separation / marginal no-go / joint lift with minimality /
optional `n=2` causal signature / packaging as a named invariant), but places all statements in the
namespace `PrimitiveHolonomy.Examples.DynamicsOnly` to avoid name collisions with the original file.

All proofs are constructive; see the `AXIOM_AUDIT` block at the end.
-/

namespace PrimitiveHolonomy
namespace Examples
namespace DynamicsOnly

universe u w

variable {P : Type u} [HistoryGraph P]

/-!
## A minimal copy of the “joint interface” wrappers

The original project defines these in `COFRS/Synthesis.lean`, but that file is not imported here.
They are purely definitional and do not add any axioms.
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
    ∀ x : FiberPt (P := P) (obsAB obsA obsB) (targetAB targetA targetB) h,
      Compatible (P := P) sem (obsAB obsA obsB) (targetAB targetA targetB) step x ↔
        pred (obsA x.1)

def RightObsPredictsJointStep
    {S : Type w} {VA : Type w} {VB : Type w}
    (sem : Semantics P S) (obsA : S → VA) (obsB : S → VB)
    (targetA : P → VA) (targetB : P → VB)
    {h k : P} (step : HistoryGraph.Path h k) : Prop :=
  ∃ pred : VB → Prop,
    ∀ x : FiberPt (P := P) (obsAB obsA obsB) (targetAB targetA targetB) h,
      Compatible (P := P) sem (obsAB obsA obsB) (targetAB targetA targetB) step x ↔
        pred (obsB x.1)

def MediatorDescendsLeft
    {S : Type w} {VA : Type w} {VB : Type w}
    (sem : Semantics P S) (obsA : S → VA) (obsB : S → VB)
    (targetA : P → VA) (targetB : P → VB)
    {h k : P} (step : HistoryGraph.Path h k) {n : Nat}
    (L : RefiningLiftData (P := P) sem (obsAB obsA obsB) (targetAB targetA targetB) h step n) : Prop :=
  ∃ ρA : VA → Fin n, ∀ x, (L.extObs x).2 = ρA (obsA x.1)

def MediatorDescendsRight
    {S : Type w} {VA : Type w} {VB : Type w}
    (sem : Semantics P S) (obsA : S → VA) (obsB : S → VB)
    (targetA : P → VA) (targetB : P → VB)
    {h k : P} (step : HistoryGraph.Path h k) {n : Nat}
    (L : RefiningLiftData (P := P) sem (obsAB obsA obsB) (targetAB targetA targetB) h step n) : Prop :=
  ∃ ρB : VB → Fin n, ∀ x, (L.extObs x).2 = ρB (obsB x.1)

def JointIrreducibleMediationProfile
    {S : Type w} {VA : Type w} {VB : Type w}
    (sem : Semantics P S) (obsA : S → VA) (obsB : S → VB)
    (targetA : P → VA) (targetB : P → VB)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) : Prop :=
  StepSeparatesFiber (P := P) sem (obsAB obsA obsB) (targetAB targetA targetB) step
    ∧ ¬ LeftObsPredictsJointStep (P := P) sem obsA obsB targetA targetB step
    ∧ ¬ RightObsPredictsJointStep (P := P) sem obsA obsB targetA targetB step
    ∧ CompatDimEq (P := P) sem (obsAB obsA obsB) (targetAB targetA targetB) step n


/-!
## A minimal copy of the “converse / normal-form” bridge (enumeration split)

The original project provides this in `COFRS/ConverseNormalForm.lean`. Here we inline the minimal
prefix needed for `IndependenceRelationMediationChain`:

* explicit finite enumeration of a fiber (no classical `Fintype`),
* constructive split `ObsPredictsStep ∨ StepSeparatesFiber`,
* bridge form with `fiber ≃ Fin N`.
-/

structure FiberEnum {S V : Type w} (obs : S → V) (target_obs : P → V) (h : P) : Type w where
  N : Nat
  enum : Fin N → FiberPt (P := P) obs target_obs h
  surj : ∀ x : FiberPt (P := P) obs target_obs h, ∃ i : Fin N, enum i = x

namespace FiberEnum

def ofEquivFin {S V : Type w} (obs : S → V) (target_obs : P → V) (h : P)
    {N : Nat} (e : Equiv (FiberPt (P := P) obs target_obs h) (Fin N)) :
    FiberEnum (P := P) obs target_obs h :=
  { N := N
    enum := fun i => e.invFun i
    surj := fun x => ⟨e.toFun x, e.left_inv x⟩ }

end FiberEnum

section WithEnum

variable {S V : Type w}
variable (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
variable {h k : P} (step : HistoryGraph.Path h k)

theorem obsPredictsStep_or_stepSeparatesFiber_of_fiberEnum :
    (E : FiberEnum (P := P) obs target_obs h) →
    (decCompat : ∀ x : FiberPt (P := P) obs target_obs h,
      Decidable (Compatible (P := P) sem obs target_obs step x)) →
    ObsPredictsStep (P := P) sem obs target_obs step
      ∨ StepSeparatesFiber (P := P) sem obs target_obs step := by
  intro E decCompat
  let Pcompat : Fin E.N → Prop :=
    fun i => Compatible (P := P) sem obs target_obs step (E.enum i)
  have decPcompat : ∀ i : Fin E.N, Decidable (Pcompat i) :=
    fun i => decCompat (E.enum i)
  let Pncompat : Fin E.N → Prop := fun i => ¬ Pcompat i
  have decPncompat : ∀ i : Fin E.N, Decidable (Pncompat i) := by
    intro i
    letI : Decidable (Pcompat i) := decPcompat i
    dsimp [Pncompat]
    exact instDecidableNot
  cases PrimitiveHolonomy.Combinatorics.decidableExistsFin
      (n := E.N)
      (P := Pcompat)
      (decP := decPcompat) with
  | isFalse hNoCompat =>
      refine Or.inl ?_
      refine ⟨(fun _v => False), ?_⟩
      intro x
      constructor
      · intro hx
        rcases E.surj x with ⟨i, hi⟩
        have : ∃ i : Fin E.N, Pcompat i := by
          refine ⟨i, ?_⟩
          simpa [Pcompat, hi] using hx
        exact False.elim (hNoCompat this)
      · intro hFalse
        cases hFalse
  | isTrue hHasCompat =>
      rcases hHasCompat with ⟨i0, hi0⟩
      let x0 : FiberPt (P := P) obs target_obs h := E.enum i0
      have hx0 : Compatible (P := P) sem obs target_obs step x0 := by
        simpa [x0, Pcompat] using hi0
      cases PrimitiveHolonomy.Combinatorics.decidableExistsFin
          (n := E.N)
          (P := Pncompat)
          (decP := decPncompat) with
      | isTrue hHasNCompat =>
          rcases hHasNCompat with ⟨i1, hi1⟩
          let x1 : FiberPt (P := P) obs target_obs h := E.enum i1
          have hx1 : ¬ Compatible (P := P) sem obs target_obs step x1 := by
            simpa [x1, Pncompat, Pcompat] using hi1
          have hxne : x0 ≠ x1 := by
            intro hEq
            exact hx1 (by simpa [hEq] using hx0)
          exact Or.inr ⟨x0, x1, hxne, hx0, hx1⟩
      | isFalse hNoNCompat =>
          have hall_enum : ∀ i : Fin E.N, Pcompat i := by
            intro i
            cases decPcompat i with
            | isTrue hi =>
                exact hi
            | isFalse hni =>
                exact False.elim (hNoNCompat ⟨i, hni⟩)
          have hall : ∀ x : FiberPt (P := P) obs target_obs h,
              Compatible (P := P) sem obs target_obs step x := by
            intro x
            rcases E.surj x with ⟨i, hi⟩
            have : Compatible (P := P) sem obs target_obs step (E.enum i) := by
              simpa [Pcompat] using hall_enum i
            simpa [hi] using this
          refine Or.inl ?_
          refine ⟨(fun _v => True), ?_⟩
          intro x
          constructor
          · intro _hx
            trivial
          · intro _hTrue
            exact hall x

theorem stepSeparatesFiber_of_not_obsPredictsStep_of_fiberEnum
    (hNoObs : ¬ ObsPredictsStep (P := P) sem obs target_obs step) :
    (E : FiberEnum (P := P) obs target_obs h) →
    (decCompat : ∀ x : FiberPt (P := P) obs target_obs h,
      Decidable (Compatible (P := P) sem obs target_obs step x)) →
    StepSeparatesFiber (P := P) sem obs target_obs step := by
  intro E decCompat
  rcases obsPredictsStep_or_stepSeparatesFiber_of_fiberEnum
      (P := P) (sem := sem) (obs := obs) (target_obs := target_obs)
      (h := h) (k := k) (step := step) E decCompat with hObs | hSep
  · exact False.elim (hNoObs hObs)
  · exact hSep

end WithEnum

section WithEquivFin

variable {S V : Type w}
variable (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
variable {h k : P} (step : HistoryGraph.Path h k)

theorem stepSeparatesFiber_of_not_obsPredictsStep_of_equivFin
    {N : Nat} (e : Equiv (FiberPt (P := P) obs target_obs h) (Fin N))
    (decCompat : ∀ x : FiberPt (P := P) obs target_obs h,
      Decidable (Compatible (P := P) sem obs target_obs step x))
    (hNoObs : ¬ ObsPredictsStep (P := P) sem obs target_obs step) :
    StepSeparatesFiber (P := P) sem obs target_obs step :=
  stepSeparatesFiber_of_not_obsPredictsStep_of_fiberEnum
    (P := P) (sem := sem) (obs := obs) (target_obs := target_obs)
    (h := h) (k := k) (step := step) hNoObs
    (E := FiberEnum.ofEquivFin (P := P) obs target_obs h e)
    decCompat

end WithEquivFin


/-!
## A minimal copy of the generic “CausalSignature2” layer

The original project provides this generic layer inside
`COFRS/Examples/DiagonalizationMediationCausalityThesis.lean` but that file imports a heavy
example (`GodelByCode`). Here we inline the generic layer only.
-/

section CausalSignature2Core

universe w'
variable {S V : Type w'}
variable (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
variable {h k : P} (step : HistoryGraph.Path h k)

def finZero2 : Fin 2 := ⟨0, by decide⟩
def finOne2 : Fin 2 := ⟨1, by decide⟩

abbrev LiftReadout (L : RefiningLiftData (P := P) sem obs target_obs h step 2) :
    FiberPt (P := P) obs target_obs h → Prop :=
  fun x => L.predFin ((L.extObs x).2)

def fin2Swap (i : Fin 2) : Fin 2 :=
  if i.val = 0 then finOne2 else finZero2

abbrev LiftReadoutPerm (L : RefiningLiftData (P := P) sem obs target_obs h step 2) :
    FiberPt (P := P) obs target_obs h → Prop :=
  fun x => L.predFin (fin2Swap ((L.extObs x).2))

abbrev LiftReadoutAblate (L : RefiningLiftData (P := P) sem obs target_obs h step 2) :
    FiberPt (P := P) obs target_obs h → Prop :=
  fun _x => L.predFin finZero2

theorem no_constant_classifier_of_stepSeparatesFiber
    (hSep : StepSeparatesFiber (P := P) sem obs target_obs step) :
    ¬ ∃ c : Prop, ∀ x : FiberPt (P := P) obs target_obs h,
        Compatible (P := P) sem obs target_obs step x ↔ c := by
  intro hC
  rcases hC with ⟨c, hc⟩
  rcases hSep with ⟨x, x', hxne, hx, hx'⟩
  have hxEq : Compatible (P := P) sem obs target_obs step x ↔
      Compatible (P := P) sem obs target_obs step x' := by
    exact (hc x).trans ((hc x').symm)
  have : Compatible (P := P) sem obs target_obs step x' := (hxEq.mp hx)
  exact hx' this

theorem perm_changes_readout_of_stepSeparatesFiber
    (L : RefiningLiftData (P := P) sem obs target_obs h step 2)
    (hSep : StepSeparatesFiber (P := P) sem obs target_obs step) :
    ∃ x : FiberPt (P := P) obs target_obs h,
      ¬ (LiftReadoutPerm (P := P) sem obs target_obs step L x ↔
        LiftReadout (P := P) sem obs target_obs step L x) := by
  rcases hSep with ⟨x0, x1, _hxne, hx0, hx1⟩

  have h0 : LiftReadout (P := P) sem obs target_obs step L x0 := by
    have := (L.factors x0).1 hx0
    dsimp [LiftReadout]
    exact this

  have h1 : ¬ LiftReadout (P := P) sem obs target_obs step L x1 := by
    intro h
    dsimp [LiftReadout] at h
    have : Compatible (P := P) sem obs target_obs step x1 :=
      (L.factors x1).2 h
    exact hx1 this

  have hσne : (L.extObs x0).2 ≠ (L.extObs x1).2 := by
    intro hσ
    have hpredEq : LiftReadout (P := P) sem obs target_obs step L x0 ↔
        LiftReadout (P := P) sem obs target_obs step L x1 := by
      dsimp [LiftReadout]
      exact iff_of_eq (congrArg L.predFin hσ)
    exact h1 (hpredEq.mp h0)

  have fin2_val_eq_zero_or_eq_one : ∀ i : Fin 2, i.val = 0 ∨ i.val = 1 := by
    intro i
    cases i with
    | mk v hv =>
        cases v with
        | zero =>
            left; rfl
        | succ v' =>
            have hv' : v' = 0 := by
              have : v' < 1 := by
                have : Nat.succ v' < 2 := hv
                exact Nat.lt_of_succ_lt_succ this
              exact nat_eq_zero_of_lt_one this
            subst hv'
            right; rfl

  have hswap : fin2Swap ((L.extObs x0).2) = (L.extObs x1).2 := by
    rcases fin2_val_eq_zero_or_eq_one ((L.extObs x0).2) with h0v | h0v
    · have h1v : ((L.extObs x1).2).val = 1 := by
        rcases fin2_val_eq_zero_or_eq_one ((L.extObs x1).2) with h10 | h11
        ·
          exfalso
          apply hσne
          apply Fin.ext
          exact h0v.trans h10.symm
        · exact h11
      apply Fin.ext
      have hSwap0 : fin2Swap ((L.extObs x0).2) = finOne2 := by
        dsimp [fin2Swap]
        rw [if_pos h0v]
      have : (fin2Swap ((L.extObs x0).2)).val = 1 := by
        rw [hSwap0]
        rfl
      exact this.trans h1v.symm
    · have h1v : ((L.extObs x1).2).val = 0 := by
        rcases fin2_val_eq_zero_or_eq_one ((L.extObs x1).2) with h10 | h11
        · exact h10
        ·
          exfalso
          apply hσne
          apply Fin.ext
          exact h0v.trans h11.symm
      apply Fin.ext
      have hSwap0 : fin2Swap ((L.extObs x0).2) = finZero2 := by
        have hnot : ((L.extObs x0).2).val ≠ 0 := by
          intro hEq0
          have one_ne_zero : (1 : Nat) ≠ 0 := by
            intro hEq
            cases hEq
          exact one_ne_zero (h0v.symm.trans hEq0)
        dsimp [fin2Swap]
        rw [if_neg hnot]
      have : (fin2Swap ((L.extObs x0).2)).val = 0 := by
        rw [hSwap0]
        rfl
      exact this.trans h1v.symm

  refine ⟨x0, ?_⟩
  intro hIff
  have hPerm0 : LiftReadoutPerm (P := P) sem obs target_obs step L x0 ↔
      LiftReadout (P := P) sem obs target_obs step L x1 := by
    dsimp [LiftReadoutPerm, LiftReadout]
    exact iff_of_eq (congrArg L.predFin hswap)
  have hPermFalse : ¬ LiftReadoutPerm (P := P) sem obs target_obs step L x0 := by
    intro hPerm
    exact h1 (hPerm0.mp hPerm)
  have : LiftReadoutPerm (P := P) sem obs target_obs step L x0 := (hIff.2 h0)
  exact hPermFalse this

theorem ablation_breaks_correctness_of_stepSeparatesFiber
    (L : RefiningLiftData (P := P) sem obs target_obs h step 2)
    (hSep : StepSeparatesFiber (P := P) sem obs target_obs step) :
    ¬ (∀ x : FiberPt (P := P) obs target_obs h,
        Compatible (P := P) sem obs target_obs step x ↔
          LiftReadoutAblate (P := P) sem obs target_obs step L x) := by
  intro hAbl
  have : ∃ c : Prop, ∀ x : FiberPt (P := P) obs target_obs h,
      Compatible (P := P) sem obs target_obs step x ↔ c := by
    refine ⟨L.predFin finZero2, ?_⟩
    intro x
    have hx := hAbl x
    dsimp [LiftReadoutAblate] at hx
    exact hx
  exact (no_constant_classifier_of_stepSeparatesFiber (P := P) sem obs target_obs step hSep) this

structure CausalSignature2Data : Type w' where
  L : RefiningLiftData (P := P) sem obs target_obs h step 2
  permWitness :
    ∃ x : FiberPt (P := P) obs target_obs h,
      ¬ (LiftReadoutPerm (P := P) sem obs target_obs step L x ↔
        LiftReadout (P := P) sem obs target_obs step L x)
  ablationFails :
    ¬ (∀ x : FiberPt (P := P) obs target_obs h,
        Compatible (P := P) sem obs target_obs step x ↔
          LiftReadoutAblate (P := P) sem obs target_obs step L x)

abbrev CausalSignature2 : Prop :=
  Nonempty (CausalSignature2Data (P := P) sem obs target_obs (h := h) step)

theorem causalSignature2_of_stepSeparatesFiber_of_refiningLift2
    (hSep : StepSeparatesFiber (P := P) sem obs target_obs step)
    (hLift : RefiningLift (P := P) sem obs target_obs h step 2) :
    CausalSignature2 (P := P) sem obs target_obs (h := h) step := by
  rcases hLift with ⟨L⟩
  refine ⟨⟨L, ?_, ?_⟩⟩
  · exact perm_changes_readout_of_stepSeparatesFiber (P := P) sem obs target_obs step L hSep
  · exact ablation_breaks_correctness_of_stepSeparatesFiber (P := P) sem obs target_obs step L hSep

end CausalSignature2Core


/-!
## Main content: the two-interface chain (same as the original file, but self-contained)
-/

section TwoInterfaces

variable {S VA VB : Type w}
variable (sem : Semantics P S)
variable (obsA : S → VA) (obsB : S → VB)
variable (targetA : P → VA) (targetB : P → VB)
variable {h k : P} (step : HistoryGraph.Path h k)

-- Local “joint interface” abbreviations (fixed to the section variables).
-- We use `let`-bindings inside definitions/theorems below to avoid re-generalizing `obsA`, `obsB`,
-- `targetA`, `targetB` as parameters of a standalone constant.
local notation "obsAB'" => (obsAB obsA obsB)
local notation "targetAB'" => (targetAB targetA targetB)

def fiberAB_to_A :
    FiberPt (P := P) (obsAB obsA obsB)
      (targetAB targetA targetB) h →
      FiberPt (P := P) obsA targetA h :=
  fun x => ⟨x.1, by exact congrArg Prod.fst x.2⟩

def fiberAB_to_B :
    FiberPt (P := P) (obsAB obsA obsB)
      (targetAB targetA targetB) h →
      FiberPt (P := P) obsB targetB h :=
  fun x => ⟨x.1, by exact congrArg Prod.snd x.2⟩

theorem compatibleA_of_compatibleAB
    (x :
      FiberPt (P := P) (obsAB obsA obsB)
        (targetAB targetA targetB) h) :
      Compatible (P := P) sem (obsAB obsA obsB)
        (targetAB targetA targetB) step x →
      Compatible (P := P) sem obsA targetA step
        (fiberAB_to_A (P := P) (obsA := obsA) (obsB := obsB) (targetA := targetA)
          (targetB := targetB) (h := h) x) := by
  intro hC
  rcases hC with ⟨y, hTrans⟩
  refine ⟨⟨y.1, ?_⟩, ?_⟩
  · exact congrArg Prod.fst y.2
  · exact hTrans

theorem compatibleB_of_compatibleAB
    (x :
      FiberPt (P := P) (obsAB obsA obsB)
        (targetAB targetA targetB) h) :
      Compatible (P := P) sem (obsAB obsA obsB)
        (targetAB targetA targetB) step x →
      Compatible (P := P) sem obsB targetB step
        (fiberAB_to_B (P := P) (obsA := obsA) (obsB := obsB) (targetA := targetA)
          (targetB := targetB) (h := h) x) := by
  intro hC
  rcases hC with ⟨y, hTrans⟩
  refine ⟨⟨y.1, ?_⟩, ?_⟩
  · exact congrArg Prod.snd y.2
  · exact hTrans

abbrev LeftObsPredictsJointStep' : Prop :=
  LeftObsPredictsJointStep (P := P) sem obsA obsB targetA targetB step

abbrev RightObsPredictsJointStep' : Prop :=
  RightObsPredictsJointStep (P := P) sem obsA obsB targetA targetB step

theorem not_sigFactorsThrough_of_leftFactors
    {Q : Type w}
    (σ : FiberPt (P := P) (obsAB')
      (targetAB') h → Q)
    (hσ : ∃ f : VA → Q, ∀ x, σ x = f (obsA x.1))
    (hSep :
      StepSeparatesFiber (P := P) sem (obsAB')
        (targetAB') step) :
    ¬ SigFactorsThrough (P := P) sem (obsAB')
      (targetAB') (h := h) σ := by
  intro hFac
  rcases hSep with ⟨x, x', _hxne, hx, hx'⟩
  rcases hσ with ⟨f, hf⟩
  have hAx : obsA x.1 = targetA h := congrArg Prod.fst x.2
  have hAx' : obsA x'.1 = targetA h := congrArg Prod.fst x'.2
  have hEq : σ x = σ x' := by
    calc
      σ x = f (obsA x.1) := hf x
      _ = f (targetA h) := congrArg f hAx
      _ = f (obsA x'.1) := (congrArg f hAx').symm
      _ = σ x' := (hf x').symm
  have hSig :
      ∀ s, Sig (P := P) sem (obsAB')
        (targetAB') x s ↔
          Sig (P := P) sem (obsAB')
            (targetAB') x' s :=
    hFac (x := x) (x' := x') hEq
  let s : Future (P := P) h := ⟨k, step⟩
  have hStep := hSig s
  dsimp [Sig, CompatibleFuture] at hStep
  exact hx' (hStep.mp hx)

theorem not_sigFactorsThrough_of_rightFactors
    {Q : Type w}
    (σ : FiberPt (P := P) (obsAB')
      (targetAB') h → Q)
    (hσ : ∃ f : VB → Q, ∀ x, σ x = f (obsB x.1))
    (hSep :
      StepSeparatesFiber (P := P) sem (obsAB')
        (targetAB') step) :
    ¬ SigFactorsThrough (P := P) sem (obsAB')
      (targetAB') (h := h) σ := by
  intro hFac
  rcases hSep with ⟨x, x', _hxne, hx, hx'⟩
  rcases hσ with ⟨f, hf⟩
  have hBx : obsB x.1 = targetB h := congrArg Prod.snd x.2
  have hBx' : obsB x'.1 = targetB h := congrArg Prod.snd x'.2
  have hEq : σ x = σ x' := by
    calc
      σ x = f (obsB x.1) := hf x
      _ = f (targetB h) := congrArg f hBx
      _ = f (obsB x'.1) := (congrArg f hBx').symm
      _ = σ x' := (hf x').symm
  have hSig :
      ∀ s, Sig (P := P) sem (obsAB')
        (targetAB') x s ↔
          Sig (P := P) sem (obsAB')
            (targetAB') x' s :=
    hFac (x := x) (x' := x') hEq
  let s : Future (P := P) h := ⟨k, step⟩
  have hStep := hSig s
  dsimp [Sig, CompatibleFuture] at hStep
  exact hx' (hStep.mp hx)

theorem refiningLift_of_jointCompatSigDimLe
    {n : Nat}
    (hSig :
      CompatSigDimLe (P := P) sem (obsAB')
        (targetAB') (h := h) n) :
    RefiningLift (P := P) sem (obsAB')
      (targetAB') h step n := by
  exact refiningLift_of_compatSigDimLe (P := P) sem
    (obsAB')
    (targetAB')
    (h := h) (k := k) (step := step) (n := n) hSig

abbrev MediatorDescendsLeft' {n : Nat}
    (L : RefiningLiftData (P := P) sem (obsAB')
      (targetAB') h step n) : Prop :=
  MediatorDescendsLeft (P := P) sem obsA obsB targetA targetB step L

abbrev MediatorDescendsRight' {n : Nat}
    (L : RefiningLiftData (P := P) sem (obsAB')
      (targetAB') h step n) : Prop :=
  MediatorDescendsRight (P := P) sem obsA obsB targetA targetB step L

theorem leftObsPredictsJointStep_of_mediatorDescendsLeft
    {n : Nat}
    (L : RefiningLiftData (P := P) sem (obsAB')
      (targetAB') h step n) :
    MediatorDescendsLeft' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step L →
      LeftObsPredictsJointStep' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
        (targetA := targetA) (targetB := targetB) (h := h) (k := k) step := by
  rintro ⟨ρA, hρA⟩
  refine ⟨(fun v => L.predFin (ρA v)), ?_⟩
  intro x
  have hx : Compatible (P := P) sem (obsAB')
      (targetAB') step x ↔
        L.predFin ((L.extObs x).2) :=
    L.factors x
  simpa [hρA x] using hx

theorem rightObsPredictsJointStep_of_mediatorDescendsRight
    {n : Nat}
    (L : RefiningLiftData (P := P) sem (obsAB')
      (targetAB') h step n) :
    MediatorDescendsRight' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step L →
      RightObsPredictsJointStep' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
        (targetA := targetA) (targetB := targetB) (h := h) (k := k) step := by
  rintro ⟨ρB, hρB⟩
  refine ⟨(fun v => L.predFin (ρB v)), ?_⟩
  intro x
  have hx : Compatible (P := P) sem (obsAB')
      (targetAB') step x ↔
        L.predFin ((L.extObs x).2) :=
    L.factors x
  simpa [hρB x] using hx

theorem not_mediatorDescendsLeft_of_not_leftObsPredictsJointStep
    {n : Nat}
    (L : RefiningLiftData (P := P) sem (obsAB')
      (targetAB') h step n)
    (hNo : ¬ LeftObsPredictsJointStep' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step) :
    ¬ MediatorDescendsLeft' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step L := by
  intro hDesc
  exact hNo (leftObsPredictsJointStep_of_mediatorDescendsLeft
    (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
    (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step) L hDesc)

theorem not_mediatorDescendsRight_of_not_rightObsPredictsJointStep
    {n : Nat}
    (L : RefiningLiftData (P := P) sem (obsAB')
      (targetAB') h step n)
    (hNo : ¬ RightObsPredictsJointStep' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step) :
    ¬ MediatorDescendsRight' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step L := by
  intro hDesc
  exact hNo (rightObsPredictsJointStep_of_mediatorDescendsRight
    (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
    (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step) L hDesc)

theorem not_leftObsPredictsJointStep_of_stepSeparatesJointFiber
    (hSep :
      StepSeparatesFiber (P := P) sem (obsAB')
        (targetAB') step) :
    ¬ LeftObsPredictsJointStep' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
        (targetA := targetA) (targetB := targetB) (h := h) (k := k) step := by
  intro hPred
  rcases hPred with ⟨pred, hcorr⟩
  have hConst :
      ∃ c : Prop,
        ∀ x : FiberPt (P := P) (obsAB')
            (targetAB') h,
          Compatible (P := P) sem (obsAB')
              (targetAB') step x ↔ c := by
    refine ⟨pred (targetA h), ?_⟩
    intro x
    have hxA : obsA x.1 = targetA h := congrArg Prod.fst x.2
    simpa [hxA] using (hcorr x)
  exact (no_constant_classifier_of_stepSeparatesFiber
      (P := P) (sem := sem)
      (obs := (obsAB'))
      (target_obs := (targetAB'))
      (h := h) (k := k) (step := step) hSep) hConst

theorem not_rightObsPredictsJointStep_of_stepSeparatesJointFiber
    (hSep :
      StepSeparatesFiber (P := P) sem (obsAB')
        (targetAB') step) :
    ¬ RightObsPredictsJointStep' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
        (targetA := targetA) (targetB := targetB) (h := h) (k := k) step := by
  intro hPred
  rcases hPred with ⟨pred, hcorr⟩
  have hConst :
      ∃ c : Prop,
        ∀ x : FiberPt (P := P) (obsAB')
            (targetAB') h,
          Compatible (P := P) sem (obsAB')
              (targetAB') step x ↔ c := by
    refine ⟨pred (targetB h), ?_⟩
    intro x
    have hxB : obsB x.1 = targetB h := congrArg Prod.snd x.2
    simpa [hxB] using (hcorr x)
  exact (no_constant_classifier_of_stepSeparatesFiber
      (P := P) (sem := sem)
      (obs := (obsAB'))
      (target_obs := (targetAB'))
      (h := h) (k := k) (step := step) hSep) hConst

theorem endToEnd_joint_global
    {n : Nat}
    (hSepAB :
      StepSeparatesFiber (P := P) sem (obsAB')
        (targetAB') step)
    (hSigAB :
      CompatSigDimLe (P := P) sem (obsAB')
        (targetAB') (h := h) n) :
    (¬ LeftObsPredictsJointStep' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
        (targetA := targetA) (targetB := targetB) (h := h) (k := k) step)
      ∧ (¬ RightObsPredictsJointStep' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
        (targetA := targetA) (targetB := targetB) (h := h) (k := k) step)
      ∧ RefiningLift (P := P) sem (obsAB')
        (targetAB') h step n := by
  have hNoL :=
    not_leftObsPredictsJointStep_of_stepSeparatesJointFiber
      (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step) hSepAB
  have hNoR :=
    not_rightObsPredictsJointStep_of_stepSeparatesJointFiber
      (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step) hSepAB
  have hLift :=
    refiningLift_of_jointCompatSigDimLe
      (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step)
      (n := n) hSigAB
  exact ⟨hNoL, hNoR, hLift⟩

theorem double_noGo_of_lagEvent
    {kA kB : P}
    {pA qA : HistoryGraph.Path h kA} (αA : HistoryGraph.Deformation pA qA)
    {pB qB : HistoryGraph.Path h kB} (αB : HistoryGraph.Deformation pB qB)
    (hLagA : LagEvent (P := P) sem obsA targetA αA step)
    (hLagB : LagEvent (P := P) sem obsB targetB αB step) :
    (¬ ObsPredictsStep (P := P) sem obsA targetA step) ∧
      (¬ ObsPredictsStep (P := P) sem obsB targetB step) := by
  refine ⟨?_, ?_⟩
  · exact not_obsPredictsStep_of_lagEvent (P := P) sem obsA targetA αA step hLagA
  · exact not_obsPredictsStep_of_lagEvent (P := P) sem obsB targetB αB step hLagB

theorem double_noGo_to_separation_and_minimalJointLift
    {NA NB n : Nat}
    (eA : Equiv (FiberPt (P := P) obsA targetA h) (Fin NA))
    (eB : Equiv (FiberPt (P := P) obsB targetB h) (Fin NB))
    (decA : ∀ x : FiberPt (P := P) obsA targetA h,
      Decidable (Compatible (P := P) sem obsA targetA step x))
    (decB : ∀ x : FiberPt (P := P) obsB targetB h,
      Decidable (Compatible (P := P) sem obsB targetB step x))
    (hNoA : ¬ ObsPredictsStep (P := P) sem obsA targetA step)
    (hNoB : ¬ ObsPredictsStep (P := P) sem obsB targetB step)
    (hDimAB : CompatDimEq (P := P) sem (obsAB')
      (targetAB') step n) :
    StepSeparatesFiber (P := P) sem obsA targetA step
      ∧ StepSeparatesFiber (P := P) sem obsB targetB step
      ∧ (RefiningLift (P := P) sem (obsAB')
          (targetAB') h step n
        ∧ ∀ m : Nat, m < n →
            ¬ RefiningLift (P := P) sem (obsAB')
              (targetAB') h step m) := by
  have hSepA :
      StepSeparatesFiber (P := P) sem obsA targetA step :=
    stepSeparatesFiber_of_not_obsPredictsStep_of_equivFin
      (P := P) (sem := sem) (obs := obsA) (target_obs := targetA)
      (h := h) (k := k) (step := step) eA decA hNoA
  have hSepB :
      StepSeparatesFiber (P := P) sem obsB targetB step :=
    stepSeparatesFiber_of_not_obsPredictsStep_of_equivFin
      (P := P) (sem := sem) (obs := obsB) (target_obs := targetB)
      (h := h) (k := k) (step := step) eB decB hNoB
  have hLift :
      RefiningLift (P := P) sem (obsAB')
        (targetAB') h step n :=
    refiningLift_of_compatDimEq
      (P := P) sem (obsAB')
      (targetAB') step n hDimAB
  have hNoSmaller :
      ∀ m : Nat, m < n →
        ¬ RefiningLift (P := P) sem (obsAB')
          (targetAB') h step m :=
    no_smaller_refiningLift_of_compatDimEq
      (P := P) sem (obsAB')
      (targetAB') step n hDimAB
  exact ⟨hSepA, hSepB, ⟨hLift, hNoSmaller⟩⟩

theorem jointLift2_yields_causalSignature2
    (hSepAB :
      StepSeparatesFiber (P := P) sem (obsAB')
        (targetAB') step)
    (hDimAB2 : CompatDimEq (P := P) sem (obsAB')
      (targetAB') step 2) :
    CausalSignature2 (P := P) sem (obsAB')
      (targetAB') (h := h) step := by
  have hLift2 :
      RefiningLift (P := P) sem (obsAB')
        (targetAB') h step 2 :=
    refiningLift_of_compatDimEq
      (P := P) sem (obsAB')
      (targetAB') step 2 hDimAB2
  exact causalSignature2_of_stepSeparatesFiber_of_refiningLift2
    (P := P) (sem := sem)
    (obs := (obsAB'))
    (target_obs := (targetAB'))
    (h := h) (k := k) (step := step) hSepAB hLift2

theorem endToEnd_joint
    {n : Nat}
    (hSepAB :
      StepSeparatesFiber (P := P) sem (obsAB')
        (targetAB') step)
    (hDimAB : CompatDimEq (P := P) sem (obsAB')
      (targetAB') step n) :
    (¬ LeftObsPredictsJointStep' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
        (targetA := targetA) (targetB := targetB) (h := h) (k := k) step)
      ∧
      (¬ RightObsPredictsJointStep' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
        (targetA := targetA) (targetB := targetB) (h := h) (k := k) step)
      ∧
      (RefiningLift (P := P) sem (obsAB')
          (targetAB') h step n
        ∧ ∀ m : Nat, m < n →
            ¬ RefiningLift (P := P) sem (obsAB')
              (targetAB') h step m) := by
  refine ⟨?_, ?_, ?_⟩
  · exact not_leftObsPredictsJointStep_of_stepSeparatesJointFiber
      (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step hSepAB
  · exact not_rightObsPredictsJointStep_of_stepSeparatesJointFiber
      (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step hSepAB
  · have hLift :
        RefiningLift (P := P) sem (obsAB')
          (targetAB') h step n :=
      refiningLift_of_compatDimEq
        (P := P) sem (obsAB')
        (targetAB') step n hDimAB
    have hNoSmaller :
        ∀ m : Nat, m < n →
          ¬ RefiningLift (P := P) sem (obsAB')
            (targetAB') h step m :=
      no_smaller_refiningLift_of_compatDimEq
        (P := P) sem (obsAB')
        (targetAB') step n hDimAB
    exact ⟨hLift, hNoSmaller⟩

theorem not_mediatorDescendsLeft_of_stepSeparatesJointFiber
    {n : Nat}
    (hSep :
      StepSeparatesFiber (P := P) sem (obsAB')
        (targetAB') step)
    (L : RefiningLiftData (P := P) sem (obsAB')
      (targetAB') h step n) :
    ¬ MediatorDescendsLeft' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step L := by
  apply not_mediatorDescendsLeft_of_not_leftObsPredictsJointStep
    (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
    (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step) L
  exact not_leftObsPredictsJointStep_of_stepSeparatesJointFiber
    (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
    (targetA := targetA) (targetB := targetB) (h := h) (k := k) step hSep

theorem not_mediatorDescendsRight_of_stepSeparatesJointFiber
    {n : Nat}
    (hSep :
      StepSeparatesFiber (P := P) sem (obsAB')
        (targetAB') step)
    (L : RefiningLiftData (P := P) sem (obsAB')
      (targetAB') h step n) :
    ¬ MediatorDescendsRight' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step L := by
  apply not_mediatorDescendsRight_of_not_rightObsPredictsJointStep
    (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
    (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step) L
  exact not_rightObsPredictsJointStep_of_stepSeparatesJointFiber
    (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
    (targetA := targetA) (targetB := targetB) (h := h) (k := k) step hSep

theorem endToEnd_full
    {kA kB : P}
    {pA qA : HistoryGraph.Path h kA} (αA : HistoryGraph.Deformation pA qA)
    {pB qB : HistoryGraph.Path h kB} (αB : HistoryGraph.Deformation pB qB)
    {NA NB n : Nat}
    (eA : Equiv (FiberPt (P := P) obsA targetA h) (Fin NA))
    (eB : Equiv (FiberPt (P := P) obsB targetB h) (Fin NB))
    (decA : ∀ x : FiberPt (P := P) obsA targetA h,
      Decidable (Compatible (P := P) sem obsA targetA step x))
    (decB : ∀ x : FiberPt (P := P) obsB targetB h,
      Decidable (Compatible (P := P) sem obsB targetB step x))
    (hLagA : LagEvent (P := P) sem obsA targetA αA step)
    (hLagB : LagEvent (P := P) sem obsB targetB αB step)
    (hSepAB :
      StepSeparatesFiber (P := P) sem (obsAB')
        (targetAB') step)
    (hDimAB : CompatDimEq (P := P) sem (obsAB')
      (targetAB') step n) :
    StepSeparatesFiber (P := P) sem obsA targetA step
      ∧ StepSeparatesFiber (P := P) sem obsB targetB step
      ∧ (¬ LeftObsPredictsJointStep' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
          (targetA := targetA) (targetB := targetB) (h := h) (k := k) step)
      ∧ (¬ RightObsPredictsJointStep' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
          (targetA := targetA) (targetB := targetB) (h := h) (k := k) step)
      ∧ (RefiningLift (P := P) sem (obsAB')
          (targetAB') h step n
        ∧ ∀ m : Nat, m < n →
            ¬ RefiningLift (P := P) sem (obsAB')
              (targetAB') h step m) := by
  have hNo := double_noGo_of_lagEvent
    (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
    (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step)
    (kA := kA) (kB := kB) (αA := αA) (αB := αB) hLagA hLagB
  have hSepMin :=
    double_noGo_to_separation_and_minimalJointLift
      (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step)
      (NA := NA) (NB := NB) (n := n) eA eB decA decB hNo.1 hNo.2 hDimAB
  have hJoint :=
    endToEnd_joint
      (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step)
      (n := n) hSepAB hDimAB
  refine ⟨hSepMin.1, hSepMin.2.1, ?_, ?_, hSepMin.2.2⟩
  · exact hJoint.1
  · exact hJoint.2.1

theorem endToEnd_full_with_causalSignature2
    {kA kB : P}
    {pA qA : HistoryGraph.Path h kA} (αA : HistoryGraph.Deformation pA qA)
    {pB qB : HistoryGraph.Path h kB} (αB : HistoryGraph.Deformation pB qB)
    {NA NB : Nat}
    (eA : Equiv (FiberPt (P := P) obsA targetA h) (Fin NA))
    (eB : Equiv (FiberPt (P := P) obsB targetB h) (Fin NB))
    (decA : ∀ x : FiberPt (P := P) obsA targetA h,
      Decidable (Compatible (P := P) sem obsA targetA step x))
    (decB : ∀ x : FiberPt (P := P) obsB targetB h,
      Decidable (Compatible (P := P) sem obsB targetB step x))
    (hLagA : LagEvent (P := P) sem obsA targetA αA step)
    (hLagB : LagEvent (P := P) sem obsB targetB αB step)
    (hSepAB :
      StepSeparatesFiber (P := P) sem (obsAB')
        (targetAB') step)
    (hDimAB2 : CompatDimEq (P := P) sem (obsAB')
      (targetAB') step 2) :
    (StepSeparatesFiber (P := P) sem obsA targetA step
      ∧ StepSeparatesFiber (P := P) sem obsB targetB step
      ∧ (¬ LeftObsPredictsJointStep' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
          (targetA := targetA) (targetB := targetB) (h := h) (k := k) step)
      ∧ (¬ RightObsPredictsJointStep' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
          (targetA := targetA) (targetB := targetB) (h := h) (k := k) step)
      ∧ (RefiningLift (P := P) sem (obsAB')
          (targetAB') h step 2
        ∧ ∀ m : Nat, m < 2 →
            ¬ RefiningLift (P := P) sem (obsAB')
              (targetAB') h step m))
    ∧ CausalSignature2 (P := P) sem (obsAB')
        (targetAB') (h := h) step := by
  refine ⟨?_, ?_⟩
  · exact endToEnd_full
      (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step)
      (kA := kA) (kB := kB) (αA := αA) (αB := αB)
      (NA := NA) (NB := NB) (n := 2) eA eB decA decB hLagA hLagB hSepAB hDimAB2
  · exact jointLift2_yields_causalSignature2
      (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step)
      hSepAB hDimAB2

theorem jointIrreducibleMediationProfile_of_sep_and_dim
    {n : Nat}
    (hSepAB :
      StepSeparatesFiber (P := P) sem (obsAB')
        (targetAB') step)
    (hDimAB : CompatDimEq (P := P) sem (obsAB')
      (targetAB') step n) :
    JointIrreducibleMediationProfile (P := P) sem obsA obsB targetA targetB step n := by
  have hJoint :=
    endToEnd_joint
      (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step)
      (n := n) hSepAB hDimAB
  exact ⟨hSepAB, hJoint.1, hJoint.2.1, hDimAB⟩

theorem not_mediatorDescendsLeft_of_jointIrreducibleMediationProfile
    {n : Nat}
    (hProf : JointIrreducibleMediationProfile (P := P) sem obsA obsB targetA targetB step n)
    (L : RefiningLiftData (P := P) sem (obsAB')
      (targetAB') h step n) :
    ¬ MediatorDescendsLeft' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step L := by
  exact not_mediatorDescendsLeft_of_stepSeparatesJointFiber
    (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
    (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step)
    hProf.1 L

theorem not_mediatorDescendsRight_of_jointIrreducibleMediationProfile
    {n : Nat}
    (hProf : JointIrreducibleMediationProfile (P := P) sem obsA obsB targetA targetB step n)
    (L : RefiningLiftData (P := P) sem (obsAB')
      (targetAB') h step n) :
    ¬ MediatorDescendsRight' (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step L := by
  exact not_mediatorDescendsRight_of_stepSeparatesJointFiber
    (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
    (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step)
    hProf.1 L

theorem causalSignature2_of_jointIrreducibleMediationProfile2
    (hProf : JointIrreducibleMediationProfile (P := P) sem obsA obsB targetA targetB step 2) :
    CausalSignature2 (P := P) sem (obsAB')
      (targetAB') (h := h) step := by
  exact jointLift2_yields_causalSignature2
    (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
    (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step)
    hProf.1 hProf.2.2.2

end TwoInterfaces

end DynamicsOnly
end Examples
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.Examples.DynamicsOnly.stepSeparatesFiber_of_not_obsPredictsStep_of_equivFin
#print axioms PrimitiveHolonomy.Examples.DynamicsOnly.causalSignature2_of_stepSeparatesFiber_of_refiningLift2
#print axioms PrimitiveHolonomy.Examples.DynamicsOnly.endToEnd_full
#print axioms PrimitiveHolonomy.Examples.DynamicsOnly.jointIrreducibleMediationProfile_of_sep_and_dim
/- AXIOM_AUDIT_END -/
