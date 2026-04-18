import COFRS.Dynamics
import COFRS.Examples.GodelByCode

/-!
# Core theorem chain (Lean): diagonalization ⇒ no-go obs-only ⇒ forced finite lift ⇒ testable causal signature

This file is a **single place** where the project’s thesis sentence is expressed as Lean theorems.
It does not change the repository’s objective; it only makes the objective *checkable*.

We separate three layers:

1. **Static regime destroyed (obs-only no-go).**
   A separating witness (`LagEvent`, hence `StepSeparatesFiber`) implies
   `¬ ObsPredictsStep` (universal quantification over all obs-only decision rules).

2. **Forced factorization through a mediator (minimal finite lift).**
   Exact compatibility dimension (`CompatDimEq … n`) is equivalent to existence of a canonical
   `RefiningLift … n` on the observable fiber.

3. **Causality as a testable signature.**
   When a step separates a fiber and a `RefiningLiftData … 2` exists, then:
   - any “ablation” that removes the `Fin 2` supplement (constant readout) cannot remain correct;
   - a “permutation” intervention on the `Fin 2` mediator (swap) changes the readout on some fiber point.

The last item is deliberately stated **on the fiber**, to match the rest of COFRS.
All proofs are constructive; the `AXIOM_AUDIT` block at the end must report no axioms.
-/

namespace PrimitiveHolonomy
namespace Examples

open PrimitiveHolonomy

section WithHistoryGraph

variable {P : Type u} [HistoryGraph P]

section Generic

universe w

variable {S V : Type w}
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
  rcases hSep with ⟨x0, x1, hxne, hx0, hx1⟩

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
      -- same `Fin 2` class ⇒ same predicate value
      dsimp [LiftReadout]
      exact iff_of_eq (congrArg L.predFin hσ)
    exact h1 (hpredEq.mp h0)

  -- Helper: every `Fin 2` value has `val = 0` or `val = 1`.
  have fin2_val_eq_zero_or_eq_one : ∀ i : Fin 2, i.val = 0 ∨ i.val = 1 := by
    intro i
    cases i with
    | mk v hv =>
        cases v with
        | zero =>
            left
            rfl
        | succ v' =>
            have hv' : v' = 0 := by
              have : v' < 1 := by
                have : Nat.succ v' < 2 := hv
                exact Nat.lt_of_succ_lt_succ this
              exact nat_eq_zero_of_lt_one this
            subst hv'
            right
            rfl

  have hswap : fin2Swap ((L.extObs x0).2) = (L.extObs x1).2 := by
    rcases fin2_val_eq_zero_or_eq_one ((L.extObs x0).2) with h0v | h0v
    · -- `x0` has val 0, so `x1` must have val 1.
      have h1v : ((L.extObs x1).2).val = 1 := by
        rcases fin2_val_eq_zero_or_eq_one ((L.extObs x1).2) with h10 | h11
        ·
          exfalso
          apply hσne
          apply Fin.ext
          exact h0v.trans h10.symm
        · exact h11
      apply Fin.ext
      -- swap sends 0 to 1
      have hSwap0 : fin2Swap ((L.extObs x0).2) = finOne2 := by
        dsimp [fin2Swap]
        rw [if_pos h0v]
      have : (fin2Swap ((L.extObs x0).2)).val = 1 := by
        rw [hSwap0]
        rfl
      exact this.trans h1v.symm
    · -- `x0` has val 1, so `x1` must have val 0.
      have h1v : ((L.extObs x1).2).val = 0 := by
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
  -- `LiftReadoutPerm x0` is the predicate value at the swapped class (i.e. `x1`’s class).
  have hPerm0 : LiftReadoutPerm (P := P) sem obs target_obs step L x0 ↔
      LiftReadout (P := P) sem obs target_obs step L x1 := by
    dsimp [LiftReadoutPerm, LiftReadout]
    exact iff_of_eq (congrArg L.predFin hswap)
  have hPermFalse : ¬ LiftReadoutPerm (P := P) sem obs target_obs step L x0 := by
    intro hPerm
    exact h1 (hPerm0.mp hPerm)
  -- original is true, permuted is false, so they are not equivalent
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

structure CausalSignature2Data : Type w where
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

end Generic

section DiagonalInstance

open HolonomicGodelByCode

variable (Provable : Nat → Prop)
variable (U : Nat → Nat → Bool)
variable (D : DiagonalCode (Provable := Provable) (U := U))

theorem diagonalization_yields_causalSignature2
    (e : Nat) :
    CausalSignature2 (P := Nat)
      (@semantics (Provable := Provable)) obs target_obs
      (h := g (D := D) e)
      (PPath.step (g (D := D) e)) := by
  -- separating witness comes from the diagonal lag event
  have hSep :
      StepSeparatesFiber (P := Nat)
        (@semantics (Provable := Provable)) obs target_obs
        (h := g (D := D) e) (k := g (D := D) e)
        (PPath.step (g (D := D) e)) :=
    stepSeparatesFiber_of_lagEvent
      (P := Nat)
      (sem := @semantics (Provable := Provable))
      (obs := obs) (target_obs := target_obs)
      (α := α (D := D) e)
      (step := PPath.step (g (D := D) e))
      (lagEvent_at_diag (Provable := Provable) (U := U) (D := D) e)
  -- a `Fin 2` lift comes from the diagonal dimension upper bound
  have hLift :
      RefiningLift (P := Nat)
        (@semantics (Provable := Provable)) obs target_obs
        (g (D := D) e)
        (PPath.step (g (D := D) e)) 2 := by
    have hDim :
        CompatDimLe (P := Nat)
          (@semantics (Provable := Provable)) obs target_obs
          (h := g (D := D) e) (k := g (D := D) e)
          (PPath.step (g (D := D) e)) 2 :=
      diag_compatDimLe_two_step (Provable := Provable) (U := U) (D := D) e
    exact (compatDimLe_iff_refiningLift
      (P := Nat)
      (sem := @semantics (Provable := Provable))
      (obs := obs) (target_obs := target_obs)
      (step := (PPath.step (g (D := D) e)))
      (n := 2)).1 hDim
  exact causalSignature2_of_stepSeparatesFiber_of_refiningLift2
    (P := Nat)
    (sem := @semantics (Provable := Provable))
    (obs := obs) (target_obs := target_obs)
    (h := g (D := D) e)
    (step := PPath.step (g (D := D) e))
    hSep hLift

theorem diagonalization_yields_minimalRefiningLift2
    (e : Nat) :
    RefiningLift (P := Nat)
      (@semantics (Provable := Provable)) obs target_obs
      (g (D := D) e)
      (PPath.step (g (D := D) e)) 2
    ∧
    (∀ m : Nat, m < 2 →
      ¬ RefiningLift (P := Nat)
          (@semantics (Provable := Provable)) obs target_obs
          (g (D := D) e)
          (PPath.step (g (D := D) e)) m) := by
  -- `Fin 2` lift from the diagonal compatibility dimension upper bound
  have hLift2 :
      RefiningLift (P := Nat)
        (@semantics (Provable := Provable)) obs target_obs
        (g (D := D) e)
        (PPath.step (g (D := D) e)) 2 := by
    have hDim :
        CompatDimLe (P := Nat)
          (@semantics (Provable := Provable)) obs target_obs
          (h := g (D := D) e) (k := g (D := D) e)
          (PPath.step (g (D := D) e)) 2 :=
      diag_compatDimLe_two_step (Provable := Provable) (U := U) (D := D) e
    exact (compatDimLe_iff_refiningLift
      (P := Nat)
      (sem := @semantics (Provable := Provable))
      (obs := obs) (target_obs := target_obs)
      (step := (PPath.step (g (D := D) e)))
      (n := 2)).1 hDim

  -- Dimension "exactly 2" in the (2 vs 1) sense, from the diagonal witness package.
  have hEqTwo :
      CompatDimEqTwo (P := Nat)
        (@semantics (Provable := Provable)) obs target_obs
        (h := g (D := D) e) (k := g (D := D) e)
        (PPath.step (g (D := D) e)) :=
    diag_compatDimEqTwo_step (Provable := Provable) (U := U) (D := D) e

  refine ⟨hLift2, ?_⟩
  intro m hm
  cases m with
  | zero =>
      -- No lift of size 0 can exist: `Fin 0` is empty, but the diagonal fiber is inhabited.
      intro hLift0
      rcases hLift0 with ⟨L⟩
      have : False := Fin.elim0 ((L.extObs (x (D := D) e)).2)
      exact this.elim
  | succ m' =>
      -- If `m < 2` and `m = succ m'`, then `m = 1`.
      have hm' : m' < 1 := Nat.lt_of_succ_lt_succ hm
      have hm'' : m' = 0 := nat_eq_zero_of_lt_one hm'
      subst hm''
      -- Contradict `¬ CompatDimLe ... 1` transported through the lift equivalence.
      intro hLift1
      have hDim1 :
          CompatDimLe (P := Nat)
            (@semantics (Provable := Provable)) obs target_obs
            (h := g (D := D) e) (k := g (D := D) e)
            (PPath.step (g (D := D) e)) 1 :=
        (compatDimLe_iff_refiningLift
          (P := Nat)
          (sem := @semantics (Provable := Provable))
          (obs := obs) (target_obs := target_obs)
          (step := (PPath.step (g (D := D) e)))
          (n := 1)).2 hLift1
      exact hEqTwo.2 hDim1

end DiagonalInstance

section DiagonalPackage

open HolonomicGodelByCode

variable (Provable : Nat → Prop)
variable (U : Nat → Nat → Bool)
variable (D : DiagonalCode (Provable := Provable) (U := U))

theorem diagonalization_yields_minimalLift2_and_causalSignature2
    (e : Nat) :
    (RefiningLift (P := Nat)
        (@semantics (Provable := Provable)) obs target_obs
        (g (D := D) e)
        (PPath.step (g (D := D) e)) 2
      ∧
      (∀ m : Nat, m < 2 →
        ¬ RefiningLift (P := Nat)
            (@semantics (Provable := Provable)) obs target_obs
            (g (D := D) e)
            (PPath.step (g (D := D) e)) m))
    ∧
    CausalSignature2 (P := Nat)
      (@semantics (Provable := Provable)) obs target_obs
      (h := g (D := D) e)
      (PPath.step (g (D := D) e)) := by
  refine ⟨
    diagonalization_yields_minimalRefiningLift2 (Provable := Provable) (U := U) (D := D) e,
    diagonalization_yields_causalSignature2 (Provable := Provable) (U := U) (D := D) e⟩

end DiagonalPackage

end WithHistoryGraph

end Examples
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.Examples.no_constant_classifier_of_stepSeparatesFiber
#print axioms PrimitiveHolonomy.Examples.perm_changes_readout_of_stepSeparatesFiber
#print axioms PrimitiveHolonomy.Examples.ablation_breaks_correctness_of_stepSeparatesFiber
#print axioms PrimitiveHolonomy.Examples.causalSignature2_of_stepSeparatesFiber_of_refiningLift2
#print axioms PrimitiveHolonomy.Examples.diagonalization_yields_causalSignature2
#print axioms PrimitiveHolonomy.Examples.diagonalization_yields_minimalRefiningLift2
#print axioms PrimitiveHolonomy.Examples.diagonalization_yields_minimalLift2_and_causalSignature2
/- AXIOM_AUDIT_END -/
