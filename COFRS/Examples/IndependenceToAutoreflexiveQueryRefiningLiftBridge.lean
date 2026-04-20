import COFRS.Dynamics
import COFRS.Examples.IndependenceToAutoreflexiveQueryBridge

/-!
# Independence to autoreflexive query, then to `CompatDimEq` / `RefiningLift`

This file is a bridge from the "repair by querying a second margin" setup to the step-local
finite-mediation layer in `COFRS/Dynamics.lean`.

Scope:

* we stay on a fixed left fiber `FiberPt obsA targetA h`,
* we assume a step-local obstruction `StepSeparatesFiber` on `obsA`,
* and a step-local correctness hypothesis stating that `decAB (targetA h, obsB x)` decides
  `Compatible … step x` on that left fiber.

From these, we build:

* an explicit finite summary `σ : fiber(h) → Fin 2` deciding compatibility,
* the lower bound `¬ CompatDimLe … 1`,
* therefore `CompatDimEq … 2`, and a corresponding `RefiningLift … 2`.

All proofs are constructive; see the `AXIOM_AUDIT` block at the end.
-/

namespace PrimitiveHolonomy
namespace Examples

universe u w

variable {P : Type u} [HistoryGraph P]

section RefiningLiftBridge

variable {S VA VB : Type w}
variable (sem : Semantics P S)
variable (obsA : S → VA) (obsB : S → VB)
variable (targetA : P → VA)
variable {h k : P} (step : HistoryGraph.Path h k)
variable (decAB : VA × VB → Bool)

abbrev fin2OfBool : Bool → Fin 2
  | false => ⟨0, by decide⟩
  | true => ⟨1, by decide⟩

theorem compatDimLe_two_of_correctOnLeftFiber
    (hCorr :
      QueryRepairBySecondMargin.CorrectOnLeftFiber (P := P)
        (S := S) (VA := VA) (VB := VB)
        sem obsA obsB targetA h step decAB) :
    CompatDimLe (P := P) sem obsA targetA step 2 := by
  refine ⟨(fun x => fin2OfBool (decAB (targetA h, obsB x.1))), (fun i => i = fin2OfBool true), ?_⟩
  intro x
  constructor
  · intro hC
    have hDec : decAB (targetA h, obsB x.1) = true := (hCorr x).2 hC
    exact congrArg fin2OfBool hDec
  · intro hPred
    -- `σ x` is `fin2OfBool (decAB ...)`, and `pred` asserts it equals `fin2OfBool true`,
    -- hence the boolean must be `true`.
    have hEq : fin2OfBool (decAB (targetA h, obsB x.1)) = fin2OfBool true := hPred
    cases hb : decAB (targetA h, obsB x.1) with
    | false =>
        -- contradiction: `fin2OfBool false = fin2OfBool true`
        have hEq' := hEq
        rw [hb] at hEq'
        cases hEq'
    | true =>
        have : decAB (targetA h, obsB x.1) = true := hb
        exact (hCorr x).1 this

theorem not_compatDimLe_zero_of_stepSeparatesFiber
    (hSep : StepSeparatesFiber (P := P) sem obsA targetA step) :
    ¬ CompatDimLe (P := P) sem obsA targetA step 0 := by
  intro hDim
  rcases hSep with ⟨x, _x', _hne, _hx, _hx'⟩
  rcases hDim with ⟨σ, _pred, _hcorr⟩
  exact Fin.elim0 (σ x)

theorem compatDimEq_two_of_stepSeparatesFiber_of_correctOnLeftFiber
    (hSep : StepSeparatesFiber (P := P) sem obsA targetA step)
    (hCorr :
      QueryRepairBySecondMargin.CorrectOnLeftFiber (P := P)
        (S := S) (VA := VA) (VB := VB)
        sem obsA obsB targetA h step decAB) :
    CompatDimEq (P := P) sem obsA targetA step 2 := by
  refine ⟨compatDimLe_two_of_correctOnLeftFiber
      (P := P) (S := S) (VA := VA) (VB := VB)
      (sem := sem) (obsA := obsA) (obsB := obsB) (targetA := targetA)
      (h := h) (step := step) (decAB := decAB) hCorr, ?_⟩
  intro m hm
  cases m with
  | zero =>
      -- `m = 0`
      simpa using (not_compatDimLe_zero_of_stepSeparatesFiber
        (P := P) (sem := sem) (obsA := obsA) (targetA := targetA) (step := step) hSep)
  | succ m =>
      cases m with
      | zero =>
          -- `m = 1`
          have : ¬ CompatDimLe (P := P) sem obsA targetA step 1 :=
            not_compatDimLe_one_of_stepSeparatesFiber (P := P) sem obsA targetA step hSep
          simpa using this
      | succ m =>
          -- `m ≥ 2`, contradicts `Nat.succ (Nat.succ m) < 2`
          have hge : 2 ≤ Nat.succ (Nat.succ m) :=
            Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le m))
          have : ¬ Nat.succ (Nat.succ m) < 2 := Nat.not_lt_of_ge hge
          intro _hDim
          exact this hm

theorem refiningLift_two_of_stepSeparatesFiber_of_correctOnLeftFiber
    (hSep : StepSeparatesFiber (P := P) sem obsA targetA step)
    (hCorr :
      QueryRepairBySecondMargin.CorrectOnLeftFiber (P := P)
        (S := S) (VA := VA) (VB := VB)
        sem obsA obsB targetA h step decAB) :
    RefiningLift (P := P) sem obsA targetA h step 2 := by
  have hEq :
      CompatDimEq (P := P) sem obsA targetA step 2 :=
    compatDimEq_two_of_stepSeparatesFiber_of_correctOnLeftFiber
      (P := P) (S := S) (VA := VA) (VB := VB)
      (sem := sem) (obsA := obsA) (obsB := obsB) (targetA := targetA)
      (h := h) (k := k) (step := step) (decAB := decAB) hSep hCorr
  exact refiningLift_of_compatDimEq (P := P) sem obsA targetA step 2 hEq

end RefiningLiftBridge

end Examples
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.Examples.compatDimLe_two_of_correctOnLeftFiber
#print axioms PrimitiveHolonomy.Examples.compatDimEq_two_of_stepSeparatesFiber_of_correctOnLeftFiber
#print axioms PrimitiveHolonomy.Examples.refiningLift_two_of_stepSeparatesFiber_of_correctOnLeftFiber
/- AXIOM_AUDIT_END -/
