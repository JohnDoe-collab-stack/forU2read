import COFRS.Dynamics
import COFRS.Examples.IndependenceToAutoreflexiveQueryBridge

/-!
# Independence to autoreflexive query, then to `CompatDimEq` / `RefiningLift` and `Sig`

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

We then add a global layer (still on a fixed left fiber):

* a hypothesis that the response channel determines the full future signature `Sig`,
* a constructive proof that this yields a finite global compression `CompatSigDimLe … n`,
* and a lemma showing that, for the minimal query architecture, the witness summary is read from
  the post-query state.

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

section SigBridge

variable {S VA VB : Type w}
variable (sem : Semantics P S)
variable (obsA : S → VA) (obsB : S → VB)
variable (targetA : P → VA)
variable {h : P}

/--
Global correctness on a fixed left fiber:
there exists a predicate on the response channel that decides compatibility for every future step.

This is the hypothesis needed to connect the query-layer mediator to the canonical signature `Sig`.
-/
def CorrectSigOnLeftFiber
    (predB : VB → Future (P := P) h → Prop) : Prop :=
  ∀ x : FiberPt (P := P) obsA targetA h, ∀ fut : Future (P := P) h,
    predB (obsB x.1) fut ↔ CompatibleFuture (P := P) sem obsA targetA fut x

theorem sigFactorsThrough_obsB_of_correctSigOnLeftFiber
    (predB : VB → Future (P := P) h → Prop)
    (hCorr : CorrectSigOnLeftFiber (P := P) (sem := sem)
      (obsA := obsA) (obsB := obsB) (targetA := targetA) (h := h) predB) :
    SigFactorsThrough (P := P) sem obsA targetA (h := h) (fun x => obsB x.1) := by
  apply sigFactorsThrough_of_summary_correct (P := P) sem obsA targetA (h := h)
    (σ := fun x => obsB x.1) (pred := predB)
  intro x fut
  simpa [CorrectSigOnLeftFiber] using (hCorr x fut)

theorem sigFactorsThrough_encode_obsB_of_correctSigOnLeftFiber_of_encode_injective
    {n : Nat} (encode : VB → Fin n) (hEncode : Function.Injective encode)
    (predB : VB → Future (P := P) h → Prop)
    (hCorr : CorrectSigOnLeftFiber (P := P) (sem := sem)
      (obsA := obsA) (obsB := obsB) (targetA := targetA) (h := h) predB) :
    SigFactorsThrough (P := P) sem obsA targetA (h := h) (fun x => encode (obsB x.1)) := by
  let predFin : Fin n → Future (P := P) h → Prop :=
    fun i fut => ∃ v : VB, encode v = i ∧ predB v fut
  apply sigFactorsThrough_of_summary_correct (P := P) sem obsA targetA (h := h)
    (σ := fun x => encode (obsB x.1)) (pred := predFin)
  intro x fut
  constructor
  · rintro ⟨v, hv, hvPred⟩
    have hv' : encode v = encode (obsB x.1) := by simpa using hv
    have : v = obsB x.1 := hEncode hv'
    subst this
    exact (hCorr x fut).1 hvPred
  · intro hComp
    have : predB (obsB x.1) fut := (hCorr x fut).2 hComp
    exact ⟨obsB x.1, rfl, this⟩

theorem compatSigDimLe_of_correctSigOnLeftFiber_of_encode_injective
    {n : Nat} (encode : VB → Fin n) (hEncode : Function.Injective encode)
    (predB : VB → Future (P := P) h → Prop)
    (hCorr : CorrectSigOnLeftFiber (P := P) (sem := sem)
      (obsA := obsA) (obsB := obsB) (targetA := targetA) (h := h) predB) :
    CompatSigDimLe (P := P) sem obsA targetA (h := h) n := by
  refine ⟨(fun x => encode (obsB x.1)),
    (fun i fut => ∃ v : VB, encode v = i ∧ predB v fut), ?_⟩
  intro x fut
  constructor
  · rintro ⟨v, hv, hvPred⟩
    have hv' : encode v = encode (obsB x.1) := by simpa using hv
    have : v = obsB x.1 := hEncode hv'
    subst this
    exact (hCorr x fut).1 hvPred
  · intro hComp
    have : predB (obsB x.1) fut := (hCorr x fut).2 hComp
    exact ⟨obsB x.1, rfl, this⟩

theorem sigFactorsThrough_encode_postStateUnder_true_of_correctSigOnLeftFiber_of_encode_injective
    (defaultB : VB) (decAB : VA × VB → Bool)
    {n : Nat} (encode : VB → Fin n) (hEncode : Function.Injective encode)
    (predB : VB → Future (P := P) h → Prop)
    (hCorr : CorrectSigOnLeftFiber (P := P) (sem := sem)
      (obsA := obsA) (obsB := obsB) (targetA := targetA) (h := h) predB) :
    let Arch :=
      queryRepairBySecondMargin (P := P) (obsA := obsA) (obsB := obsB) (targetA := targetA)
        (h0 := h) (defaultB := defaultB) (decAB := decAB)
    SigFactorsThrough (P := P) sem obsA targetA (h := h)
      (fun world => encode (AutoreflexiveQueryArchitecture.postStateUnder Arch world true).2) := by
  intro Arch
  have hFac :
      SigFactorsThrough (P := P) sem obsA targetA (h := h) (fun x => encode (obsB x.1)) :=
    sigFactorsThrough_encode_obsB_of_correctSigOnLeftFiber_of_encode_injective
      (P := P) (sem := sem) (obsA := obsA) (obsB := obsB) (targetA := targetA) (h := h)
      (encode := encode) hEncode predB hCorr
  intro x x' hσ
  -- `postStateUnder Arch _ true` stores `obsB` in its second component, so `σ` equality reduces to
  -- equality of `encode (obsB _)`.
  have hσ' : encode (obsB x.1) = encode (obsB x'.1) := by
    simpa [Arch] using hσ
  exact hFac hσ'

end SigBridge

end Examples
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.Examples.compatDimLe_two_of_correctOnLeftFiber
#print axioms PrimitiveHolonomy.Examples.compatDimEq_two_of_stepSeparatesFiber_of_correctOnLeftFiber
#print axioms PrimitiveHolonomy.Examples.refiningLift_two_of_stepSeparatesFiber_of_correctOnLeftFiber
#print axioms PrimitiveHolonomy.Examples.sigFactorsThrough_obsB_of_correctSigOnLeftFiber
#print axioms PrimitiveHolonomy.Examples.sigFactorsThrough_encode_obsB_of_correctSigOnLeftFiber_of_encode_injective
#print axioms PrimitiveHolonomy.Examples.compatSigDimLe_of_correctSigOnLeftFiber_of_encode_injective
#print axioms PrimitiveHolonomy.Examples.sigFactorsThrough_encode_postStateUnder_true_of_correctSigOnLeftFiber_of_encode_injective
/- AXIOM_AUDIT_END -/
