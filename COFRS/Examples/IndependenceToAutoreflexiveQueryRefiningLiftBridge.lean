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

variable {P : Type u}

section RefiningLiftBridge

variable [HistoryGraph P]

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

section PostStateReadback

variable {S VA VB : Type w}
variable (obsA : S → VA) (obsB : S → VB)
variable (targetA : P → VA)
variable {h : P}

/--
In the minimal query architecture, the post-query state (under action `true`) stores the response
in the second component. This makes any summary of the response channel readable from the
post-query state.
-/
theorem sigma_from_postStateUnder_true_eq
    (defaultB : VB) (decAB : VA × VB → Bool)
    {n : Nat} (encode : VB → Fin n)
    (world : FiberPt (P := P) obsA targetA h) :
    let Arch :=
      queryRepairBySecondMargin (P := P) (obsA := obsA) (obsB := obsB) (targetA := targetA)
        (h0 := h) (defaultB := defaultB) (decAB := decAB)
    encode (AutoreflexiveQueryArchitecture.postStateUnder Arch world true).2 =
      encode (obsB world.1) := by
  rfl

end PostStateReadback

section SigBridge

variable [HistoryGraph P]

variable {S VA VB : Type w}
variable (sem : Semantics P S)
variable (obsA : S → VA) (obsB : S → VB)
variable (targetA : P → VA)
variable {h : P}

/-- A concrete witness that the full signature `Sig` is not constant on the left fiber. -/
def SigSeparatesLeftFiber : Prop :=
  ∃ x x' : FiberPt (P := P) obsA targetA h,
    ∃ fut : Future (P := P) h,
      Sig (P := P) sem obsA targetA x fut ∧
        ¬ Sig (P := P) sem obsA targetA x' fut

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

/--
If `Sig` separates the left fiber, there is no global `Fin 0` compression.

Reason: `CompatSigDimLe ... 0` provides a function into `Fin 0`,
contradicting the existence of a point in the separating witness.
-/
theorem not_compatSigDimLe_zero_of_sigSeparatesLeftFiber
    (hSep : SigSeparatesLeftFiber (P := P) (sem := sem)
      (obsA := obsA) (targetA := targetA) (h := h)) :
    ¬ CompatSigDimLe (P := P) sem obsA targetA (h := h) 0 := by
  intro hDim
  rcases hSep with ⟨x, _x', _fut, _hx, _hx'⟩
  rcases hDim with ⟨σ, _pred, _Hcorr⟩
  exact Fin.elim0 (σ x)

/--
If `Sig` separates the left fiber, there is no global `Fin 1` compression.

Reason: `Fin 1` is a subsingleton, so any `σ : fiber → Fin 1` identifies any two states.
If `σ` respects `Sig`, this forces equality of `Sig` on every future step, contradicting separation.
-/
theorem not_compatSigDimLe_one_of_sigSeparatesLeftFiber
    (hSep : SigSeparatesLeftFiber (P := P) (sem := sem)
      (obsA := obsA) (targetA := targetA) (h := h)) :
    ¬ CompatSigDimLe (P := P) sem obsA targetA (h := h) 1 := by
  intro hDim
  rcases hSep with ⟨x, x', fut, hx, hx'⟩
  rcases sigFactorsThrough_of_compatSigDimLe
      (P := P) (sem := sem) (obs := obsA) (target_obs := targetA) (h := h) (n := 1) hDim with
    ⟨σ, hσ⟩
  have fin1_val_eq_zero : ∀ t : Fin 1, t.val = 0 := by
    intro t
    cases t with
    | mk v hv =>
        cases v with
        | zero => rfl
        | succ v =>
            have : False := Nat.not_lt_zero v (Nat.lt_of_succ_lt_succ hv)
            exact this.elim
  have hEq : σ x = σ x' := by
    apply Fin.ext
    have hx0 : (σ x).val = 0 := fin1_val_eq_zero (σ x)
    have hx'0 : (σ x').val = 0 := fin1_val_eq_zero (σ x')
    exact hx0.trans hx'0.symm
  have hIff := hσ hEq fut
  exact hx' (hIff.mp hx)

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

 /--
 A `CompatSigDimLe` witness with the summary explicitly read from the post-query state.

 This avoids any extra definition, and keeps the dependence on the minimal query architecture
 explicit in the statement.
 -/
theorem exists_predFin_for_postStateUnder_true_of_correctSigOnLeftFiber_of_encode_injective
    (defaultB : VB) (decAB : VA × VB → Bool)
    {n : Nat} (encode : VB → Fin n) (hEncode : Function.Injective encode)
    (predB : VB → Future (P := P) h → Prop)
    (hCorr : CorrectSigOnLeftFiber (P := P) (sem := sem)
      (obsA := obsA) (obsB := obsB) (targetA := targetA) (h := h) predB) :
    let Arch :=
      queryRepairBySecondMargin (P := P) (obsA := obsA) (obsB := obsB) (targetA := targetA)
        (h0 := h) (defaultB := defaultB) (decAB := decAB)
    ∃ predFin : Fin n → Future (P := P) h → Prop,
      ∀ x fut,
        predFin (encode (AutoreflexiveQueryArchitecture.postStateUnder Arch x true).2) fut ↔
          CompatibleFuture (P := P) sem obsA targetA fut x := by
  intro Arch
  let predFin : Fin n → Future (P := P) h → Prop :=
    fun i fut => ∃ v : VB, encode v = i ∧ predB v fut
  refine ⟨predFin, ?_⟩
  intro x fut
  constructor
  · rintro ⟨v, hv, hvPred⟩
    have hv' : encode v = encode (obsB x.1) := by
      simpa [predFin, Arch] using hv
    have : v = obsB x.1 := hEncode hv'
    subst this
    exact (hCorr x fut).1 hvPred
  · intro hComp
    have : predB (obsB x.1) fut := (hCorr x fut).2 hComp
    refine ⟨obsB x.1, ?_, this⟩
    -- `postStateUnder ... true` stores `obsB x.1` in its second component.
    have hEq :
        encode (AutoreflexiveQueryArchitecture.postStateUnder Arch x true).2 =
          encode (obsB x.1) := by
      simpa [Arch] using
        (sigma_from_postStateUnder_true_eq (P := P) (obsA := obsA) (obsB := obsB)
          (targetA := targetA) (h := h) (defaultB := defaultB) (decAB := decAB)
          (encode := encode) x)
    exact hEq.symm

/--
Global minimality at `2`, on a fixed left fiber.

This is the global analogue of the step-local `CompatDimEq ... 2`: if there is an injective
encoding of the response channel into `Fin 2` that is correct for the full signature, and if `Sig`
separates the fiber, then the global signature dimension is exactly `2`.
-/
theorem compatSigDimEq_two_of_correctSigOnLeftFiber_of_encode_injective_of_sigSeparatesLeftFiber
    (encode : VB → Fin 2) (hEncode : Function.Injective encode)
    (predB : VB → Future (P := P) h → Prop)
    (hCorr : CorrectSigOnLeftFiber (P := P) (sem := sem)
      (obsA := obsA) (obsB := obsB) (targetA := targetA) (h := h) predB)
    (hSep : SigSeparatesLeftFiber (P := P) (sem := sem)
      (obsA := obsA) (targetA := targetA) (h := h)) :
    CompatSigDimEq (P := P) sem obsA targetA (h := h) 2 := by
  refine ⟨
    compatSigDimLe_of_correctSigOnLeftFiber_of_encode_injective
      (P := P) (sem := sem) (obsA := obsA) (obsB := obsB) (targetA := targetA) (h := h)
      (encode := encode) hEncode predB hCorr,
    ?_⟩
  intro m hm
  cases m with
  | zero =>
      exact (not_compatSigDimLe_zero_of_sigSeparatesLeftFiber
        (P := P) (sem := sem) (obsA := obsA) (targetA := targetA) (h := h) hSep)
  | succ m =>
      cases m with
      | zero =>
          -- `m = 1`
          exact (not_compatSigDimLe_one_of_sigSeparatesLeftFiber
            (P := P) (sem := sem) (obsA := obsA) (targetA := targetA) (h := h) hSep)
      | succ m =>
          -- `m >= 2`, contradicts `Nat.succ (Nat.succ m) < 2`
          have hge : 2 ≤ Nat.succ (Nat.succ m) :=
            Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le m))
          have : ¬ Nat.succ (Nat.succ m) < 2 := Nat.not_lt_of_ge hge
          intro _hDim
          exact this hm

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
#print axioms PrimitiveHolonomy.Examples.exists_predFin_for_postStateUnder_true_of_correctSigOnLeftFiber_of_encode_injective
#print axioms PrimitiveHolonomy.Examples.sigma_from_postStateUnder_true_eq
#print axioms PrimitiveHolonomy.Examples.not_compatSigDimLe_zero_of_sigSeparatesLeftFiber
#print axioms PrimitiveHolonomy.Examples.not_compatSigDimLe_one_of_sigSeparatesLeftFiber
#print axioms PrimitiveHolonomy.Examples.compatSigDimEq_two_of_correctSigOnLeftFiber_of_encode_injective_of_sigSeparatesLeftFiber
/- AXIOM_AUDIT_END -/
