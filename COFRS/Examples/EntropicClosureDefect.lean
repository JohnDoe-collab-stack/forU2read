import COFRS.Examples.ReferentialInduction

/-!
# Entropic closure defect (support-relative, constructive)

This file provides a constructive bridge between:

* the *structural* closure/factorization layer in `COFRS/Examples/ReferentialInduction.lean`, and
* the *support-relative* (distribution-relative) "entropy layer" used in `Private_notes/Entropie.md`.

We do **not** formalize a numeric Shannon entropy here (no `Real.log`, no measure theory).
Instead, we capture exactly the operational content used by the project:

* `H_P(Y | O) = 0`  ↔  `Y` factors through `O` on the support of `P`;
* `H_P(Y | O) > 0`  ↔  there is a diagonal defect witness charged by `P`.

To stay fully constructive, a "distribution" is represented by a weight function `ω : X → Nat`,
and "positive mass" is `ω x ≠ 0`.

All proofs are constructive; see the `AXIOM_AUDIT` block at the end.
-/

namespace PrimitiveHolonomy
namespace Examples

universe u w

variable {P : Type u} [HistoryGraph P]

namespace ReferentialProblem

/-!
## Support model for a distribution

We represent a (discrete) distribution by weights `ω : X → Nat`.
Only the support predicate `ω x ≠ 0` matters for the `=0` vs `>0` closure regime.
-/

def Weight (R : ReferentialProblem.{w}) :=
  R.X → Nat

def Supp {R : ReferentialProblem.{w}} (ω : Weight R) (x : R.X) : Prop :=
  ω x ≠ 0

/-!
## Support-relative closure (entropy-zero) and support-relative defect (entropy-positive)

Reading against `Private_notes/Entropie.md`:

* `ClosesOnSupport ω` corresponds to `D_P(Y;O) = 0` (i.e. `H_P(Y|O) = 0`).
* `DefectOnSupport ω` corresponds to `D_P(Y;O) > 0` (a witness-charged non-closure).
-/

def ClosesOnSupport (R : ReferentialProblem.{w}) (ω : Weight R) : Prop :=
  ∃ pred : R.Q → Prop, ∀ x : R.X, Supp ω x → (R.T x ↔ pred (R.q x))

def DefectOnSupport (R : ReferentialProblem.{w}) (ω : Weight R) : Prop :=
  ∃ x x' : R.X,
    Supp ω x ∧ Supp ω x' ∧ R.q x = R.q x' ∧ R.T x ∧ ¬ R.T x'

theorem closesOnSupport_of_closes (R : ReferentialProblem.{w}) (ω : Weight R) :
    R.Closes → R.ClosesOnSupport ω := by
  rintro ⟨pred, hpred⟩
  refine ⟨pred, ?_⟩
  intro x _hxSupp
  exact hpred x

theorem not_defectOnSupport_of_closesOnSupport (R : ReferentialProblem.{w}) (ω : Weight R) :
    R.ClosesOnSupport ω → ¬ R.DefectOnSupport ω := by
  rintro ⟨pred, hpred⟩ ⟨x, x', hxSupp, hx'Supp, hq, hxT, hx'T⟩
  have hxPred : pred (R.q x) := (hpred x hxSupp).1 hxT
  have hx'Pred : pred (R.q x') := by
    have : pred (R.q x) ↔ pred (R.q x') :=
      PrimitiveHolonomy.iff_of_eq (congrArg pred hq)
    exact this.mp hxPred
  have : R.T x' := (hpred x' hx'Supp).2 hx'Pred
  exact hx'T this

/-!
### Canonical closure predicate from "no defect" (decidable truth)

Constructively, turning the negative statement "no defect witness exists" into the positive
statement "there exists a closing predicate" requires that the target truth be decidable.

In the intended discrete settings, `Y` is a Boolean truth and this assumption is satisfied.
-/

theorem closesOnSupport_of_not_defectOnSupport
    (R : ReferentialProblem.{w}) (ω : Weight R) [DecidablePred R.T] :
    (¬ R.DefectOnSupport ω) → R.ClosesOnSupport ω := by
  intro hNo
  let pred : R.Q → Prop :=
    fun q0 => ∃ x' : R.X, Supp ω x' ∧ R.q x' = q0 ∧ R.T x'
  refine ⟨pred, ?_⟩
  intro x hxSupp
  constructor
  · intro hxT
    exact ⟨x, hxSupp, rfl, hxT⟩
  · intro hxPred
    rcases hxPred with ⟨x', hx'Supp, hq, hx'T⟩
    -- If `T x` were false, we'd have a supported diagonal defect.
    by_cases hxT : R.T x
    · exact hxT
    · exfalso
      exact hNo ⟨x', x, hx'Supp, hxSupp, hq, hx'T, hxT⟩

theorem closesOnSupport_iff_not_defectOnSupport
    (R : ReferentialProblem.{w}) (ω : Weight R) [DecidablePred R.T] :
    R.ClosesOnSupport ω ↔ ¬ R.DefectOnSupport ω := by
  constructor
  · exact not_defectOnSupport_of_closesOnSupport (R := R) (ω := ω)
  · exact closesOnSupport_of_not_defectOnSupport (R := R) (ω := ω)

/-!
## Bridge to `DiagonalWitness` and to the forced-mediation theorems
-/

theorem diagonalWitness_of_defectOnSupport (R : ReferentialProblem.{w}) (ω : Weight R) :
    R.DefectOnSupport ω → R.DiagonalWitness := by
  rintro ⟨x, x', _hxSupp, _hx'Supp, hq, hxT, hx'T⟩
  have hxne : x ≠ x' := by
    intro hEq
    subst hEq
    exact hx'T hxT
  exact ⟨x, x', hxne, hq, hxT, hx'T⟩

theorem not_closes_of_defectOnSupport (R : ReferentialProblem.{w}) (ω : Weight R) :
    R.DefectOnSupport ω → ¬ R.Closes := by
  intro hDef
  have hDiag : R.DiagonalWitness := diagonalWitness_of_defectOnSupport (R := R) (ω := ω) hDef
  exact ReferentialProblem.not_closes_of_diagonalWitness (R := R) hDiag

theorem not_descends_of_defectOnSupport_of_mediatesLe
    {n : Nat} (R : ReferentialProblem.{w}) (ω : Weight R)
    (hDef : R.DefectOnSupport ω)
    (σ : R.X → Fin n) (predFin : Fin n → Prop)
    (hMed : ∀ x : R.X, R.T x ↔ predFin (σ x)) :
    ¬ R.DescendsToQuot σ := by
  have hDiag : R.DiagonalWitness := diagonalWitness_of_defectOnSupport (R := R) (ω := ω) hDef
  exact ReferentialProblem.not_descends_of_diagonalWitness_of_mediatesLe R hDiag σ predFin hMed

theorem closesOnSupport_extendQuot_of_mediatesLe
    {n : Nat} (R : ReferentialProblem.{w}) (ω : Weight R)
    (σ : R.X → Fin n) (predFin : Fin n → Prop)
    (hMed : ∀ x : R.X, R.T x ↔ predFin (σ x)) :
    (R.extendQuot σ).ClosesOnSupport ω := by
  have hClose : (R.extendQuot σ).Closes :=
    ReferentialProblem.closes_extendQuot_of_mediatesLe (R := R) σ predFin hMed
  exact closesOnSupport_of_closes (R := R.extendQuot σ) (ω := ω) hClose

/--
If `σ` descends to the original quotient (it is computable from `q`), then extending the quotient
by `σ` cannot remove a support-charged defect witness: any defect inside a `q`-fiber remains a defect
inside the extended fiber.

This is the support-level version of the principle "a mediator computed from the observable does not
reduce the closure defect".
-/
theorem defectOnSupport_extendQuot_of_defectOnSupport_of_descendsToQuot
    {n : Nat} (R : ReferentialProblem.{w}) (ω : Weight R) (σ : R.X → Fin n)
    (hDesc : R.DescendsToQuot σ) :
    R.DefectOnSupport ω → (R.extendQuot σ).DefectOnSupport ω := by
  rintro ⟨x, x', hxSupp, hx'Supp, hq, hxT, hx'T⟩
  rcases hDesc with ⟨f, hf⟩
  have hσ : σ x = σ x' := by
    have hxEq : σ x = f (R.q x) := hf x
    have hx'Eq : σ x' = f (R.q x') := hf x'
    calc
      σ x = f (R.q x) := hxEq
      _ = f (R.q x') := congrArg f hq
      _ = σ x' := (hx'Eq).symm
  refine ⟨x, x', hxSupp, hx'Supp, ?_, hxT, hx'T⟩
  -- equality of the extended quotient values
  exact Prod.ext hq hσ

theorem defectOnSupport_of_defectOnSupport_extendQuot
    {n : Nat} (R : ReferentialProblem.{w}) (ω : Weight R) (σ : R.X → Fin n) :
    (R.extendQuot σ).DefectOnSupport ω → R.DefectOnSupport ω := by
  rintro ⟨x, x', hxSupp, hx'Supp, hq', hxT, hx'T⟩
  have hq : R.q x = R.q x' := congrArg Prod.fst hq'
  exact ⟨x, x', hxSupp, hx'Supp, hq, hxT, hx'T⟩

theorem defectOnSupport_extendQuot_iff_of_descendsToQuot
    {n : Nat} (R : ReferentialProblem.{w}) (ω : Weight R) (σ : R.X → Fin n)
    (hDesc : R.DescendsToQuot σ) :
    (R.extendQuot σ).DefectOnSupport ω ↔ R.DefectOnSupport ω := by
  constructor
  · exact defectOnSupport_of_defectOnSupport_extendQuot (R := R) (ω := ω) (σ := σ)
  · exact defectOnSupport_extendQuot_of_defectOnSupport_of_descendsToQuot
      (R := R) (ω := ω) (σ := σ) hDesc

/--
If `σ` descends to the original quotient (it is computable from `q`) and the truth closes on the
extended quotient on the support, then it already closes on the original quotient on the support.

This is the support-level version of: `H(Y | O, z) = 0` implies `H(Y | O) = 0` when `z` is a function
of `O`.
-/
theorem closesOnSupport_of_closesOnSupport_extendQuot_of_descendsToQuot
    {n : Nat} (R : ReferentialProblem.{w}) (ω : Weight R) (σ : R.X → Fin n)
    (hDesc : R.DescendsToQuot σ) :
    (R.extendQuot σ).ClosesOnSupport ω → R.ClosesOnSupport ω := by
  rintro ⟨pred, hpred⟩
  rcases hDesc with ⟨f, hf⟩
  let pred0 : R.Q → Prop := fun q0 => pred (q0, f q0)
  refine ⟨pred0, ?_⟩
  intro x hxSupp
  have hσ : σ x = f (R.q x) := hf x
  have hpredEq :
      pred ((R.q x, σ x)) ↔ pred (R.q x, f (R.q x)) :=
    PrimitiveHolonomy.iff_of_eq (congrArg pred (Prod.ext rfl hσ))
  -- `extendQuot` has `q x := (R.q x, σ x)` and the same `T`.
  have hxClose : R.T x ↔ pred (R.q x, σ x) := hpred x hxSupp
  exact hxClose.trans hpredEq

end ReferentialProblem

end Examples
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.Examples.ReferentialProblem.closesOnSupport_iff_not_defectOnSupport
#print axioms PrimitiveHolonomy.Examples.ReferentialProblem.diagonalWitness_of_defectOnSupport
#print axioms PrimitiveHolonomy.Examples.ReferentialProblem.not_descends_of_defectOnSupport_of_mediatesLe
#print axioms PrimitiveHolonomy.Examples.ReferentialProblem.defectOnSupport_extendQuot_iff_of_descendsToQuot
#print axioms PrimitiveHolonomy.Examples.ReferentialProblem.closesOnSupport_of_closesOnSupport_extendQuot_of_descendsToQuot
/- AXIOM_AUDIT_END -/
