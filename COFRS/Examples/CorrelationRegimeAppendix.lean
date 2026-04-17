import COFRS.Dynamics
import COFRS.ConverseNormalForm

/-!
# Appendix: a finitary “correlation regime” (positive error lower bound)

The repository’s core definitions are not probabilistic: they are structural and fiber-based.
However, the design-level meaning of “correlation-only” used in experiments can be captured
constructively in a fully finitary way:

* fix a finite fiber `Ω := FiberPt obs target_obs h`,
* and consider predictors that depend **only** on the observable interface `obs`.

If the step separates the fiber (`StepSeparatesFiber`), then any `obs`-only predictor must make
at least one mistake on `Ω`.

This file formalizes the corresponding strictly finitary statement:
nonzero error count for any `obs`-only Boolean predictor.

It also encodes the corresponding “uniform error rate” view as a finitary fraction `errCount / |Ω|`
(witnessed by a positive numerator together with `|Ω| > 0`), without introducing any probabilistic
machinery.

All proofs are constructive; see the `AXIOM_AUDIT` block at the end.
-/

namespace PrimitiveHolonomy
namespace Examples

universe u w

variable {P : Type u} [HistoryGraph P]

section CorrelationAppendix

variable {S' V' : Type w}
variable (sem' : Semantics P S') (obs : S' → V') (target_obs : P → V')
variable {h' k' : P} (step' : HistoryGraph.Path h' k')

/-- Constructive Boolean view of `Compatible ... x` given a pointwise decidability oracle. -/
def compatBool
    (decCompat :
      ∀ x : FiberPt (P := P) obs target_obs h',
        Decidable (Compatible (P := P) sem' obs target_obs step' x))
    (x : FiberPt (P := P) obs target_obs h') : Bool :=
  match decCompat x with
  | isTrue _ => true
  | isFalse _ => false

/-- `compatBool` is correct: it is `true` exactly when `Compatible` holds. -/
theorem compatBool_eq_true_iff
    (decCompat :
      ∀ x : FiberPt (P := P) obs target_obs h',
        Decidable (Compatible (P := P) sem' obs target_obs step' x))
    (x : FiberPt (P := P) obs target_obs h') :
    compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
        (h' := h') (step' := step') decCompat x = true ↔
      Compatible (P := P) sem' obs target_obs step' x := by
  unfold compatBool
  cases hdc : decCompat x with
  | isTrue h =>
      constructor
      · intro _
        exact h
      · intro _
        rfl
  | isFalse h =>
      constructor
      · intro hEq
        cases hEq
      · intro hC
        exfalso
        exact h hC

/--
Boolean misclassification predicate for an `obs`-only predictor `pred : V' → Bool` on a fiber point.

If `pred (obs x)` predicts `true`, then a mistake means `Compatible` is false; if it predicts `false`,
then a mistake means `Compatible` is true.
-/
def misBool
    (decCompat :
      ∀ x : FiberPt (P := P) obs target_obs h',
        Decidable (Compatible (P := P) sem' obs target_obs step' x))
    (pred : V' → Bool)
    (x : FiberPt (P := P) obs target_obs h') : Bool :=
  match pred (obs x.1) with
  | true =>
      Bool.not (compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
        (h' := h') (step' := step') decCompat x)
  | false =>
      compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
        (h' := h') (step' := step') decCompat x

/--
Appendix notion ("correlational" in the intended non-statistical sense):

`pred : V' → Bool` is correlationally correct if it decides the dynamic truth using only the
observable interface `obs`.

This is the deterministic / finitary analogue of “only using the marginal”.
-/
def CorrelationallyCorrect
    (decCompat :
      ∀ x : FiberPt (P := P) obs target_obs h',
        Decidable (Compatible (P := P) sem' obs target_obs step' x))
    (pred : V' → Bool) : Prop :=
  ∀ x : FiberPt (P := P) obs target_obs h',
    pred (obs x.1) =
      compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
        (h' := h') (step' := step') decCompat x

/--
If there is no Boolean misclassification anywhere on the fiber, then the rule is correlationally
correct (it exactly matches `compatBool` pointwise).

This is the bridge needed to upgrade “no perfect obs-only predictor” into an explicit
“at least one mistake”.
-/
theorem correlationallyCorrect_of_no_misBool
    (decCompat :
      ∀ x : FiberPt (P := P) obs target_obs h',
        Decidable (Compatible (P := P) sem' obs target_obs step' x))
    (pred : V' → Bool)
    (hNoErr :
      ∀ x : FiberPt (P := P) obs target_obs h',
        misBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
          (h' := h') (step' := step') decCompat pred x = false) :
    CorrelationallyCorrect sem' obs target_obs step' decCompat pred := by
  intro x
  have hmis : misBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
      (h' := h') (step' := step') decCompat pred x = false := hNoErr x
  cases hb : pred (obs x.1) with
  | false =>
      have hcb :
          compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
            (h' := h') (step' := step') decCompat x = false := by
        have hmis' := hmis
        dsimp [misBool] at hmis'
        rw [hb] at hmis'
        exact hmis'
      exact Eq.symm hcb
  | true =>
      have hnot :
          Bool.not (compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
              (h' := h') (step' := step') decCompat x) = false := by
        have hmis' := hmis
        dsimp [misBool] at hmis'
        rw [hb] at hmis'
        exact hmis'
      cases hc :
          compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
            (h' := h') (step' := step') decCompat x with
      | false =>
          have hnot' := hnot
          rw [hc] at hnot'
          have hNotFalse : Bool.not false = true := rfl
          have hcontra : true = false := Eq.trans hNotFalse.symm hnot'
          cases hcontra
      | true =>
          rfl

/-- A correlationally-correct Boolean rule yields an `ObsPredictsStep` witness. -/
theorem obsPredictsStep_of_correlationallyCorrect
    (decCompat :
      ∀ x : FiberPt (P := P) obs target_obs h',
        Decidable (Compatible (P := P) sem' obs target_obs step' x))
    {pred : V' → Bool}
    (hCorr : CorrelationallyCorrect sem' obs target_obs step' decCompat pred) :
    ObsPredictsStep (P := P) sem' obs target_obs step' := by
  refine ⟨(fun v => pred v = true), ?_⟩
  intro x
  have hx : pred (obs x.1) =
      compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
        (h' := h') (step' := step') decCompat x := hCorr x
  constructor
  · intro hC
    have hb :
        compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
          (h' := h') (step' := step') decCompat x = true :=
      (compatBool_eq_true_iff (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
        (h' := h') (step' := step') decCompat x).2 hC
    exact Eq.trans hx hb
  · intro hPred
    have hb :
        compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
          (h' := h') (step' := step') decCompat x = true :=
      Eq.trans hx.symm hPred
    exact (compatBool_eq_true_iff (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
      (h' := h') (step' := step') decCompat x).1 hb

/--
If the repository’s no-go holds (`¬ ObsPredictsStep`), then no correlationally-correct Boolean rule exists.

This is the intended formal counterpart of “no marginal/correlational shortcut closes the decision”.
-/
theorem not_correlationallyCorrect_of_not_obsPredictsStep
    (decCompat :
      ∀ x : FiberPt (P := P) obs target_obs h',
        Decidable (Compatible (P := P) sem' obs target_obs step' x))
    (hNo : ¬ ObsPredictsStep (P := P) sem' obs target_obs step') :
    ∀ pred : V' → Bool,
      ¬ CorrelationallyCorrect sem' obs target_obs step' decCompat pred := by
  intro pred hCorr
  apply hNo
  exact obsPredictsStep_of_correlationallyCorrect (P := P) (sem' := sem') (obs := obs)
    (target_obs := target_obs) (h' := h') (step' := step') decCompat hCorr

/--
If the step separates the fiber, then every obs-only Boolean predictor makes a mistake
at some explicit point of the fiber.
-/
theorem exists_misBool_of_stepSeparatesFiber
    (decCompat :
      ∀ x : FiberPt (P := P) obs target_obs h',
        Decidable (Compatible (P := P) sem' obs target_obs step' x))
    (hSep : StepSeparatesFiber (P := P) sem' obs target_obs step')
    (pred : V' → Bool) :
    ∃ x : FiberPt (P := P) obs target_obs h',
      misBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
        (h' := h') (step' := step') decCompat pred x = true := by
  rcases hSep with ⟨xT, xF, _hxne, hxT, hxF⟩
  have hxTobs : obs xT.1 = target_obs h' := xT.2
  have hxFobs : obs xF.1 = target_obs h' := xF.2
  cases hb : pred (target_obs h') with
  | true =>
      refine ⟨xF, ?_⟩
      have hbF : pred (obs xF.1) = true := by
        rw [hxFobs]
        exact hb
      have hCompatFalse :
          compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
            (h' := h') (step' := step') decCompat xF = false := by
        cases hc :
            compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
              (h' := h') (step' := step') decCompat xF with
        | false => rfl
        | true =>
            have hC : Compatible (P := P) sem' obs target_obs step' xF :=
              (compatBool_eq_true_iff (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
                (h' := h') (step' := step') decCompat xF).1 hc
            exact False.elim (hxF hC)
      have hbScr : pred (obs xF.1) = true := hbF
      cases hpred : pred (obs xF.1) with
      | false =>
          have : false = true := Eq.trans hpred.symm hbScr
          cases this
      | true =>
          unfold misBool
          rw [hpred, hCompatFalse]
          rfl
  | false =>
      refine ⟨xT, ?_⟩
      have hbT : pred (obs xT.1) = false := by
        rw [hxTobs]
        exact hb
      have hCompatTrue :
          compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
            (h' := h') (step' := step') decCompat xT = true := by
        cases hc :
            compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
              (h' := h') (step' := step') decCompat xT with
        | true => rfl
        | false =>
            have hTrue :
                compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
                  (h' := h') (step' := step') decCompat xT = true :=
              (compatBool_eq_true_iff (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
                (h' := h') (step' := step') decCompat xT).2 hxT
            have hTrue' := hTrue
            rw [hc] at hTrue'
            cases hTrue'
      have hbScr : pred (obs xT.1) = false := hbT
      cases hpred : pred (obs xT.1) with
      | true =>
          have : true = false := Eq.trans hpred.symm hbScr
          cases this
      | false =>
          unfold misBool
          rw [hpred]
          exact hCompatTrue

/-!
### From `¬ ObsPredictsStep` to an explicit mistake

The core development proves non-closure as `¬ ObsPredictsStep`. The converse/normal-form layer
(`COFRS/ConverseNormalForm.lean`) turns that negative statement into an explicit fiber separation,
provided we have:

- an explicit finite enumeration of the fiber (`FiberEnum`), and
- a pointwise decidability oracle for `Compatible` on that fiber.

This lemma packages the “there exists at least one mistake” form directly from `¬ ObsPredictsStep`,
so the appendix has both the “count > 0” statement and the explicit witness form.
-/
theorem exists_misBool_of_not_obsPredictsStep
    (E : FiberEnum (P := P) obs target_obs h')
    (decCompat :
      ∀ x : FiberPt (P := P) obs target_obs h',
        Decidable (Compatible (P := P) sem' obs target_obs step' x))
    (hNo : ¬ ObsPredictsStep (P := P) sem' obs target_obs step')
    (pred : V' → Bool) :
    ∃ x : FiberPt (P := P) obs target_obs h',
      misBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
        (h' := h') (step' := step') decCompat pred x = true := by
  have hOr :=
    PrimitiveHolonomy.obsPredictsStep_or_stepSeparatesFiber_of_fiberEnum
      (P := P) (sem := sem') (obs := obs) (target_obs := target_obs)
      (step := step') E decCompat
  cases hOr with
  | inl hObs =>
      exact False.elim (hNo hObs)
  | inr hSep =>
      exact exists_misBool_of_stepSeparatesFiber (P := P) (sem' := sem') (obs := obs)
        (target_obs := target_obs) (h' := h') (step' := step') decCompat hSep pred

namespace BoolCount

private def liftFin {n : Nat} : Fin n → Fin (Nat.succ n) :=
  fun i => ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩

private def lastFin (n : Nat) : Fin (Nat.succ n) := ⟨n, Nat.lt_succ_self n⟩

/-- Constructive count of `true` values of a Boolean predicate over `Fin n`. -/
def countTrue : (n : Nat) → (Fin n → Bool) → Nat
  | 0, _ => 0
  | Nat.succ n, f =>
      countTrue n (fun i => f (liftFin (n := n) i)) +
        match f (lastFin n) with
        | true => 1
        | false => 0

theorem countTrue_pos_of_exists_true :
    ∀ {n : Nat} {f : Fin n → Bool},
      (∃ i : Fin n, f i = true) → 0 < countTrue n f := by
  intro n
  induction n with
  | zero =>
      intro f hex
      rcases hex with ⟨i, _⟩
      exact Fin.elim0 i
  | succ n ih =>
      intro f hex
      rcases hex with ⟨i, hi⟩
      by_cases hLast : i.val = n
      ·
        have hiLast : i = lastFin n := by
          have hLastVal : (lastFin n).val = n := rfl
          apply Fin.ext
          rw [hLastVal]
          exact hLast
        have hLastTrue : f (lastFin n) = true := by
          have hi' := hi
          rw [hiLast] at hi'
          exact hi'
        have hPos : 0 < countTrue n (fun t : Fin n => f (liftFin (n := n) t)) + 1 := by
          have h : 0 < Nat.succ (countTrue n (fun t : Fin n => f (liftFin (n := n) t))) :=
            Nat.zero_lt_succ _
          have hEq :
              Nat.succ (countTrue n (fun t : Fin n => f (liftFin (n := n) t))) =
                countTrue n (fun t : Fin n => f (liftFin (n := n) t)) + 1 :=
            Nat.succ_eq_add_one _
          have h' := h
          rw [hEq] at h'
          exact h'
        unfold countTrue
        rw [hLastTrue]
        exact hPos
      ·
        have hle : i.val ≤ n := Nat.le_of_lt_succ i.isLt
        have hlt : i.val < n := Nat.lt_of_le_of_ne hle hLast
        let j : Fin n := ⟨i.val, hlt⟩
        have hj : f (liftFin (n := n) j) = true := by
          have hij : liftFin (n := n) j = i := by
            apply Fin.ext
            rfl
          have hi' := hi
          rw [← hij] at hi'
          exact hi'
        have : 0 < countTrue n (fun t : Fin n => f (liftFin (n := n) t)) :=
          ih ⟨j, hj⟩
        have hPos :
            0 < countTrue n (fun t : Fin n => f (liftFin (n := n) t)) +
              (match f (lastFin n) with | true => 1 | false => 0) :=
          Nat.lt_of_lt_of_le this (Nat.le_add_right _ _)
        unfold countTrue
        exact hPos

end BoolCount

/-- Finite error count over an explicit fiber enumeration. -/
def errCount
    (E : FiberEnum (P := P) obs target_obs h')
    (decCompat :
      ∀ x : FiberPt (P := P) obs target_obs h',
        Decidable (Compatible (P := P) sem' obs target_obs step' x))
    (pred : V' → Bool) : Nat :=
  BoolCount.countTrue E.N (fun i =>
    misBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
      (h' := h') (step' := step') decCompat pred (E.enum i))

/--
Finitary “uniform error rate” view: a fraction `num/den` with `den = |Ω| = E.N`.

We keep this lightweight and purely finitary: “rate is strictly positive” is witnessed by
`0 < num` together with `0 < den`.
-/
structure ErrRate where
  num : Nat
  den : Nat
  den_pos : 0 < den

def errRate
    (E : FiberEnum (P := P) obs target_obs h')
    (hN : 0 < E.N)
    (decCompat :
      ∀ x : FiberPt (P := P) obs target_obs h',
        Decidable (Compatible (P := P) sem' obs target_obs step' x))
    (pred : V' → Bool) : ErrRate :=
  { num := errCount (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
      (h' := h') (step' := step') E decCompat pred
    den := E.N
    den_pos := by simpa using hN }

theorem errRate_num_pos_of_errCount_pos
    (E : FiberEnum (P := P) obs target_obs h')
    (hN : 0 < E.N)
    (decCompat :
      ∀ x : FiberPt (P := P) obs target_obs h',
        Decidable (Compatible (P := P) sem' obs target_obs step' x))
    (pred : V' → Bool)
    (hPos :
      0 < errCount (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
        (h' := h') (step' := step') E decCompat pred) :
    0 < (errRate (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
      (h' := h') (step' := step') E hN decCompat pred).num := by
  simpa [errRate] using hPos

theorem errCount_pos_of_exists_misBool
    (E : FiberEnum (P := P) obs target_obs h')
    (decCompat :
      ∀ x : FiberPt (P := P) obs target_obs h',
        Decidable (Compatible (P := P) sem' obs target_obs step' x))
    (pred : V' → Bool)
    (hMis :
      ∃ x : FiberPt (P := P) obs target_obs h',
        misBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
          (h' := h') (step' := step') decCompat pred x = true) :
    0 < errCount (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
      (h' := h') (step' := step') E decCompat pred := by
  rcases hMis with ⟨x, hx⟩
  rcases E.surj x with ⟨i, hi⟩
  have hAtI :
      (fun j : Fin E.N =>
          misBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
            (h' := h') (step' := step') decCompat pred (E.enum j)) i = true := by
    have hEq :
        misBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
            (h' := h') (step' := step') decCompat pred (E.enum i) =
          misBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
            (h' := h') (step' := step') decCompat pred x :=
      congrArg
        (fun y =>
          misBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
            (h' := h') (step' := step') decCompat pred y) hi
    exact Eq.trans hEq hx
  have : 0 < BoolCount.countTrue E.N (fun j : Fin E.N =>
        misBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
          (h' := h') (step' := step') decCompat pred (E.enum j)) :=
    BoolCount.countTrue_pos_of_exists_true ⟨i, hAtI⟩
  unfold errCount
  exact this

theorem errCount_pos_of_stepSeparatesFiber
    (E : FiberEnum (P := P) obs target_obs h')
    (decCompat :
      ∀ x : FiberPt (P := P) obs target_obs h',
        Decidable (Compatible (P := P) sem' obs target_obs step' x))
    (hSep : StepSeparatesFiber (P := P) sem' obs target_obs step')
    (pred : V' → Bool) :
    0 < errCount (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
      (h' := h') (step' := step') E decCompat pred := by
  apply errCount_pos_of_exists_misBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
    (h' := h') (step' := step') (E := E) (decCompat := decCompat) (pred := pred)
  exact exists_misBool_of_stepSeparatesFiber (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
    (h' := h') (step' := step') decCompat hSep pred

/--
Finitary “strictly positive error count” version: under an explicit fiber enumeration and a
pointwise decidability oracle, `¬ ObsPredictsStep` implies every obs-only Boolean predictor makes
at least one mistake on the fiber, hence the finite error count is strictly positive.
-/
theorem errCount_pos_of_not_obsPredictsStep
    (E : FiberEnum (P := P) obs target_obs h')
    (decCompat :
      ∀ x : FiberPt (P := P) obs target_obs h',
        Decidable (Compatible (P := P) sem' obs target_obs step' x))
    (hNo : ¬ ObsPredictsStep (P := P) sem' obs target_obs step')
    (pred : V' → Bool) :
    0 < errCount (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
      (h' := h') (step' := step') E decCompat pred := by
  apply errCount_pos_of_exists_misBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
    (h' := h') (step' := step') (E := E) (decCompat := decCompat) (pred := pred)
  exact exists_misBool_of_not_obsPredictsStep (P := P) (sem' := sem') (obs := obs)
    (target_obs := target_obs) (h' := h') (step' := step') (E := E)
    (decCompat := decCompat) hNo pred

theorem errRate_num_pos_of_not_obsPredictsStep
    (E : FiberEnum (P := P) obs target_obs h')
    (hN : 0 < E.N)
    (decCompat :
      ∀ x : FiberPt (P := P) obs target_obs h',
        Decidable (Compatible (P := P) sem' obs target_obs step' x))
    (hNo : ¬ ObsPredictsStep (P := P) sem' obs target_obs step')
    (pred : V' → Bool) :
    0 < (errRate (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
      (h' := h') (step' := step') E hN decCompat pred).num := by
  apply errRate_num_pos_of_errCount_pos (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
    (h' := h') (step' := step') (E := E) (hN := hN) (decCompat := decCompat) (pred := pred)
  exact errCount_pos_of_not_obsPredictsStep (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
    (h' := h') (step' := step') (E := E) (decCompat := decCompat) hNo pred

end CorrelationAppendix

end Examples
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.Examples.compatBool
#print axioms PrimitiveHolonomy.Examples.compatBool_eq_true_iff
#print axioms PrimitiveHolonomy.Examples.misBool
#print axioms PrimitiveHolonomy.Examples.correlationallyCorrect_of_no_misBool
#print axioms PrimitiveHolonomy.Examples.CorrelationallyCorrect
#print axioms PrimitiveHolonomy.Examples.obsPredictsStep_of_correlationallyCorrect
#print axioms PrimitiveHolonomy.Examples.not_correlationallyCorrect_of_not_obsPredictsStep
#print axioms PrimitiveHolonomy.Examples.exists_misBool_of_stepSeparatesFiber
#print axioms PrimitiveHolonomy.Examples.exists_misBool_of_not_obsPredictsStep
#print axioms PrimitiveHolonomy.Examples.BoolCount.countTrue
#print axioms PrimitiveHolonomy.Examples.BoolCount.countTrue_pos_of_exists_true
#print axioms PrimitiveHolonomy.Examples.errCount
#print axioms PrimitiveHolonomy.Examples.ErrRate
#print axioms PrimitiveHolonomy.Examples.errRate
#print axioms PrimitiveHolonomy.Examples.errRate_num_pos_of_errCount_pos
#print axioms PrimitiveHolonomy.Examples.errCount_pos_of_exists_misBool
#print axioms PrimitiveHolonomy.Examples.errCount_pos_of_stepSeparatesFiber
#print axioms PrimitiveHolonomy.Examples.errCount_pos_of_not_obsPredictsStep
#print axioms PrimitiveHolonomy.Examples.errRate_num_pos_of_not_obsPredictsStep
/- AXIOM_AUDIT_END -/
