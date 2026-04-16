import COFRS.Dynamics
import COFRS.ConverseNormalForm
import COFRS.Examples.DiagonalizationMediationCausalityThesis

/-!
# Independence → relation → mediator (Lean spine, two interfaces)

This file makes **operationally checkable** a long-form chain that is used throughout the project:

* two marginal interfaces can each be insufficient (no obs-only closure),
* the insufficiency can be certified by diagonal obstruction (`LagEvent`),
* negative no-go statements can be bridged to explicit separating witnesses (constructively, given finitary data),
* and recoverability is quantified by an exact finite mediator (`Fin n`) via compatibility dimension
  and its canonical lift (`RefiningLift`), with minimality.

This is intentionally stated as reusable theorems with all hypotheses explicit.
All proofs are constructive; see the `AXIOM_AUDIT` block at the end.
-/

namespace PrimitiveHolonomy
namespace Examples

universe u w

variable {P : Type u} [HistoryGraph P]

section TwoInterfaces

variable {S VA VB : Type w}
variable (sem : Semantics P S)
variable (obsA : S → VA) (obsB : S → VB)
variable (targetA : P → VA) (targetB : P → VB)
variable {h k : P} (step : HistoryGraph.Path h k)

abbrev obsAB : S → VA × VB := PrimitiveHolonomy.obsAB (obsA := obsA) (obsB := obsB)

abbrev targetAB : P → VA × VB :=
  PrimitiveHolonomy.targetAB (P := P) (targetA := targetA) (targetB := targetB)

/-!
## Fiber projection and comparison lemmas (joint truth projects to weaker marginal truths)

For the **joint** interface `obsAB : S → VA×VB`, we can project fiber points to the marginal
fibers for `obsA` and `obsB`.

The key logical direction made explicit below is:

* joint compatibility ⇒ marginal compatibility.

In general, the converse does **not** hold: marginal compatibility can be strictly weaker than
joint compatibility.
-/

def fiberAB_to_A :
    FiberPt (P := P) (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) h →
      FiberPt (P := P) obsA targetA h :=
  fun x =>
    ⟨x.1, by
      -- x.2 : (obsA x, obsB x) = (targetA h, targetB h)
      exact congrArg Prod.fst x.2⟩

def fiberAB_to_B :
    FiberPt (P := P) (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) h →
      FiberPt (P := P) obsB targetB h :=
  fun x =>
    ⟨x.1, by
      exact congrArg Prod.snd x.2⟩

theorem compatibleA_of_compatibleAB
    (x : FiberPt (P := P) (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) h) :
    Compatible (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
        (targetAB (targetA := targetA) (targetB := targetB)) step x →
      Compatible (P := P) sem obsA targetA step (fiberAB_to_A (P := P) (obsA := obsA) (obsB := obsB)
        (targetA := targetA) (targetB := targetB) (h := h) x) := by
  intro hC
  rcases hC with ⟨y, hTrans⟩
  refine ⟨⟨y.1, ?_⟩, ?_⟩
  · exact congrArg Prod.fst y.2
  · exact hTrans

theorem compatibleB_of_compatibleAB
    (x : FiberPt (P := P) (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) h) :
    Compatible (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
        (targetAB (targetA := targetA) (targetB := targetB)) step x →
      Compatible (P := P) sem obsB targetB step (fiberAB_to_B (P := P) (obsA := obsA) (obsB := obsB)
        (targetA := targetA) (targetB := targetB) (h := h) x) := by
  intro hC
  rcases hC with ⟨y, hTrans⟩
  refine ⟨⟨y.1, ?_⟩, ?_⟩
  · exact congrArg Prod.snd y.2
  · exact hTrans

/-!
## Explicit “irreducibility to marginals” for the joint dynamic truth

To express “the joint truth is not contained in either marginal view”, we keep the **dynamic truth**
fixed as `Compatible` on the joint fiber (`obs := obsAB`), but restrict the predictor to depend only on
the left (resp. right) projection.

Since all points in a joint fiber share the same `obsAB` value, any left-only (or right-only) predictor
collapses to a constant classifier on that fiber. Therefore, as soon as the step separates the joint fiber,
such predictors are impossible.
-/

abbrev LeftObsPredictsJointStep : Prop :=
  PrimitiveHolonomy.LeftObsPredictsJointStep (P := P) sem obsA obsB targetA targetB step

abbrev RightObsPredictsJointStep : Prop :=
  PrimitiveHolonomy.RightObsPredictsJointStep (P := P) sem obsA obsB targetA targetB step

/-!
### Mediator descent (irreducibility at the mediator level)

The previous “irreducibility” notion was phrased at the level of **predicting the joint dynamic truth**
from a marginal projection.

To express the strongest form used in the thesis narrative, we also define “descent” for the mediator:
the finite supplement carried by a `RefiningLiftData` on the joint fiber should not be reconstructible
from either marginal observation alone.

We show:

* mediator descends to the left ⇒ the joint dynamic truth is left-predictable;
* mediator descends to the right ⇒ the joint dynamic truth is right-predictable;
* therefore, any no-go for left/right predictability implies no-go for descent of the mediator itself.
-/

abbrev MediatorDescendsLeft {n : Nat}
    (L : RefiningLiftData (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) h step n) : Prop :=
  PrimitiveHolonomy.MediatorDescendsLeft (P := P) sem obsA obsB targetA targetB step L

abbrev MediatorDescendsRight {n : Nat}
    (L : RefiningLiftData (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) h step n) : Prop :=
  PrimitiveHolonomy.MediatorDescendsRight (P := P) sem obsA obsB targetA targetB step L

theorem leftObsPredictsJointStep_of_mediatorDescendsLeft
    {n : Nat}
    (L : RefiningLiftData (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) h step n) :
    MediatorDescendsLeft (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step L →
      LeftObsPredictsJointStep (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
        (targetA := targetA) (targetB := targetB) (h := h) (k := k) step := by
  rintro ⟨ρA, hρA⟩
  refine ⟨(fun v => L.predFin (ρA v)), ?_⟩
  intro x
  have hx : Compatible (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) step x ↔
        L.predFin ((L.extObs x).2) :=
    L.factors x
  -- substitute the descent equation
  simpa [hρA x] using hx

theorem rightObsPredictsJointStep_of_mediatorDescendsRight
    {n : Nat}
    (L : RefiningLiftData (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) h step n) :
    MediatorDescendsRight (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step L →
      RightObsPredictsJointStep (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
        (targetA := targetA) (targetB := targetB) (h := h) (k := k) step := by
  rintro ⟨ρB, hρB⟩
  refine ⟨(fun v => L.predFin (ρB v)), ?_⟩
  intro x
  have hx : Compatible (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) step x ↔
        L.predFin ((L.extObs x).2) :=
    L.factors x
  simpa [hρB x] using hx

theorem not_mediatorDescendsLeft_of_not_leftObsPredictsJointStep
    {n : Nat}
    (L : RefiningLiftData (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) h step n)
    (hNo : ¬ LeftObsPredictsJointStep (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step) :
    ¬ MediatorDescendsLeft (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step L := by
  intro hDesc
  exact hNo (leftObsPredictsJointStep_of_mediatorDescendsLeft
    (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
    (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step) L hDesc)

theorem not_mediatorDescendsRight_of_not_rightObsPredictsJointStep
    {n : Nat}
    (L : RefiningLiftData (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) h step n)
    (hNo : ¬ RightObsPredictsJointStep (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step) :
    ¬ MediatorDescendsRight (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step L := by
  intro hDesc
  exact hNo (rightObsPredictsJointStep_of_mediatorDescendsRight
    (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
    (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step) L hDesc)

theorem not_leftObsPredictsJointStep_of_stepSeparatesJointFiber
    (hSep :
      StepSeparatesFiber (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
        (targetAB (targetA := targetA) (targetB := targetB)) step) :
    ¬ LeftObsPredictsJointStep (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
        (targetA := targetA) (targetB := targetB) (h := h) (k := k) step := by
  intro hPred
  rcases hPred with ⟨pred, hcorr⟩
  have hConst :
      ∃ c : Prop,
        ∀ x : FiberPt (P := P) (obsAB (obsA := obsA) (obsB := obsB))
            (targetAB (targetA := targetA) (targetB := targetB)) h,
          Compatible (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
              (targetAB (targetA := targetA) (targetB := targetB)) step x ↔ c := by
    refine ⟨pred (targetA h), ?_⟩
    intro x
    have hxA : obsA x.1 = targetA h := congrArg Prod.fst x.2
    simpa [hxA] using (hcorr x)
  exact (PrimitiveHolonomy.Examples.no_constant_classifier_of_stepSeparatesFiber
      (P := P) (sem := sem)
      (obs := (obsAB (obsA := obsA) (obsB := obsB)))
      (target_obs := (targetAB (targetA := targetA) (targetB := targetB)))
      (h := h) (k := k) (step := step) hSep) hConst

theorem not_rightObsPredictsJointStep_of_stepSeparatesJointFiber
    (hSep :
      StepSeparatesFiber (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
        (targetAB (targetA := targetA) (targetB := targetB)) step) :
    ¬ RightObsPredictsJointStep (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
        (targetA := targetA) (targetB := targetB) (h := h) (k := k) step := by
  intro hPred
  rcases hPred with ⟨pred, hcorr⟩
  have hConst :
      ∃ c : Prop,
        ∀ x : FiberPt (P := P) (obsAB (obsA := obsA) (obsB := obsB))
            (targetAB (targetA := targetA) (targetB := targetB)) h,
          Compatible (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
              (targetAB (targetA := targetA) (targetB := targetB)) step x ↔ c := by
    refine ⟨pred (targetB h), ?_⟩
    intro x
    have hxB : obsB x.1 = targetB h := congrArg Prod.snd x.2
    simpa [hxB] using (hcorr x)
  exact (PrimitiveHolonomy.Examples.no_constant_classifier_of_stepSeparatesFiber
      (P := P) (sem := sem)
      (obs := (obsAB (obsA := obsA) (obsB := obsB)))
      (target_obs := (targetAB (targetA := targetA) (targetB := targetB)))
      (h := h) (k := k) (step := step) hSep) hConst

/-!
## (1) Diagonal obstruction certifies marginal no-go (two interfaces)

This is just the generic `LagEvent → ¬ ObsPredictsStep`, packaged for two interfaces.
-/

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

/-!
## (2) Bridging no-go to explicit separation, and quantifying the joint repair

This closes the longer operational chain:

* no-go on `obsA` + finitary fiber data + decidability ⇒ explicit `StepSeparatesFiber` on `obsA`,
* no-go on `obsB` + finitary fiber data + decidability ⇒ explicit `StepSeparatesFiber` on `obsB`,
* exact joint compatibility dimension ⇒ canonical finite mediator on the joint interface, with minimality.

The mediator part uses `CompatDimEq … n` on `obsAB` (the joint interface).
-/

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
    (hDimAB : CompatDimEq (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) step n) :
    StepSeparatesFiber (P := P) sem obsA targetA step
      ∧ StepSeparatesFiber (P := P) sem obsB targetB step
      ∧ (RefiningLift (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
          (targetAB (targetA := targetA) (targetB := targetB)) h step n
        ∧ ∀ m : Nat, m < n →
            ¬ RefiningLift (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
              (targetAB (targetA := targetA) (targetB := targetB)) h step m) := by
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
      RefiningLift (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
        (targetAB (targetA := targetA) (targetB := targetB)) h step n :=
    refiningLift_of_compatDimEq
      (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) step n hDimAB
  have hNoSmaller :
      ∀ m : Nat, m < n →
        ¬ RefiningLift (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
          (targetAB (targetA := targetA) (targetB := targetB)) h step m :=
    no_smaller_refiningLift_of_compatDimEq
      (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) step n hDimAB
  exact ⟨hSepA, hSepB, ⟨hLift, hNoSmaller⟩⟩

/-!
## (3) Optional: in the binary case, forced mediation yields a causal signature

This packages the “(separation + `Fin 2` lift) ⇒ intervention signature” theorem for the joint interface.
-/

theorem jointLift2_yields_causalSignature2
    (hSepAB :
      StepSeparatesFiber (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
        (targetAB (targetA := targetA) (targetB := targetB)) step)
    (hDimAB2 : CompatDimEq (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) step 2) :
    CausalSignature2 (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) (h := h) step := by
  have hLift2 :
      RefiningLift (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
        (targetAB (targetA := targetA) (targetB := targetB)) h step 2 :=
    refiningLift_of_compatDimEq
      (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) step 2 hDimAB2
  exact causalSignature2_of_stepSeparatesFiber_of_refiningLift2
    (P := P) (sem := sem)
    (obs := (obsAB (obsA := obsA) (obsB := obsB)))
    (target_obs := (targetAB (targetA := targetA) (targetB := targetB)))
    (h := h) (k := k) (step := step) hSepAB hLift2

/-!
## (4) End-to-end wrapper: joint separation + marginal irreducibility + minimal joint mediator (+ causal if `n=2`)

This packages the strongest “single theorem” form expected operationally:

* joint separation (dynamic truth varies on the joint fiber),
* impossibility of left-only and right-only prediction of the joint truth,
* existence and minimality of a canonical joint finite mediator (`Fin n`),
* and (optionally) the binary intervention signature.
-/

theorem endToEnd_joint
    {n : Nat}
    (hSepAB :
      StepSeparatesFiber (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
        (targetAB (targetA := targetA) (targetB := targetB)) step)
    (hDimAB : CompatDimEq (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) step n) :
    (¬ LeftObsPredictsJointStep (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
        (targetA := targetA) (targetB := targetB) (h := h) (k := k) step)
      ∧
      (¬ RightObsPredictsJointStep (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
        (targetA := targetA) (targetB := targetB) (h := h) (k := k) step)
      ∧
      (RefiningLift (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
          (targetAB (targetA := targetA) (targetB := targetB)) h step n
        ∧ ∀ m : Nat, m < n →
            ¬ RefiningLift (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
              (targetAB (targetA := targetA) (targetB := targetB)) h step m) := by
  refine ⟨?_, ?_, ?_⟩
  · exact not_leftObsPredictsJointStep_of_stepSeparatesJointFiber
      (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step hSepAB
  · exact not_rightObsPredictsJointStep_of_stepSeparatesJointFiber
      (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step hSepAB
  · have hLift :
        RefiningLift (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
          (targetAB (targetA := targetA) (targetB := targetB)) h step n :=
      refiningLift_of_compatDimEq
        (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
        (targetAB (targetA := targetA) (targetB := targetB)) step n hDimAB
    have hNoSmaller :
        ∀ m : Nat, m < n →
          ¬ RefiningLift (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
            (targetAB (targetA := targetA) (targetB := targetB)) h step m :=
      no_smaller_refiningLift_of_compatDimEq
        (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
        (targetAB (targetA := targetA) (targetB := targetB)) step n hDimAB
    exact ⟨hLift, hNoSmaller⟩

theorem not_mediatorDescendsLeft_of_stepSeparatesJointFiber
    {n : Nat}
    (hSep :
      StepSeparatesFiber (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
        (targetAB (targetA := targetA) (targetB := targetB)) step)
    (L : RefiningLiftData (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) h step n) :
    ¬ MediatorDescendsLeft (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
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
      StepSeparatesFiber (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
        (targetAB (targetA := targetA) (targetB := targetB)) step)
    (L : RefiningLiftData (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) h step n) :
    ¬ MediatorDescendsRight (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step L := by
  apply not_mediatorDescendsRight_of_not_rightObsPredictsJointStep
    (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
    (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step) L
  exact not_rightObsPredictsJointStep_of_stepSeparatesJointFiber
    (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
    (targetA := targetA) (targetB := targetB) (h := h) (k := k) step hSep

/-!
## (5) End-to-end wrapper (maximal form used in the thesis narrative)

This closes the “single spine theorem” form that mentions:

* **two marginal diagonal obstructions** (lag events) and their constructive separation witnesses;
* **joint separation** (the same joint dynamic truth varies on the joint fiber);
* **irreducibility** of the joint truth to each marginal projection;
* **minimal finite mediator** on the joint interface; and
* (optionally, when `n = 2`) the **intervention signature**.
-/

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
      StepSeparatesFiber (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
        (targetAB (targetA := targetA) (targetB := targetB)) step)
    (hDimAB : CompatDimEq (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) step n) :
    StepSeparatesFiber (P := P) sem obsA targetA step
      ∧ StepSeparatesFiber (P := P) sem obsB targetB step
      ∧ (¬ LeftObsPredictsJointStep (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
          (targetA := targetA) (targetB := targetB) (h := h) (k := k) step)
      ∧ (¬ RightObsPredictsJointStep (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
          (targetA := targetA) (targetB := targetB) (h := h) (k := k) step)
      ∧ (RefiningLift (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
          (targetAB (targetA := targetA) (targetB := targetB)) h step n
        ∧ ∀ m : Nat, m < n →
            ¬ RefiningLift (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
              (targetAB (targetA := targetA) (targetB := targetB)) h step m) := by
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
      StepSeparatesFiber (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
        (targetAB (targetA := targetA) (targetB := targetB)) step)
    (hDimAB2 : CompatDimEq (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) step 2) :
    (StepSeparatesFiber (P := P) sem obsA targetA step
      ∧ StepSeparatesFiber (P := P) sem obsB targetB step
      ∧ (¬ LeftObsPredictsJointStep (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
          (targetA := targetA) (targetB := targetB) (h := h) (k := k) step)
      ∧ (¬ RightObsPredictsJointStep (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
          (targetA := targetA) (targetB := targetB) (h := h) (k := k) step)
      ∧ (RefiningLift (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
          (targetAB (targetA := targetA) (targetB := targetB)) h step 2
        ∧ ∀ m : Nat, m < 2 →
            ¬ RefiningLift (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
              (targetAB (targetA := targetA) (targetB := targetB)) h step m))
      ∧
      CausalSignature2 (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
        (targetAB (targetA := targetA) (targetB := targetB)) (h := h) step := by
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

/-!
## (6) Packaging as a named invariant (for synthesis / documentation)

`COFRS/Synthesis.lean` defines `PrimitiveHolonomy.JointIrreducibleMediationProfile`, a lightweight
predicate intended as a reusable **joint-level** invariant name:

* it packages separation and minimal finite repairability on the joint interface `obsAB`,
* and irreducibility of predicting the **joint** truth from either marginal projection.

It is not the full narrative wrapper: in particular, it does not include marginal diagonal
certification (`LagEvent` on each margin) nor the constructive extraction of marginal separation
from marginal no-go statements. Those are bundled in `endToEnd_full` / `endToEnd_full_with_causalSignature2`.

The lemmas below show:

* how the joint spine implies the joint-level profile; and
* how the profile yields the strongest “irreducibility” consequences used in narrative statements
  (non-descent of the mediator to either margin, and in the binary case a causal signature).
-/

theorem jointIrreducibleMediationProfile_of_sep_and_dim
    {n : Nat}
    (hSepAB :
      StepSeparatesFiber (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
        (targetAB (targetA := targetA) (targetB := targetB)) step)
    (hDimAB : CompatDimEq (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) step n) :
    PrimitiveHolonomy.JointIrreducibleMediationProfile (P := P) sem obsA obsB targetA targetB step n := by
  have hJoint :=
    endToEnd_joint
      (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step)
      (n := n) hSepAB hDimAB
  exact ⟨hSepAB, hJoint.1, hJoint.2.1, hDimAB⟩

theorem not_mediatorDescendsLeft_of_jointIrreducibleMediationProfile
    {n : Nat}
    (hProf : PrimitiveHolonomy.JointIrreducibleMediationProfile (P := P) sem obsA obsB targetA targetB step n)
    (L : RefiningLiftData (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) h step n) :
    ¬ MediatorDescendsLeft (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step L := by
  exact not_mediatorDescendsLeft_of_stepSeparatesJointFiber
    (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
    (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step)
    hProf.1 L

theorem not_mediatorDescendsRight_of_jointIrreducibleMediationProfile
    {n : Nat}
    (hProf : PrimitiveHolonomy.JointIrreducibleMediationProfile (P := P) sem obsA obsB targetA targetB step n)
    (L : RefiningLiftData (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) h step n) :
    ¬ MediatorDescendsRight (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (targetB := targetB) (h := h) (k := k) step L := by
  exact not_mediatorDescendsRight_of_stepSeparatesJointFiber
    (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
    (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step)
    hProf.1 L

theorem causalSignature2_of_jointIrreducibleMediationProfile2
    (hProf : PrimitiveHolonomy.JointIrreducibleMediationProfile (P := P) sem obsA obsB targetA targetB step 2) :
    CausalSignature2 (P := P) sem (obsAB (obsA := obsA) (obsB := obsB))
      (targetAB (targetA := targetA) (targetB := targetB)) (h := h) step := by
  exact jointLift2_yields_causalSignature2
    (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
    (targetA := targetA) (targetB := targetB) (h := h) (k := k) (step := step)
    hProf.1 hProf.2.2.2

/-!
## Appendix: a finitary “correlation regime” (uniform error lower bound)

The repository’s core definitions are not probabilistic: they are structural and fiber-based.
However, the *design-level* meaning of “correlation-only” used in experiments can be captured
constructively in a fully finitary way:

* fix a finite fiber `Ω := FiberPt obs target_obs h`,
* equip it with the uniform distribution (counting measure),
* and consider predictors that depend **only** on the observable interface `obs`.

If the step separates the fiber (`StepSeparatesFiber`), then any `obs`-only predictor must make
at least one mistake on `Ω`. Under the uniform distribution, this is a strictly positive error
probability.

This appendix formalizes the corresponding *strictly finitary* statement:
nonzero error count (hence nonzero uniform error rate) for any `obs`-only Boolean predictor.
-/

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
      (compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
          (h' := h') (step' := step') decCompat x)

/--
Appendix notion ("correlational" in the intended non-statistical sense):

`pred : V' → Bool` is *correlationally correct* if it decides the dynamic truth
using only the observable interface `obs`.

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
If there is **no** Boolean misclassification anywhere on the fiber, then the rule is
correlationally correct (it exactly matches `compatBool` pointwise).

This is the missing bridge needed to upgrade “no perfect obs-only predictor” into
an explicit “at least one mistake”.
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
  -- unfold `misBool` by cases on the prediction bit
  cases hb : pred (obs x.1) with
  | false =>
      -- `misBool = compatBool` in this branch, so `compatBool = false` and hence `pred = compatBool`.
      have hcb :
          compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
            (h' := h') (step' := step') decCompat x = false := by
        have hmis' := hmis
        dsimp [misBool] at hmis'
        rw [hb] at hmis'
        exact hmis'
      -- goal is `false = compatBool ...`, so use symmetry of `hcb`
      exact Eq.symm hcb
  | true =>
      -- `misBool = Bool.not (compatBool)` in this branch, so `compatBool = true`.
      have hnot :
          Bool.not (compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
              (h' := h') (step' := step') decCompat x) = false := by
        have hmis' := hmis
        dsimp [misBool] at hmis'
        rw [hb] at hmis'
        exact hmis'
      -- show `compatBool ... = true` by cases on it
      cases hc :
          compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
            (h' := h') (step' := step') decCompat x with
      | false =>
          -- `hnot` becomes `Bool.not false = false`, but `Bool.not false = true`.
          have hnot' := hnot
          rw [hc] at hnot'
          have hNotFalse : Bool.not false = true := rfl
          have hcontra : true = false := Eq.trans hNotFalse.symm hnot'
          cases hcontra
      | true =>
          -- goal is `true = true`
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
at **some explicit** point of the fiber.
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
  rcases hSep with ⟨xT, xF, hxne, hxT, hxF⟩
  -- The observable is constant on the fiber, hence `pred (obs x) = pred (target_obs h')` for both points.
  have hxTobs : obs xT.1 = target_obs h' := xT.2
  have hxFobs : obs xF.1 = target_obs h' := xF.2
  cases hb : pred (target_obs h') with
  | true =>
    -- predictor says "true" everywhere on the fiber, so it must fail on the incompatible witness.
    refine ⟨xF, ?_⟩
    have hbF : pred (obs xF.1) = true := by
      rw [hxFobs]
      exact hb
    have hCompatFalse :
        compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
          (h' := h') (step' := step') decCompat xF = false := by
      -- `compatBool = true` would contradict `hxF`.
      cases hc :
          compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
            (h' := h') (step' := step') decCompat xF with
      | false => rfl
      | true =>
          have hC : Compatible (P := P) sem' obs target_obs step' xF :=
            (compatBool_eq_true_iff (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
              (h' := h') (step' := step') decCompat xF).1 hc
          exact False.elim (hxF hC)
    -- `misBool = Bool.not (compatBool)` in this branch, hence it is true.
    have hbScr : pred (obs xF.1) = true := hbF
    cases hpred : pred (obs xF.1) with
    | false =>
        have : false = true := Eq.trans hpred.symm hbScr
        cases this
    | true =>
        -- reduce to `Bool.not false = true`
        unfold misBool
        rw [hpred, hCompatFalse]
        rfl
  | false =>
    -- predictor says "false" everywhere on the fiber, so it must fail on the compatible witness.
    refine ⟨xT, ?_⟩
    have hbT : pred (obs xT.1) = false := by
      rw [hxTobs]
      exact hb
    have hCompatTrue :
        compatBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
          (h' := h') (step' := step') decCompat xT = true := by
      -- `compatBool = false` would contradict `hxT`.
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
          -- contradiction with `hc : compatBool ... = false`
          have hTrue' := hTrue
          rw [hc] at hTrue'
          cases hTrue'
    -- `misBool = compatBool` in this branch, hence it is true.
    have hbScr : pred (obs xT.1) = false := hbT
    cases hpred : pred (obs xT.1) with
    | true =>
        have : true = false := Eq.trans hpred.symm hbScr
        cases this
    | false =>
        unfold misBool
        rw [hpred, hCompatTrue]

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
      · -- witness is the last index
        have hiLast : i = lastFin n := by
          have hLastVal : (lastFin n).val = n := rfl
          apply Fin.ext
          rw [hLastVal]
          exact hLast
        have hLastTrue : f (lastFin n) = true := by
          -- rewrite the witness equality in `hi`
          have hi' := hi
          rw [hiLast] at hi'
          exact hi'
        -- the last addend contributes 1, hence the total is positive
        have hPos : 0 < countTrue n (fun t : Fin n => f (liftFin (n := n) t)) + 1 := by
          -- `0 < a+1` for any `a` (rewrite `0 < Nat.succ a`)
          have h : 0 < Nat.succ (countTrue n (fun t : Fin n => f (liftFin (n := n) t))) :=
            Nat.zero_lt_succ _
          have hEq :
              Nat.succ (countTrue n (fun t : Fin n => f (liftFin (n := n) t))) =
                countTrue n (fun t : Fin n => f (liftFin (n := n) t)) + 1 :=
            Nat.succ_eq_add_one _
          have h' := h
          rw [hEq] at h'
          exact h'
        -- unfold `countTrue` at `Nat.succ n` and rewrite the last match using `hLastTrue`
        unfold countTrue
        -- goal is now `0 < countTrue n ... + match f (lastFin n) with ...`
        -- and `hLastTrue` forces the match to be `1`
        -- so we can finish by rewriting and using `hPos`.
        rw [hLastTrue]
        exact hPos
      · -- witness is in the first `n` indices
        have hle : i.val ≤ n := Nat.le_of_lt_succ i.isLt
        have hlt : i.val < n := Nat.lt_of_le_of_ne hle hLast
        let j : Fin n := ⟨i.val, hlt⟩
        have hj : f (liftFin (n := n) j) = true := by
          have hij : liftFin (n := n) j = i := by
            apply Fin.ext
            rfl
          have hi' := hi
          -- rewrite `hi : f i = true` along `hij`
          rw [← hij] at hi'
          exact hi'
        have : 0 < countTrue n (fun t : Fin n => f (liftFin (n := n) t)) :=
          ih ⟨j, hj⟩
        -- then the total is positive regardless of the last addend
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
  -- turn the fiber witness into a `Fin E.N` witness for the counted predicate
  have hAtI :
      (fun j : Fin E.N =>
          misBool (P := P) (sem' := sem') (obs := obs) (target_obs := target_obs)
            (h' := h') (step' := step') decCompat pred (E.enum j)) i = true := by
    -- rewrite `hx` along `hi : E.enum i = x`
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
  have hOr :=
    PrimitiveHolonomy.obsPredictsStep_or_stepSeparatesFiber_of_fiberEnum
      (P := P) (sem := sem') (obs := obs) (target_obs := target_obs)
      (step := step') E decCompat
  cases hOr with
  | inl hObs =>
      exact False.elim (hNo hObs)
  | inr hSep =>
      exact errCount_pos_of_stepSeparatesFiber (P := P) (sem' := sem') (obs := obs)
        (target_obs := target_obs) (h' := h') (step' := step') (E := E)
        (decCompat := decCompat) hSep pred

end CorrelationAppendix

end TwoInterfaces

end Examples
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.Examples.compatibleA_of_compatibleAB
#print axioms PrimitiveHolonomy.Examples.compatibleB_of_compatibleAB
#print axioms PrimitiveHolonomy.Examples.leftObsPredictsJointStep_of_mediatorDescendsLeft
#print axioms PrimitiveHolonomy.Examples.rightObsPredictsJointStep_of_mediatorDescendsRight
#print axioms PrimitiveHolonomy.Examples.not_mediatorDescendsLeft_of_stepSeparatesJointFiber
#print axioms PrimitiveHolonomy.Examples.not_mediatorDescendsRight_of_stepSeparatesJointFiber
#print axioms PrimitiveHolonomy.Examples.not_leftObsPredictsJointStep_of_stepSeparatesJointFiber
#print axioms PrimitiveHolonomy.Examples.not_rightObsPredictsJointStep_of_stepSeparatesJointFiber
#print axioms PrimitiveHolonomy.Examples.double_noGo_of_lagEvent
#print axioms PrimitiveHolonomy.Examples.double_noGo_to_separation_and_minimalJointLift
#print axioms PrimitiveHolonomy.Examples.jointLift2_yields_causalSignature2
#print axioms PrimitiveHolonomy.Examples.endToEnd_joint
#print axioms PrimitiveHolonomy.Examples.endToEnd_full
#print axioms PrimitiveHolonomy.Examples.endToEnd_full_with_causalSignature2
#print axioms PrimitiveHolonomy.Examples.jointIrreducibleMediationProfile_of_sep_and_dim
#print axioms PrimitiveHolonomy.Examples.not_mediatorDescendsLeft_of_jointIrreducibleMediationProfile
#print axioms PrimitiveHolonomy.Examples.not_mediatorDescendsRight_of_jointIrreducibleMediationProfile
#print axioms PrimitiveHolonomy.Examples.causalSignature2_of_jointIrreducibleMediationProfile2
#print axioms PrimitiveHolonomy.Examples.compatBool
#print axioms PrimitiveHolonomy.Examples.compatBool_eq_true_iff
#print axioms PrimitiveHolonomy.Examples.misBool
#print axioms PrimitiveHolonomy.Examples.correlationallyCorrect_of_no_misBool
#print axioms PrimitiveHolonomy.Examples.CorrelationallyCorrect
#print axioms PrimitiveHolonomy.Examples.obsPredictsStep_of_correlationallyCorrect
#print axioms PrimitiveHolonomy.Examples.not_correlationallyCorrect_of_not_obsPredictsStep
#print axioms PrimitiveHolonomy.Examples.exists_misBool_of_stepSeparatesFiber
#print axioms PrimitiveHolonomy.Examples.BoolCount.countTrue
#print axioms PrimitiveHolonomy.Examples.BoolCount.countTrue_pos_of_exists_true
#print axioms PrimitiveHolonomy.Examples.errCount
#print axioms PrimitiveHolonomy.Examples.errCount_pos_of_exists_misBool
#print axioms PrimitiveHolonomy.Examples.errCount_pos_of_stepSeparatesFiber
#print axioms PrimitiveHolonomy.Examples.errCount_pos_of_not_obsPredictsStep
/- AXIOM_AUDIT_END -/
