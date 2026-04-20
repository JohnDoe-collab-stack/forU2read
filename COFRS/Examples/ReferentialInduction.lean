import COFRS.Dynamics

/-!
# Referential induction (quotients, diagonal witnesses, forced mediation)

This file formalizes a minimal, constructive notion of "induction" used in the project.

Core idea:

* A quotient `q : X → Q` induces fibers ("same visible").
* A truth `T : X → Prop` is not closed by `q` if there exist `x ≠ x'` with `q x = q x'`
  but `T x` differs from `T x'`. This is a diagonal witness.
* If there exists a finite mediator `σ : X → Fin n` that decides `T`, then:
  - `σ` cannot descend to `q` (it cannot be a function of `q`), because `T` varies inside a fiber.
  - extending the quotient to `q' x := (q x, σ x)` closes `T`.

This file exposes the mechanism at three levels:

* Single-step repair (`InductionStep`): obstruction (diagonal witness) plus a finite mediator,
  yielding a forced quotient extension that closes the current truth.
* Re-targetable chains (`ReferentialDerivation`): after repairing a stage, the next stage may
  aim at a new truth `Tnext` on the extended quotient.
* Disciplined chains (`DisciplinedReferentialDerivation`): re-targeting is required to use the
  extension, witnessed by a diagonal obstruction for `Tnext` in the old quotient view.

The development is intentionally abstract (quotients and truths), and can be instantiated with
`Compatible` and `StepSeparatesFiber` from `COFRS/Dynamics.lean`. It also connects to the global
canonical mediator layer (`Sig`) by showing that step separation forbids any obs-only summary from
respecting `Sig`, while global signature compressibility (`CompatSigDimLe`) yields a local
induction step via a refining lift.

All proofs are constructive; see the `AXIOM_AUDIT` block at the end.
-/

namespace PrimitiveHolonomy
namespace Examples

universe u w uQ

variable {P : Type u} [HistoryGraph P]

/-!
## Abstract quotients and diagonal witnesses
-/

structure ReferentialProblem where
  X : Type w
  Q : Type w
  q : X → Q
  T : X → Prop

namespace ReferentialProblem

def Closes (R : ReferentialProblem) : Prop :=
  ∃ pred : R.Q → Prop, ∀ x : R.X, R.T x ↔ pred (R.q x)

def DiagonalWitness (R : ReferentialProblem) : Prop :=
  ∃ x x' : R.X, x ≠ x' ∧ R.q x = R.q x' ∧ R.T x ∧ ¬ R.T x'

def MediatesLe (R : ReferentialProblem) (n : Nat) : Prop :=
  ∃ (σ : R.X → Fin n) (predFin : Fin n → Prop),
    ∀ x : R.X, R.T x ↔ predFin (σ x)

def DescendsToQuot {n : Nat} (R : ReferentialProblem) (σ : R.X → Fin n) : Prop :=
  ∃ f : R.Q → Fin n, ∀ x : R.X, σ x = f (R.q x)

def retarget (R : ReferentialProblem) (T' : R.X → Prop) : ReferentialProblem where
  X := R.X
  Q := R.Q
  q := R.q
  T := T'

def extendQuot {n : Nat} (R : ReferentialProblem) (σ : R.X → Fin n) :
    ReferentialProblem where
  X := R.X
  Q := R.Q × Fin n
  q := fun x => (R.q x, σ x)
  T := R.T

theorem refines_extendQuot {n : Nat} (R : ReferentialProblem) (σ : R.X → Fin n) :
    ∃ π : (R.extendQuot σ).Q → R.Q, ∀ x : (R.extendQuot σ).X, R.q x = π ((R.extendQuot σ).q x) :=
by
  refine ⟨Prod.fst, ?_⟩
  intro x
  rfl

theorem closes_extendQuot_of_mediatesLe
    {n : Nat} (R : ReferentialProblem) (σ : R.X → Fin n) (predFin : Fin n → Prop)
    (hMed : ∀ x : R.X, R.T x ↔ predFin (σ x)) :
    (R.extendQuot σ).Closes := by
  refine ⟨(fun w : R.Q × Fin n => predFin w.2), ?_⟩
  intro x
  exact hMed x

theorem closes_of_descendsToQuot_of_mediatesLe
    {n : Nat} (R : ReferentialProblem)
    (σ : R.X → Fin n) (predFin : Fin n → Prop)
    (hMed : ∀ x : R.X, R.T x ↔ predFin (σ x))
    (hDesc : R.DescendsToQuot σ) :
    R.Closes := by
  rcases hDesc with ⟨f, hf⟩
  refine ⟨(fun q => predFin (f q)), ?_⟩
  intro x
  have hσ : σ x = f (R.q x) := hf x
  have hpred : predFin (σ x) ↔ predFin (f (R.q x)) :=
    PrimitiveHolonomy.iff_of_eq (congrArg predFin hσ)
  exact (hMed x).trans hpred

theorem not_closes_of_diagonalWitness (R : ReferentialProblem) :
    R.DiagonalWitness → ¬ R.Closes := by
  rintro ⟨x, x', _hxne, hq, hxT, hx'T⟩ hClose
  rcases hClose with ⟨pred, hpred⟩
  have hx : pred (R.q x) := (hpred x).1 hxT
  have hx' : pred (R.q x') := by
    have : pred (R.q x) ↔ pred (R.q x') := PrimitiveHolonomy.iff_of_eq (congrArg pred hq)
    exact (this.mp hx)
  have : R.T x' := (hpred x').2 hx'
  exact hx'T this

theorem not_descends_of_diagonalWitness_of_mediatesLe
    {n : Nat} (R : ReferentialProblem)
    (hDiag : R.DiagonalWitness)
    (σ : R.X → Fin n) (predFin : Fin n → Prop)
    (hMed : ∀ x : R.X, R.T x ↔ predFin (σ x)) :
    ¬ R.DescendsToQuot σ := by
  intro hDesc
  have hClose : R.Closes :=
    closes_of_descendsToQuot_of_mediatesLe (R := R) σ predFin hMed hDesc
  exact (not_closes_of_diagonalWitness (R := R) hDiag) hClose

end ReferentialProblem

/-!
## A single induction step (packaged)

`InductionStep` is data: it exhibits a diagonal witness for non-closure, and a finite mediator
that closes the truth. The key derived facts are:

* the mediator does not descend to the original quotient;
* extending the quotient by the mediator closes the truth.
-/

structure InductionStep where
  R : ReferentialProblem.{w}
  n : Nat
  σ : R.X → Fin n
  predFin : Fin n → Prop
  diag : R.DiagonalWitness
  mediates : ∀ x : R.X, R.T x ↔ predFin (σ x)

/-!
### Induction steps, parameterized by the stage

`InductionStep` packages the stage `R` as a field.
For some developments (for example, "the next stage is already repairable"), it is more convenient
to parameterize the induction step by its stage in the type.
-/

structure InductionStepOn (R : ReferentialProblem.{w}) where
  n : Nat
  σ : R.X → Fin n
  predFin : Fin n → Prop
  diag : R.DiagonalWitness
  mediates : ∀ x : R.X, R.T x ↔ predFin (σ x)

namespace InductionStepOn

def asInductionStep {R : ReferentialProblem.{w}} (I : InductionStepOn R) : InductionStep :=
  { R := R
    n := I.n
    σ := I.σ
    predFin := I.predFin
    diag := I.diag
    mediates := I.mediates }

def R' {R : ReferentialProblem.{w}} (I : InductionStepOn R) : ReferentialProblem.{w} :=
  R.extendQuot I.σ

theorem not_descends {R : ReferentialProblem.{w}} (I : InductionStepOn R) :
    ¬ R.DescendsToQuot I.σ :=
  ReferentialProblem.not_descends_of_diagonalWitness_of_mediatesLe R I.diag I.σ I.predFin I.mediates

theorem closes_extended {R : ReferentialProblem.{w}} (I : InductionStepOn R) :
    (I.R').Closes :=
  ReferentialProblem.closes_extendQuot_of_mediatesLe R I.σ I.predFin I.mediates

end InductionStepOn

namespace InductionStep

def R' (I : InductionStep) : ReferentialProblem.{w} :=
  I.R.extendQuot I.σ

theorem not_descends (I : InductionStep) :
    ¬ I.R.DescendsToQuot I.σ :=
  ReferentialProblem.not_descends_of_diagonalWitness_of_mediatesLe I.R I.diag I.σ I.predFin I.mediates

theorem closes_extended (I : InductionStep) :
    (I.R').Closes :=
  ReferentialProblem.closes_extendQuot_of_mediatesLe I.R I.σ I.predFin I.mediates

theorem refines_extended (I : InductionStep) :
    ∃ π : (I.R').Q → I.R.Q, ∀ x : (I.R').X, I.R.q x = π ((I.R').q x) :=
  ReferentialProblem.refines_extendQuot I.R I.σ

end InductionStep

/-!
## Induction chains (derivations)

`InductionStep` packages one forced referential extension.
`Derivation` is the corresponding notion of a finite, witness carrying chain.

This is intentionally not indexed by `Nat` or ordinals. It is a derivation tree whose
steps are justified by diagonal witnesses and mediation data.

Scope note:

* `Derivation` captures the finite, witness carrying core of the specification.
* Ordinal indexing and limit stages, if used later as an external bookkeeping layer,
  are out of scope of this file and are not needed to define the inductive mechanism.
-/

inductive Derivation : ReferentialProblem.{w} → Type (w + 1)
  | stop {R : ReferentialProblem.{w}} : R.Closes → Derivation R
  | next (I : InductionStep) : Derivation I.R' → Derivation I.R

/-!
## Induction chains with re-targeting

`Derivation` above keeps the same target truth `T` after extending the quotient.
This is sufficient to formalize one forced repair step, but it cannot encode the
iterative mechanism described in the specification, where the next stage may aim
at a new truth.

`StageTransition` and `ReferentialDerivation` add that missing degree of freedom:
after repairing `(R, T)`, one may move to the extended quotient while changing
the target truth to a new `Tnext`.
-/

structure StageTransition where
  I : InductionStep
  Tnext : I.R'.X → Prop

namespace StageTransition

def Rnext (J : StageTransition) : ReferentialProblem :=
  ReferentialProblem.retarget J.I.R' J.Tnext

/-- `oldView` is the "old quotient view" equipped with the next-stage truth `Tnext`.

It forgets the added mediator coordinate (the `Fin n` component of `extendQuot`), keeping only
the original quotient information while evaluating the new target truth. -/
def oldView (J : StageTransition) : ReferentialProblem :=
  { X := J.I.R'.X
    Q := J.I.R.Q
    q := fun x => (J.I.R'.q x).1
    T := J.Tnext }

/-- On the extended domain, the old view quotient is definitionally the original quotient. -/
@[simp] theorem oldView_q_eq (J : StageTransition) (x : J.I.R'.X) :
    (J.oldView).q x = J.I.R.q x := by
  rfl

/-- `UsesExtension` means: with the old quotient only, the new target truth has a diagonal
witness of non-closure. This is a positive (witness carrying) version of "not closed by the
old view"; it does not assert that the new target truth is closed by the extended quotient. -/
def UsesExtension (J : StageTransition) : Prop :=
  (J.oldView).DiagonalWitness

theorem not_closes_oldView_of_usesExtension (J : StageTransition) :
    J.UsesExtension → ¬ (J.oldView).Closes :=
  (ReferentialProblem.not_closes_of_diagonalWitness (R := J.oldView))

theorem refines_next (J : StageTransition) :
    ∃ π : (J.Rnext).Q → J.I.R.Q, ∀ x : (J.Rnext).X, J.I.R.q x = π ((J.Rnext).q x) := by
  simpa [Rnext, ReferentialProblem.retarget] using J.I.refines_extended

end StageTransition

inductive ReferentialDerivation : ReferentialProblem → Type (w + 1)
  | stop {R : ReferentialProblem} : R.Closes → ReferentialDerivation R
  | next (J : StageTransition) : ReferentialDerivation J.Rnext → ReferentialDerivation J.I.R

structure DisciplinedStageTransition extends StageTransition where
  usesExtension : StageTransition.UsesExtension toStageTransition

namespace DisciplinedStageTransition

def Rnext (J : DisciplinedStageTransition) : ReferentialProblem :=
  StageTransition.Rnext J.toStageTransition

def oldView (J : DisciplinedStageTransition) : ReferentialProblem :=
  StageTransition.oldView J.toStageTransition

theorem not_closes_oldView (J : DisciplinedStageTransition) :
    ¬ (J.oldView).Closes := by
  exact StageTransition.not_closes_oldView_of_usesExtension J.toStageTransition J.usesExtension

theorem refines_next (J : DisciplinedStageTransition) :
    ∃ π : (J.Rnext).Q → J.toStageTransition.I.R.Q, ∀ x : (J.Rnext).X,
      J.toStageTransition.I.R.q x = π ((J.Rnext).q x) :=
  StageTransition.refines_next J.toStageTransition

end DisciplinedStageTransition

inductive DisciplinedReferentialDerivation : ReferentialProblem → Type (w + 1)
  | stop {R : ReferentialProblem} : R.Closes → DisciplinedReferentialDerivation R
  | next (J : DisciplinedStageTransition) :
      DisciplinedReferentialDerivation J.Rnext → DisciplinedReferentialDerivation J.toStageTransition.I.R

/-!
## Self contained stage transitions

`DisciplinedStageTransition` provides a re targeting step together with a positive witness that the
new target truth is not already closed by the old quotient view (`UsesExtension`).

To make the induction mechanism deployable as a procedure, it is often useful to bundle, in the
same object, not only the re targeting but also a forced repair step for the next stage truth.
-/

structure DisciplinedStageTransitionWithRepair where
  J : DisciplinedStageTransition
  next : InductionStepOn J.Rnext

namespace DisciplinedStageTransitionWithRepair

def Rnext (K : DisciplinedStageTransitionWithRepair) : ReferentialProblem :=
  K.J.Rnext

def Rnext' (K : DisciplinedStageTransitionWithRepair) : ReferentialProblem :=
  K.next.R'

theorem next_not_descends (K : DisciplinedStageTransitionWithRepair) :
    ¬ K.Rnext.DescendsToQuot K.next.σ :=
  K.next.not_descends

theorem next_closes_extended (K : DisciplinedStageTransitionWithRepair) :
    K.Rnext'.Closes :=
  K.next.closes_extended

end DisciplinedStageTransitionWithRepair

/-!
## Instantiation with `Compatible` at a fixed step

We package a `Compatible`-based problem as an abstract `ReferentialProblem`.
This makes it possible to express "diagonal witness", "mediator", and "extension"
without changing the underlying dynamics definitions.
-/

section CompatibleInstantiation

variable {S V : Type w}
variable (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
variable {h k : P} (step : HistoryGraph.Path h k)

def compatibleProblem : ReferentialProblem.{w} where
  X := FiberPt (P := P) obs target_obs h
  Q := V
  -- On the fiber `FiberPt obs target_obs h`, `q` is definitionally constant.
  -- This captures the intended "fiber-local and step-local" obstruction.
  q := fun x => obs x.1
  T := fun x => Compatible (P := P) sem obs target_obs step x

/-!
### Global layer via the canonical mediator `Sig`

To incorporate the full canonical mediator layer without introducing explicit indices, we reuse
the project definitions from `COFRS/Dynamics.lean`:

* `Sig` is the canonical mediator at prefix `h`.
* `SigFactorsThrough σ` is the "respect of `Sig`" contract for a summary `σ`.
* `CompatSigDimLe` is the existence of a finite summary that is correct for every future step,
  and it implies `SigFactorsThrough` for that summary.

The key point for induction is that when a step separates the fiber, no obs-only (visible-only)
summary can respect `Sig`.
-/

theorem not_sigFactorsThrough_of_factorsThroughObs_of_stepSeparatesFiber
    {Q : Type uQ}
    (σ : FiberPt (P := P) obs target_obs h → Q)
    (hσ : ∃ f : V → Q, ∀ x, σ x = f (obs x.1))
    (hSep : StepSeparatesFiber (P := P) sem obs target_obs step) :
    ¬ SigFactorsThrough (P := P) sem obs target_obs (h := h) σ := by
  intro hFac
  rcases hSep with ⟨x, x', _hxne, hx, hx'⟩
  rcases hσ with ⟨f, hf⟩
  have hobs : obs x.1 = obs x'.1 := by
    have hx0 : obs x.1 = target_obs h := x.2
    have hx'0 : obs x'.1 = target_obs h := x'.2
    exact hx0.trans hx'0.symm
  have hEq : σ x = σ x' := by
    calc
      σ x = f (obs x.1) := hf x
      _ = f (obs x'.1) := congrArg f hobs
      _ = σ x' := (hf x').symm
  have hSig :
      ∀ s, Sig (P := P) sem obs target_obs x s ↔ Sig (P := P) sem obs target_obs x' s :=
    hFac (x := x) (x' := x') hEq
  let s : Future (P := P) h := ⟨k, step⟩
  have hStep := hSig s
  dsimp [Sig, CompatibleFuture] at hStep
  exact hx' (hStep.mp hx)

theorem exists_sigFactorsThrough_nonvisible_of_compatSigDimLe_of_stepSeparatesFiber
    {n : Nat}
    (hSig : CompatSigDimLe (P := P) sem obs target_obs (h := h) n)
    (hSep : StepSeparatesFiber (P := P) sem obs target_obs step) :
    ∃ σ : FiberPt (P := P) obs target_obs h → Fin n,
      SigFactorsThrough (P := P) sem obs target_obs (h := h) σ ∧
        ¬ (∃ f : V → Fin n, ∀ x, σ x = f (obs x.1)) := by
  rcases sigFactorsThrough_of_compatSigDimLe (P := P) sem obs target_obs (h := h) (n := n) hSig with
    ⟨σ, hσ⟩
  refine ⟨σ, hσ, ?_⟩
  intro hVis
  exact not_sigFactorsThrough_of_factorsThroughObs_of_stepSeparatesFiber (P := P) (sem := sem)
    (obs := obs) (target_obs := target_obs) (h := h) (k := k) (step := step) σ hVis hSep hσ

theorem diagonalWitness_of_stepSeparatesFiber
    (hSep : StepSeparatesFiber (P := P) sem obs target_obs step) :
    (compatibleProblem (sem := sem) (obs := obs) (target_obs := target_obs) (step := step)).DiagonalWitness := by
  rcases hSep with ⟨x, x', hxne, hx, hx'⟩
  refine ⟨x, x', hxne, ?_, hx, hx'⟩
  -- both lie in the same fiber at `h`
  have hx0 : obs x.1 = target_obs h := x.2
  have hx'0 : obs x'.1 = target_obs h := x'.2
  exact hx0.trans hx'0.symm

theorem diagonalWitness_of_lagEvent
    {k' : P}
    {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step' : HistoryGraph.Path h k')
    (hLag : LagEvent (P := P) sem obs target_obs α step') :
    (compatibleProblem (sem := sem) (obs := obs) (target_obs := target_obs) (step := step')).DiagonalWitness := by
  have hSep : StepSeparatesFiber (P := P) sem obs target_obs step' :=
    stepSeparatesFiber_of_lagEvent (P := P) sem obs target_obs α step' hLag
  exact diagonalWitness_of_stepSeparatesFiber (P := P) (sem := sem) (obs := obs)
    (target_obs := target_obs) (h := h) (k := k') (step := step') hSep

theorem stepSeparatesFiber_of_diagonalWitness
    (hDiag :
      (compatibleProblem (sem := sem) (obs := obs) (target_obs := target_obs) (step := step)).DiagonalWitness) :
    StepSeparatesFiber (P := P) sem obs target_obs step := by
  rcases hDiag with ⟨x, x', hxne, _hq, hx, hx'⟩
  exact ⟨x, x', hxne, hx, hx'⟩

def inductionStep_of_refiningLiftData
    {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k)
    {n : Nat}
    (L : RefiningLiftData (P := P) sem obs target_obs h step n)
    (hSep : StepSeparatesFiber (P := P) sem obs target_obs step) :
    InductionStep := by
  let R0 : ReferentialProblem.{w} :=
    compatibleProblem (sem := sem) (obs := obs) (target_obs := target_obs) (step := step)
  refine
    { R := R0
      n := n
      σ := (fun x : FiberPt (P := P) obs target_obs h => (L.extObs x).2)
      predFin := L.predFin
      diag :=
        diagonalWitness_of_stepSeparatesFiber (P := P) (sem := sem) (obs := obs)
          (target_obs := target_obs) (h := h) (k := k) (step := step) hSep
      mediates := ?_ }
  intro x
  simpa using (L.factors x)

theorem inductionStep_of_compatSigDimLe_of_stepSeparatesFiber
    {n : Nat}
    (hSig : CompatSigDimLe (P := P) sem obs target_obs (h := h) n)
    (hSep : StepSeparatesFiber (P := P) sem obs target_obs step) :
    ∃ I : InductionStep.{w}, I.n = n := by
  have hLift : RefiningLift (P := P) sem obs target_obs h step n :=
    refiningLift_of_compatSigDimLe (P := P) sem obs target_obs step n hSig
  rcases hLift with ⟨L⟩
  let R0 : ReferentialProblem.{w} :=
    compatibleProblem (sem := sem) (obs := obs) (target_obs := target_obs) (step := step)
  refine ⟨{ R := R0
            n := n
            σ := (fun x : FiberPt (P := P) obs target_obs h => (L.extObs x).2)
            predFin := L.predFin
            diag :=
              diagonalWitness_of_stepSeparatesFiber (P := P) (sem := sem) (obs := obs)
                (target_obs := target_obs) (h := h) (k := k) (step := step) hSep
            mediates := (by
              intro x
              simpa using (L.factors x)) }, rfl⟩

end CompatibleInstantiation

end Examples
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.Examples.InductionStep.not_descends
#print axioms PrimitiveHolonomy.Examples.InductionStep.closes_extended
#print axioms PrimitiveHolonomy.Examples.InductionStepOn.not_descends
#print axioms PrimitiveHolonomy.Examples.InductionStepOn.closes_extended
#print axioms PrimitiveHolonomy.Examples.DisciplinedStageTransitionWithRepair.next_closes_extended
#print axioms PrimitiveHolonomy.Examples.inductionStep_of_refiningLiftData
#print axioms PrimitiveHolonomy.Examples.ReferentialProblem.not_closes_of_diagonalWitness
#print axioms PrimitiveHolonomy.Examples.ReferentialProblem.closes_of_descendsToQuot_of_mediatesLe
#print axioms PrimitiveHolonomy.Examples.ReferentialProblem.not_descends_of_diagonalWitness_of_mediatesLe
#print axioms PrimitiveHolonomy.Examples.Derivation
#print axioms PrimitiveHolonomy.Examples.StageTransition
#print axioms PrimitiveHolonomy.Examples.StageTransition.oldView_q_eq
#print axioms PrimitiveHolonomy.Examples.ReferentialDerivation
#print axioms PrimitiveHolonomy.Examples.DisciplinedStageTransition
#print axioms PrimitiveHolonomy.Examples.DisciplinedReferentialDerivation
#print axioms PrimitiveHolonomy.Examples.diagonalWitness_of_lagEvent
#print axioms PrimitiveHolonomy.Examples.not_sigFactorsThrough_of_factorsThroughObs_of_stepSeparatesFiber
#print axioms PrimitiveHolonomy.Examples.exists_sigFactorsThrough_nonvisible_of_compatSigDimLe_of_stepSeparatesFiber
#print axioms PrimitiveHolonomy.Examples.inductionStep_of_compatSigDimLe_of_stepSeparatesFiber
/- AXIOM_AUDIT_END -/
