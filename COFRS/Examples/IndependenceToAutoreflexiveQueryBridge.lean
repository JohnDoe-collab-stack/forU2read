import COFRS.Examples.IndependenceRelationMediationChain
import COFRS.Examples.AutoreflexiveQueryArchitecture

/-!
# Independence to autoreflexive query (minimal bridge)

This file is a minimal bridge between:

* `COFRS/Examples/IndependenceRelationMediationChain.lean` (dynamic non-closure on a marginal fiber)
* `COFRS/Examples/AutoreflexiveQueryArchitecture.lean` (query-loop architectural signature)

Scope:

This bridge does not attempt to restate the full finite mediator story (`CompatDimEq` / `RefiningLift`)
of the previous file. Instead, it formalizes a simpler mechanism:

* a dynamic truth is posed on the left fiber (`obsA`),
* the left margin alone does not close it (`StepSeparatesFiber`),
* a query requests the second margin (`obsB`) as a response,
* and the post-query state carries enough information to decide the left-fiber truth.

All proofs are constructive; see the `AXIOM_AUDIT` block at the end.
-/

namespace PrimitiveHolonomy
namespace Examples

universe u w

variable {P : Type u}

section MinimalBridge

variable {S VA VB : Type w}
variable (obsA : S → VA) (obsB : S → VB)
variable (targetA : P → VA)
variable (h : P)

variable (defaultB : VB)
variable (decAB : VA × VB → Bool)

abbrev BridgeOut : Type w := ULift.{w} Bool
abbrev out (b : Bool) : BridgeOut := ⟨b⟩

/--
A minimal query architecture on the left fiber.

World:
* `FiberPt obsA targetA h` (the left fiber is fixed)

Loop:
* `query` is constant `true` (always request `obsB`)
* the forced action `false` returns `defaultB` (a "no-query" branch)
* post-state stores `(targetA h, response)`
* decision is read from `decAB`
-/
def queryRepairBySecondMargin
    (obsA : S → VA) (obsB : S → VB) (targetA : P → VA) (h0 : P)
    (defaultB : VB) (decAB : VA × VB → Bool) : AutoreflexiveQueryArchitecture where
  World := FiberPt (P := P) obsA targetA h0
  HistoryVisible := VA
  BypassVisible := PUnit
  State := VA × VB
  Action := Bool
  Response := VB
  Output := BridgeOut
  historyVisible := fun _ => targetA h0
  bypassVisible := fun _ => PUnit.unit
  encode := fun vA => (vA, defaultB)
  query := fun _ => true
  env := fun world action =>
    if action then obsB world.1 else defaultB
  update := fun state response => (state.1, response)
  decide := fun s => out (decAB s)

namespace QueryRepairBySecondMargin

local notation "Arch" =>
  queryRepairBySecondMargin (P := P) obsA obsB targetA h defaultB decAB

section ArchSimp

/--
`query` is constant `true`, so the chosen action is always `true`.
-/
@[simp] theorem chosenAction_eq_true (world : AutoreflexiveQueryArchitecture.World Arch) :
    AutoreflexiveQueryArchitecture.chosenAction Arch world = true := by
  rfl

@[simp] theorem preState_eq (world : AutoreflexiveQueryArchitecture.World Arch) :
    AutoreflexiveQueryArchitecture.preState Arch world = (targetA h, defaultB) := by
  rfl

@[simp] theorem runUnder_true (world : AutoreflexiveQueryArchitecture.World Arch) :
    AutoreflexiveQueryArchitecture.runUnder Arch world true =
      out (decAB (targetA h, obsB world.1)) := by
  rfl

@[simp] theorem runUnder_false (world : AutoreflexiveQueryArchitecture.World Arch) :
    AutoreflexiveQueryArchitecture.runUnder Arch world false =
      out (decAB (targetA h, defaultB)) := by
  rfl

@[simp] theorem run_eq (world : AutoreflexiveQueryArchitecture.World Arch) :
    AutoreflexiveQueryArchitecture.run Arch world =
      out (decAB (targetA h, obsB world.1)) := by
  rfl

end ArchSimp

section WithHistoryGraph

variable [HistoryGraph P]
variable (sem : Semantics P S)
variable {k : P} (step : HistoryGraph.Path h k)

/--
Correctness of `decAB` as a decision rule for the left-fiber dynamic truth,
after enriching the left observation by the response `obsB`.
-/
def CorrectOnLeftFiber
    (sem : Semantics P S) (obsA : S → VA) (obsB : S → VB) (targetA : P → VA)
    (h : P) {k : P} (step : HistoryGraph.Path h k) (decAB : VA × VB → Bool) : Prop :=
  ∀ world : FiberPt (P := P) obsA targetA h,
    (decAB (targetA h, obsB world.1) = true) ↔ Compatible (P := P) sem obsA targetA step world

theorem not_decisionFactorsThroughPreStateChosen_of_stepSeparatesFiber_of_correct
    (hSep : StepSeparatesFiber (P := P) sem obsA targetA step)
    (hCorr :
      CorrectOnLeftFiber (P := P) (S := S) (VA := VA) (VB := VB)
        sem obsA obsB targetA h step decAB) :
    ¬ AutoreflexiveQueryArchitecture.DecisionFactorsThroughPreStateChosen Arch := by
  intro hCollapse
  rcases hSep with ⟨x, x', _hne, hComp, hNotComp⟩
  have hxTrue : AutoreflexiveQueryArchitecture.run Arch x = out true := by
    have hDec : decAB (targetA h, obsB x.1) = true := (hCorr x).2 hComp
    have hRun : AutoreflexiveQueryArchitecture.run Arch x =
        out (decAB (targetA h, obsB x.1)) := by
      rfl
    have : out (decAB (targetA h, obsB x.1)) = out true :=
      congrArg out hDec
    exact hRun.trans this
  have hx'False : AutoreflexiveQueryArchitecture.run Arch x' = out false := by
    cases hb : decAB (targetA h, obsB x'.1) with
    | false =>
        have hRun : AutoreflexiveQueryArchitecture.run Arch x' =
            out (decAB (targetA h, obsB x'.1)) := by
          rfl
        have : out (decAB (targetA h, obsB x'.1)) = out false :=
          congrArg out hb
        exact hRun.trans this
    | true =>
        have hx'Comp : Compatible (P := P) sem obsA targetA step x' := (hCorr x').1 hb
        exact False.elim (hNotComp hx'Comp)
  rcases hCollapse with ⟨decidePre, hCollapse⟩
  have hRunEq :
      AutoreflexiveQueryArchitecture.run Arch x =
        AutoreflexiveQueryArchitecture.run Arch x' := by
    calc
      AutoreflexiveQueryArchitecture.run Arch x =
          decidePre (AutoreflexiveQueryArchitecture.preState Arch x) := hCollapse x
      _ = decidePre (AutoreflexiveQueryArchitecture.preState Arch x') := by
        rfl
      _ = AutoreflexiveQueryArchitecture.run Arch x' := (hCollapse x').symm
  have : true = false := by
    have hEqOut : out true = out false :=
      hxTrue.symm.trans (hRunEq.trans hx'False)
    exact congrArg ULift.down hEqOut
  cases this

theorem existsAlternativeActionDecisionEffect_of_stepSeparatesFiber_of_correct
    (hSep : StepSeparatesFiber (P := P) sem obsA targetA step)
    (hCorr :
      CorrectOnLeftFiber (P := P) (S := S) (VA := VA) (VB := VB)
        sem obsA obsB targetA h step decAB) :
    AutoreflexiveQueryArchitecture.ExistsAlternativeActionDecisionEffect Arch := by
  rcases hSep with ⟨x, x', _hne, hComp, hNotComp⟩
  have hxRunTrue : AutoreflexiveQueryArchitecture.run Arch x = out true := by
    have hDec : decAB (targetA h, obsB x.1) = true := (hCorr x).2 hComp
    have hRun : AutoreflexiveQueryArchitecture.run Arch x =
        out (decAB (targetA h, obsB x.1)) := by
      rfl
    have : out (decAB (targetA h, obsB x.1)) = out true :=
      congrArg out hDec
    exact hRun.trans this
  have hx'RunFalse : AutoreflexiveQueryArchitecture.run Arch x' = out false := by
    cases hb : decAB (targetA h, obsB x'.1) with
    | false =>
        have hRun : AutoreflexiveQueryArchitecture.run Arch x' =
            out (decAB (targetA h, obsB x'.1)) := by
          rfl
        have : out (decAB (targetA h, obsB x'.1)) = out false :=
          congrArg out hb
        exact hRun.trans this
    | true =>
        have hx'Comp : Compatible (P := P) sem obsA targetA step x' := (hCorr x').1 hb
        exact False.elim (hNotComp hx'Comp)
  cases hc : decAB (targetA h, defaultB) with
  | false =>
      refine ⟨x, false, ?_, ?_⟩
      · intro hEq
        have hChosen : AutoreflexiveQueryArchitecture.chosenAction Arch x = true := by
          rfl
        have : (false : Bool) = true := hEq.trans hChosen
        cases this
      · intro hEq
        have hUnder : AutoreflexiveQueryArchitecture.runUnder Arch x false = out false := by
          have hUnder0 : AutoreflexiveQueryArchitecture.runUnder Arch x false =
              out (decAB (targetA h, defaultB)) := by
            rfl
          have : out (decAB (targetA h, defaultB)) = out false :=
            congrArg out hc
          exact hUnder0.trans this
        have : true = false := by
          have hEqOut : out true = out false :=
            hxRunTrue.symm.trans ((Eq.symm hEq).trans hUnder)
          exact congrArg ULift.down hEqOut
        cases this
  | true =>
      refine ⟨x', false, ?_, ?_⟩
      · intro hEq
        have hChosen : AutoreflexiveQueryArchitecture.chosenAction Arch x' = true := by
          rfl
        have : (false : Bool) = true := hEq.trans hChosen
        cases this
      · intro hEq
        have hUnder : AutoreflexiveQueryArchitecture.runUnder Arch x' false = out true := by
          have hUnder0 : AutoreflexiveQueryArchitecture.runUnder Arch x' false =
              out (decAB (targetA h, defaultB)) := by
            rfl
          have : out (decAB (targetA h, defaultB)) = out true :=
            congrArg out hc
          exact hUnder0.trans this
        have : true = false := by
          have hEqOut : out true = out false :=
            hUnder.symm.trans (hEq.trans hx'RunFalse)
          exact congrArg ULift.down hEqOut
        cases this

theorem not_decisionFactorsThroughPreStateUnder_of_stepSeparatesFiber_of_correct
    (hSep : StepSeparatesFiber (P := P) sem obsA targetA step)
    (hCorr :
      CorrectOnLeftFiber (P := P) (S := S) (VA := VA) (VB := VB)
        sem obsA obsB targetA h step decAB) :
    ¬ AutoreflexiveQueryArchitecture.DecisionFactorsThroughPreStateUnder Arch := by
  have hAlt : AutoreflexiveQueryArchitecture.ExistsAlternativeActionDecisionEffect Arch :=
    existsAlternativeActionDecisionEffect_of_stepSeparatesFiber_of_correct
      (P := P) (S := S) (VA := VA) (VB := VB) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (h := h) (step := step) (defaultB := defaultB) (decAB := decAB)
      hSep hCorr
  exact
    AutoreflexiveQueryArchitecture.not_decisionFactorsThroughPreStateUnder_of_existsAlternativeActionDecisionEffect
      Arch hAlt

theorem not_decisionRecoverableFromForbiddenChannel_of_stepSeparatesFiber_of_correct
    (hSep : StepSeparatesFiber (P := P) sem obsA targetA step)
    (hCorr :
      CorrectOnLeftFiber (P := P) (S := S) (VA := VA) (VB := VB)
        sem obsA obsB targetA h step decAB) :
    ¬ AutoreflexiveQueryArchitecture.DecisionRecoverableFromForbiddenChannel Arch := by
  intro hBypass
  rcases hBypass with ⟨decideBypass, hBypass⟩
  have hCollapse : AutoreflexiveQueryArchitecture.DecisionFactorsThroughPreStateChosen Arch := by
    refine ⟨fun _ => decideBypass PUnit.unit, ?_⟩
    intro world
    simpa using (hBypass world)
  exact
    not_decisionFactorsThroughPreStateChosen_of_stepSeparatesFiber_of_correct
      (P := P) (S := S) (VA := VA) (VB := VB) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (h := h) (step := step) (defaultB := defaultB) (decAB := decAB)
      hSep hCorr hCollapse

end WithHistoryGraph

end QueryRepairBySecondMargin

end MinimalBridge

end Examples
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.Examples.queryRepairBySecondMargin
#print axioms PrimitiveHolonomy.Examples.QueryRepairBySecondMargin.not_decisionFactorsThroughPreStateChosen_of_stepSeparatesFiber_of_correct
#print axioms PrimitiveHolonomy.Examples.QueryRepairBySecondMargin.existsAlternativeActionDecisionEffect_of_stepSeparatesFiber_of_correct
#print axioms PrimitiveHolonomy.Examples.QueryRepairBySecondMargin.not_decisionFactorsThroughPreStateUnder_of_stepSeparatesFiber_of_correct
#print axioms PrimitiveHolonomy.Examples.QueryRepairBySecondMargin.not_decisionRecoverableFromForbiddenChannel_of_stepSeparatesFiber_of_correct
/- AXIOM_AUDIT_END -/
