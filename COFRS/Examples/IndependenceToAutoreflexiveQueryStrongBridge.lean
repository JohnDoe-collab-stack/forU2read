import COFRS.Examples.IndependenceToAutoreflexiveQueryBridge

/-!
# Independence to autoreflexive query (strong bridge)

This file builds a stronger bridge than
`COFRS/Examples/IndependenceToAutoreflexiveQueryBridge.lean`.

Key difference:

* the minimal bridge fixes one left fiber `FiberPt obsA targetA h`, so `historyVisible` and `preState`
  are constant on the world, and the chosen action cannot vary across realized worlds;
* the strong bridge ranges over a family of left fibers, so `historyVisible`, `preState`, and
  `chosenAction` can vary, making the full `QueryLoopOperationality` profile attainable.

All proofs are constructive; see the `AXIOM_AUDIT` block at the end.
-/

namespace PrimitiveHolonomy
namespace Examples

universe u w

variable {P : Type u} [HistoryGraph P]

section StrongBridge

variable {S VA VB : Type w}
variable (sem : Semantics P S)
variable (obsA : S → VA) (obsB : S → VB)
variable (targetA : P → VA)
variable (stepAt : ∀ h : P, Σ k : P, HistoryGraph.Path h k)

variable (defaultB : VB)
variable (policy : VA → Bool)
variable (decAB : VA × VB → Bool)

abbrev StrongWorld : Type (max u w) :=
  Σ h : P, FiberPt (P := P) obsA targetA h

def queryRepairFamilyBySecondMargin
    (obsA : S → VA) (obsB : S → VB) (targetA : P → VA)
    (defaultB : VB) (policy : VA → Bool) (decAB : VA × VB → Bool) :
    AutoreflexiveQueryArchitecture where
  World := StrongWorld (P := P) obsA targetA
  HistoryVisible := VA
  BypassVisible := PUnit
  State := VA × VB
  Action := Bool
  Response := VB
  Output := BridgeOut
  historyVisible := fun w => targetA w.1
  bypassVisible := fun _ => PUnit.unit
  encode := fun vA => (vA, defaultB)
  query := fun s => policy s.1
  env := fun w action =>
    if action then obsB w.2.1 else defaultB
  update := fun state response => (state.1, response)
  decide := fun s => out (decAB s)

namespace QueryRepairFamilyBySecondMargin

local notation "ArchS" =>
  queryRepairFamilyBySecondMargin (P := P) obsA obsB targetA defaultB policy decAB

def GoodFiber (h : P) : Prop :=
  policy (targetA h) = true
    ∧ StepSeparatesFiber (P := P) sem obsA targetA (stepAt h).2
    ∧ QueryRepairBySecondMargin.CorrectOnLeftFiber (P := P)
        (S := S) (VA := VA) (VB := VB)
        sem obsA obsB targetA h (stepAt h).2 decAB

structure StrongBridgeHypotheses : Prop where
  exists_good : ∃ h : P, GoodFiber (P := P) (S := S) (VA := VA) (VB := VB)
    (sem := sem) (obsA := obsA) (obsB := obsB) (targetA := targetA) (stepAt := stepAt)
    (policy := policy) (decAB := decAB) h
  exists_false_world :
    ∃ h : P, policy (targetA h) = false ∧ Nonempty (FiberPt (P := P) obsA targetA h)
  exists_response_gap :
    ∃ w : StrongWorld (P := P) obsA targetA, obsB w.2.1 ≠ defaultB

omit [HistoryGraph P] in
@[simp] theorem chosenAction_eq_policy (w : AutoreflexiveQueryArchitecture.World ArchS) :
    AutoreflexiveQueryArchitecture.chosenAction ArchS w = policy (targetA w.1) := by
  rfl

omit [HistoryGraph P] in
@[simp] theorem preState_eq (w : AutoreflexiveQueryArchitecture.World ArchS) :
    AutoreflexiveQueryArchitecture.preState ArchS w = (targetA w.1, defaultB) := by
  rfl

omit [HistoryGraph P] in
@[simp] theorem env_true (w : AutoreflexiveQueryArchitecture.World ArchS) :
    AutoreflexiveQueryArchitecture.env ArchS w true = obsB w.2.1 := by
  rfl

omit [HistoryGraph P] in
@[simp] theorem env_false (w : AutoreflexiveQueryArchitecture.World ArchS) :
    AutoreflexiveQueryArchitecture.env ArchS w false = defaultB := by
  rfl

omit [HistoryGraph P] in
@[simp] theorem postStateUnder_true (w : AutoreflexiveQueryArchitecture.World ArchS) :
    AutoreflexiveQueryArchitecture.postStateUnder ArchS w true = (targetA w.1, obsB w.2.1) := by
  rfl

omit [HistoryGraph P] in
@[simp] theorem postStateUnder_false (w : AutoreflexiveQueryArchitecture.World ArchS) :
    AutoreflexiveQueryArchitecture.postStateUnder ArchS w false = (targetA w.1, defaultB) := by
  rfl

omit [HistoryGraph P] in
@[simp] theorem runUnder_true (w : AutoreflexiveQueryArchitecture.World ArchS) :
    AutoreflexiveQueryArchitecture.runUnder ArchS w true = out (decAB (targetA w.1, obsB w.2.1)) := by
  rfl

omit [HistoryGraph P] in
@[simp] theorem runUnder_false (w : AutoreflexiveQueryArchitecture.World ArchS) :
    AutoreflexiveQueryArchitecture.runUnder ArchS w false = out (decAB (targetA w.1, defaultB)) := by
  rfl

omit [HistoryGraph P] in
@[simp] theorem run_eq_if (w : AutoreflexiveQueryArchitecture.World ArchS) :
    AutoreflexiveQueryArchitecture.run ArchS w =
      out (decAB (targetA w.1, if policy (targetA w.1) then obsB w.2.1 else defaultB)) := by
  rfl

omit [HistoryGraph P] in
theorem run_eq_on_policy_true
    {h : P} (x : FiberPt (P := P) obsA targetA h)
    (hPolTrue : policy (targetA h) = true) :
    AutoreflexiveQueryArchitecture.run ArchS ⟨h, x⟩ = out (decAB (targetA h, obsB x.1)) := by
  dsimp [AutoreflexiveQueryArchitecture.run, AutoreflexiveQueryArchitecture.postState,
    AutoreflexiveQueryArchitecture.returnedResponse, AutoreflexiveQueryArchitecture.chosenAction,
    AutoreflexiveQueryArchitecture.preState, queryRepairFamilyBySecondMargin]
  rw [hPolTrue]
  rfl

theorem existsAlternativeActionDecisionEffect_of_goodFiber
    {h : P}
    (hPolTrue : policy (targetA h) = true)
    (hSep : StepSeparatesFiber (P := P) sem obsA targetA (stepAt h).2)
    (hCorr :
      QueryRepairBySecondMargin.CorrectOnLeftFiber (P := P)
        (S := S) (VA := VA) (VB := VB)
        sem obsA obsB targetA h (stepAt h).2 decAB) :
    AutoreflexiveQueryArchitecture.ExistsAlternativeActionDecisionEffect ArchS := by
  rcases hSep with ⟨x, x', _hne, hComp, hNotComp⟩
  have hxRunTrue : AutoreflexiveQueryArchitecture.run ArchS ⟨h, x⟩ = out true := by
    have hDec : decAB (targetA h, obsB x.1) = true := (hCorr x).2 hComp
    have hRun : AutoreflexiveQueryArchitecture.run ArchS ⟨h, x⟩ =
        out (decAB (targetA h, obsB x.1)) :=
      run_eq_on_policy_true
        (P := P) (obsA := obsA) (obsB := obsB) (targetA := targetA)
        (defaultB := defaultB) (policy := policy) (decAB := decAB)
        (h := h) x hPolTrue
    have : out (decAB (targetA h, obsB x.1)) = out true :=
      congrArg out hDec
    exact hRun.trans this
  have hx'RunFalse : AutoreflexiveQueryArchitecture.run ArchS ⟨h, x'⟩ = out false := by
    cases hb : decAB (targetA h, obsB x'.1) with
    | false =>
        have hRun : AutoreflexiveQueryArchitecture.run ArchS ⟨h, x'⟩ =
            out (decAB (targetA h, obsB x'.1)) :=
          run_eq_on_policy_true
            (P := P) (obsA := obsA) (obsB := obsB) (targetA := targetA)
            (defaultB := defaultB) (policy := policy) (decAB := decAB)
            (h := h) x' hPolTrue
        have : out (decAB (targetA h, obsB x'.1)) = out false :=
          congrArg out hb
        exact hRun.trans this
    | true =>
        have hx'Comp : Compatible (P := P) sem obsA targetA (stepAt h).2 x' := (hCorr x').1 hb
        exact False.elim (hNotComp hx'Comp)
  cases hc : decAB (targetA h, defaultB) with
  | false =>
      refine ⟨⟨h, x⟩, false, ?_, ?_⟩
      · intro hEq
        have hChosen : AutoreflexiveQueryArchitecture.chosenAction ArchS ⟨h, x⟩ = true := by
          change policy (targetA h) = true
          exact hPolTrue
        have : (false : Bool) = true := hEq.trans hChosen
        cases this
      · intro hEq
        have hUnder : AutoreflexiveQueryArchitecture.runUnder ArchS ⟨h, x⟩ false = out false := by
          have hUnder0 : AutoreflexiveQueryArchitecture.runUnder ArchS ⟨h, x⟩ false =
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
      refine ⟨⟨h, x'⟩, false, ?_, ?_⟩
      · intro hEq
        have hChosen : AutoreflexiveQueryArchitecture.chosenAction ArchS ⟨h, x'⟩ = true := by
          change policy (targetA h) = true
          exact hPolTrue
        have : (false : Bool) = true := hEq.trans hChosen
        cases this
      · intro hEq
        have hUnder : AutoreflexiveQueryArchitecture.runUnder ArchS ⟨h, x'⟩ false = out true := by
          have hUnder0 : AutoreflexiveQueryArchitecture.runUnder ArchS ⟨h, x'⟩ false =
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

theorem not_decisionFactorsThroughPreStateChosen_of_goodFiber
    {h : P}
    (hPolTrue : policy (targetA h) = true)
    (hSep : StepSeparatesFiber (P := P) sem obsA targetA (stepAt h).2)
    (hCorr :
      QueryRepairBySecondMargin.CorrectOnLeftFiber (P := P)
        (S := S) (VA := VA) (VB := VB)
        sem obsA obsB targetA h (stepAt h).2 decAB) :
    ¬ AutoreflexiveQueryArchitecture.DecisionFactorsThroughPreStateChosen ArchS := by
  intro hCollapse
  rcases hSep with ⟨x, x', _hne, hComp, hNotComp⟩
  have hxTrue : AutoreflexiveQueryArchitecture.run ArchS ⟨h, x⟩ = out true := by
    have hDec : decAB (targetA h, obsB x.1) = true := (hCorr x).2 hComp
    have hRun : AutoreflexiveQueryArchitecture.run ArchS ⟨h, x⟩ =
        out (decAB (targetA h, obsB x.1)) :=
      run_eq_on_policy_true
        (P := P) (obsA := obsA) (obsB := obsB) (targetA := targetA)
        (defaultB := defaultB) (policy := policy) (decAB := decAB)
        (h := h) x hPolTrue
    have : out (decAB (targetA h, obsB x.1)) = out true :=
      congrArg out hDec
    exact hRun.trans this
  have hx'False : AutoreflexiveQueryArchitecture.run ArchS ⟨h, x'⟩ = out false := by
    cases hb : decAB (targetA h, obsB x'.1) with
    | false =>
        have hRun : AutoreflexiveQueryArchitecture.run ArchS ⟨h, x'⟩ =
            out (decAB (targetA h, obsB x'.1)) :=
          run_eq_on_policy_true
            (P := P) (obsA := obsA) (obsB := obsB) (targetA := targetA)
            (defaultB := defaultB) (policy := policy) (decAB := decAB)
            (h := h) x' hPolTrue
        have : out (decAB (targetA h, obsB x'.1)) = out false :=
          congrArg out hb
        exact hRun.trans this
    | true =>
        have hx'Comp : Compatible (P := P) sem obsA targetA (stepAt h).2 x' := (hCorr x').1 hb
        exact False.elim (hNotComp hx'Comp)
  rcases hCollapse with ⟨decidePre, hCollapse⟩
  have hRunEq :
      AutoreflexiveQueryArchitecture.run ArchS ⟨h, x⟩ =
        AutoreflexiveQueryArchitecture.run ArchS ⟨h, x'⟩ := by
    calc
      AutoreflexiveQueryArchitecture.run ArchS ⟨h, x⟩ =
          decidePre (AutoreflexiveQueryArchitecture.preState ArchS ⟨h, x⟩) := hCollapse ⟨h, x⟩
      _ = decidePre (AutoreflexiveQueryArchitecture.preState ArchS ⟨h, x'⟩) := by
        rfl
      _ = AutoreflexiveQueryArchitecture.run ArchS ⟨h, x'⟩ := (hCollapse ⟨h, x'⟩).symm
  have : true = false := by
    have hEqOut : out true = out false := hxTrue.symm.trans (hRunEq.trans hx'False)
    exact congrArg ULift.down hEqOut
  cases this

theorem exists_runUnder_true_ne_false_of_goodFiber
    {h : P}
    (hSep : StepSeparatesFiber (P := P) sem obsA targetA (stepAt h).2)
    (hCorr :
      QueryRepairBySecondMargin.CorrectOnLeftFiber (P := P)
        (S := S) (VA := VA) (VB := VB)
        sem obsA obsB targetA h (stepAt h).2 decAB) :
    ∃ x : FiberPt (P := P) obsA targetA h,
      AutoreflexiveQueryArchitecture.runUnder ArchS ⟨h, x⟩ true ≠
        AutoreflexiveQueryArchitecture.runUnder ArchS ⟨h, x⟩ false := by
  rcases hSep with ⟨x, x', _hne, hComp, hNotComp⟩
  have hxUnderTrue : AutoreflexiveQueryArchitecture.runUnder ArchS ⟨h, x⟩ true = out true := by
    have hDec : decAB (targetA h, obsB x.1) = true := (hCorr x).2 hComp
    have hUnder : AutoreflexiveQueryArchitecture.runUnder ArchS ⟨h, x⟩ true =
        out (decAB (targetA h, obsB x.1)) := by
      rfl
    have : out (decAB (targetA h, obsB x.1)) = out true := congrArg out hDec
    exact hUnder.trans this
  have hx'UnderTrue : AutoreflexiveQueryArchitecture.runUnder ArchS ⟨h, x'⟩ true = out false := by
    cases hb : decAB (targetA h, obsB x'.1) with
    | false =>
        have hUnder : AutoreflexiveQueryArchitecture.runUnder ArchS ⟨h, x'⟩ true =
            out (decAB (targetA h, obsB x'.1)) := by
          rfl
        have : out (decAB (targetA h, obsB x'.1)) = out false := congrArg out hb
        exact hUnder.trans this
    | true =>
        have hx'Comp : Compatible (P := P) sem obsA targetA (stepAt h).2 x' := (hCorr x').1 hb
        exact False.elim (hNotComp hx'Comp)
  cases hc : decAB (targetA h, defaultB) with
  | false =>
      refine ⟨x, ?_⟩
      intro hEq
      have hUnderFalse : AutoreflexiveQueryArchitecture.runUnder ArchS ⟨h, x⟩ false = out false := by
        have hUnder : AutoreflexiveQueryArchitecture.runUnder ArchS ⟨h, x⟩ false =
            out (decAB (targetA h, defaultB)) := by
          rfl
        have : out (decAB (targetA h, defaultB)) = out false := congrArg out hc
        exact hUnder.trans this
      have : true = false := by
        have hEqOut : out true = out false :=
          hxUnderTrue.symm.trans (hEq.trans hUnderFalse)
        exact congrArg ULift.down hEqOut
      cases this
  | true =>
      refine ⟨x', ?_⟩
      intro hEq
      have hUnderFalse : AutoreflexiveQueryArchitecture.runUnder ArchS ⟨h, x'⟩ false = out true := by
        have hUnder : AutoreflexiveQueryArchitecture.runUnder ArchS ⟨h, x'⟩ false =
            out (decAB (targetA h, defaultB)) := by
          rfl
        have : out (decAB (targetA h, defaultB)) = out true := congrArg out hc
        exact hUnder.trans this
      have : true = false := by
        have hEqOut : out true = out false :=
          hUnderFalse.symm.trans (hEq.symm.trans hx'UnderTrue)
        exact congrArg ULift.down hEqOut
      cases this

theorem not_decisionRecoverableFromForbiddenChannel_of_goodFiber
    {h : P}
    (hPolTrue : policy (targetA h) = true)
    (hSep : StepSeparatesFiber (P := P) sem obsA targetA (stepAt h).2)
    (hCorr :
      QueryRepairBySecondMargin.CorrectOnLeftFiber (P := P)
        (S := S) (VA := VA) (VB := VB)
        sem obsA obsB targetA h (stepAt h).2 decAB) :
    ¬ AutoreflexiveQueryArchitecture.DecisionRecoverableFromForbiddenChannel ArchS := by
  intro hBypass
  rcases hSep with ⟨x, x', _hne, hComp, hNotComp⟩
  rcases hBypass with ⟨decideBypass, hBypass⟩
  have hxTrue : AutoreflexiveQueryArchitecture.run ArchS ⟨h, x⟩ = out true := by
    have hDec : decAB (targetA h, obsB x.1) = true := (hCorr x).2 hComp
    have hRun : AutoreflexiveQueryArchitecture.run ArchS ⟨h, x⟩ =
        out (decAB (targetA h, obsB x.1)) :=
      run_eq_on_policy_true
        (P := P) (obsA := obsA) (obsB := obsB) (targetA := targetA)
        (defaultB := defaultB) (policy := policy) (decAB := decAB)
        (h := h) x hPolTrue
    have : out (decAB (targetA h, obsB x.1)) = out true :=
      congrArg out hDec
    exact hRun.trans this
  have hx'False : AutoreflexiveQueryArchitecture.run ArchS ⟨h, x'⟩ = out false := by
    cases hb : decAB (targetA h, obsB x'.1) with
    | false =>
        have hRun : AutoreflexiveQueryArchitecture.run ArchS ⟨h, x'⟩ =
            out (decAB (targetA h, obsB x'.1)) :=
          run_eq_on_policy_true
            (P := P) (obsA := obsA) (obsB := obsB) (targetA := targetA)
            (defaultB := defaultB) (policy := policy) (decAB := decAB)
            (h := h) x' hPolTrue
        have : out (decAB (targetA h, obsB x'.1)) = out false :=
          congrArg out hb
        exact hRun.trans this
    | true =>
        have hx'Comp : Compatible (P := P) sem obsA targetA (stepAt h).2 x' := (hCorr x').1 hb
        exact False.elim (hNotComp hx'Comp)
  have hEq :
      AutoreflexiveQueryArchitecture.run ArchS ⟨h, x⟩ =
        AutoreflexiveQueryArchitecture.run ArchS ⟨h, x'⟩ := by
    calc
      AutoreflexiveQueryArchitecture.run ArchS ⟨h, x⟩ =
          decideBypass (AutoreflexiveQueryArchitecture.bypassVisible ArchS ⟨h, x⟩) := hBypass ⟨h, x⟩
      _ = decideBypass (AutoreflexiveQueryArchitecture.bypassVisible ArchS ⟨h, x'⟩) := by
        rfl
      _ = AutoreflexiveQueryArchitecture.run ArchS ⟨h, x'⟩ := (hBypass ⟨h, x'⟩).symm
  have : true = false := by
    have hEqOut : out true = out false := hxTrue.symm.trans (hEq.trans hx'False)
    exact congrArg ULift.down hEqOut
  cases this

theorem queryLoopOperationality_of_strongBridgeHypotheses
    (hHyp : StrongBridgeHypotheses (P := P) (S := S) (VA := VA) (VB := VB)
      (sem := sem) (obsA := obsA) (obsB := obsB) (targetA := targetA) (stepAt := stepAt)
      (defaultB := defaultB) (policy := policy) (decAB := decAB)) :
    AutoreflexiveQueryArchitecture.QueryLoopOperationality ArchS := by
  rcases hHyp.exists_good with ⟨hGood, hGood⟩
  rcases hGood with ⟨hPolTrue, hSep, hCorr⟩
  have hSep' := hSep
  rcases hSep' with ⟨x, _x', _hne, _hxComp, _hxNotComp⟩
  let wTrue : AutoreflexiveQueryArchitecture.World ArchS := ⟨hGood, x⟩
  rcases hHyp.exists_false_world with ⟨hFalse, hPolFalse, hNonempty⟩
  rcases hNonempty with ⟨xFalse⟩
  let wFalse : AutoreflexiveQueryArchitecture.World ArchS := ⟨hFalse, xFalse⟩
  have hChosenTrue : AutoreflexiveQueryArchitecture.chosenAction ArchS wTrue = true := by
    dsimp [AutoreflexiveQueryArchitecture.chosenAction, AutoreflexiveQueryArchitecture.preState,
      queryRepairFamilyBySecondMargin, wTrue]
    exact hPolTrue
  have hChosenFalse : AutoreflexiveQueryArchitecture.chosenAction ArchS wFalse = false := by
    dsimp [AutoreflexiveQueryArchitecture.chosenAction, AutoreflexiveQueryArchitecture.preState,
      queryRepairFamilyBySecondMargin, wFalse]
    exact hPolFalse
  have hChosenNe : AutoreflexiveQueryArchitecture.chosenAction ArchS wTrue ≠
      AutoreflexiveQueryArchitecture.chosenAction ArchS wFalse := by
    intro hEq
    have : (true : Bool) = false := by
      exact hChosenTrue.symm.trans (hEq.trans hChosenFalse)
    cases this

  rcases hHyp.exists_response_gap with ⟨wGap, hGap⟩

  have hRunTF :
      ∃ x0 : FiberPt (P := P) obsA targetA hGood,
        AutoreflexiveQueryArchitecture.runUnder ArchS ⟨hGood, x0⟩ true ≠
          AutoreflexiveQueryArchitecture.runUnder ArchS ⟨hGood, x0⟩ false :=
    exists_runUnder_true_ne_false_of_goodFiber
      (P := P) (S := S) (VA := VA) (VB := VB)
      (sem := sem) (obsA := obsA) (obsB := obsB) (targetA := targetA) (stepAt := stepAt)
      (defaultB := defaultB) (policy := policy) (decAB := decAB)
      (h := hGood) hSep hCorr

  rcases hRunTF with ⟨x0, hRunUnderNe⟩
  let w0 : AutoreflexiveQueryArchitecture.World ArchS := ⟨hGood, x0⟩

  have hRunUnderNe0 : AutoreflexiveQueryArchitecture.runUnder ArchS w0 true ≠
      AutoreflexiveQueryArchitecture.runUnder ArchS w0 false := by
    intro hEq
    dsimp [w0] at hEq
    exact hRunUnderNe hEq

  have hRunUnderNe' :
      AutoreflexiveQueryArchitecture.runUnder ArchS w0 (AutoreflexiveQueryArchitecture.chosenAction ArchS wTrue) ≠
        AutoreflexiveQueryArchitecture.runUnder ArchS w0 (AutoreflexiveQueryArchitecture.chosenAction ArchS wFalse) := by
    intro hEq
    have hEq' := hEq
    rw [hChosenTrue] at hEq'
    rw [hChosenFalse] at hEq'
    exact hRunUnderNe0 hEq'

  have hAltEffect : AutoreflexiveQueryArchitecture.ExistsAlternativeActionDecisionEffect ArchS := by
    refine ⟨w0, false, ?_, ?_⟩
    · intro hEq
      have hChosen0 : AutoreflexiveQueryArchitecture.chosenAction ArchS w0 = true := by
        dsimp [AutoreflexiveQueryArchitecture.chosenAction, AutoreflexiveQueryArchitecture.preState,
          queryRepairFamilyBySecondMargin, w0]
        exact hPolTrue
      have : (false : Bool) = true := hEq.trans hChosen0
      cases this
    · -- runUnder false differs from run (run uses chosenAction = true on this fiber)
      intro hEq
      have hChosen0 : AutoreflexiveQueryArchitecture.chosenAction ArchS w0 = true := by
        dsimp [AutoreflexiveQueryArchitecture.chosenAction, AutoreflexiveQueryArchitecture.preState,
          queryRepairFamilyBySecondMargin, w0]
        exact hPolTrue
      have hRunEq : AutoreflexiveQueryArchitecture.runUnder ArchS w0 true =
          AutoreflexiveQueryArchitecture.run ArchS w0 := by
        dsimp [AutoreflexiveQueryArchitecture.runUnder, AutoreflexiveQueryArchitecture.run,
          AutoreflexiveQueryArchitecture.postStateUnder, AutoreflexiveQueryArchitecture.postState,
          AutoreflexiveQueryArchitecture.returnedResponseUnder, AutoreflexiveQueryArchitecture.returnedResponse,
          AutoreflexiveQueryArchitecture.chosenAction, AutoreflexiveQueryArchitecture.preState,
          queryRepairFamilyBySecondMargin, w0]
        rw [hPolTrue]
        rfl
      have : AutoreflexiveQueryArchitecture.runUnder ArchS w0 true =
          AutoreflexiveQueryArchitecture.runUnder ArchS w0 false :=
        hRunEq.trans hEq.symm
      exact hRunUnderNe0 this

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hRec
    rcases hRec with ⟨queryBypass, hRec⟩
    have ht : AutoreflexiveQueryArchitecture.chosenAction ArchS wTrue = queryBypass PUnit.unit :=
      hRec wTrue
    have hf : AutoreflexiveQueryArchitecture.chosenAction ArchS wFalse = queryBypass PUnit.unit :=
      hRec wFalse
    have : AutoreflexiveQueryArchitecture.chosenAction ArchS wTrue =
        AutoreflexiveQueryArchitecture.chosenAction ArchS wFalse := ht.trans hf.symm
    exact hChosenNe this
  · refine ⟨wGap, wTrue, wFalse, hChosenNe, ?_⟩
    intro hEq
    have : obsB wGap.2.1 = defaultB := by
      have h1 : AutoreflexiveQueryArchitecture.env ArchS wGap (AutoreflexiveQueryArchitecture.chosenAction ArchS wTrue) =
          obsB wGap.2.1 := by
        rw [hChosenTrue]
        rfl
      have h2 : AutoreflexiveQueryArchitecture.env ArchS wGap (AutoreflexiveQueryArchitecture.chosenAction ArchS wFalse) =
          defaultB := by
        rw [hChosenFalse]
        rfl
      exact h1.symm.trans (hEq.trans h2)
    exact hGap this
  · refine ⟨wGap, wTrue, wFalse, hChosenNe, ?_⟩
    intro hEq
    have hSnd :
        (AutoreflexiveQueryArchitecture.postStateUnder ArchS wGap (AutoreflexiveQueryArchitecture.chosenAction ArchS wTrue)).2 =
          (AutoreflexiveQueryArchitecture.postStateUnder ArchS wGap (AutoreflexiveQueryArchitecture.chosenAction ArchS wFalse)).2 :=
      congrArg Prod.snd hEq
    have : obsB wGap.2.1 = defaultB := by
      have h1 :
          (AutoreflexiveQueryArchitecture.postStateUnder ArchS wGap (AutoreflexiveQueryArchitecture.chosenAction ArchS wTrue)).2 =
            obsB wGap.2.1 := by
        rw [hChosenTrue]
        rfl
      have h2 :
          (AutoreflexiveQueryArchitecture.postStateUnder ArchS wGap (AutoreflexiveQueryArchitecture.chosenAction ArchS wFalse)).2 =
            defaultB := by
        rw [hChosenFalse]
        rfl
      exact h1.symm.trans (hSnd.trans h2)
    exact hGap this
  · refine ⟨w0, wTrue, wFalse, hChosenNe, ?_⟩
    exact hRunUnderNe'
  · exact hAltEffect
  · intro hCollapse
    exact (not_decisionFactorsThroughPreStateChosen_of_goodFiber
      (P := P) (S := S) (VA := VA) (VB := VB)
      (sem := sem) (obsA := obsA) (obsB := obsB) (targetA := targetA) (stepAt := stepAt)
      (defaultB := defaultB) (policy := policy) (decAB := decAB)
      (h := hGood) hPolTrue hSep hCorr) hCollapse
  · intro hBypass
    exact (not_decisionRecoverableFromForbiddenChannel_of_goodFiber
      (P := P) (S := S) (VA := VA) (VB := VB)
      (sem := sem) (obsA := obsA) (obsB := obsB) (targetA := targetA) (stepAt := stepAt)
      (defaultB := defaultB) (policy := policy) (decAB := decAB)
      (h := hGood) hPolTrue hSep hCorr) hBypass

end QueryRepairFamilyBySecondMargin

end StrongBridge

/-!
## Strong bridge with a nontrivial forbidden channel

This section generalizes the strong bridge by allowing `BypassVisible := B` for an arbitrary type `B`,
with an explicit `bypassVisible : StrongWorld → B`.

Since bypass recoverability is an information-level notion, we add explicit hypotheses guaranteeing
non-recoverability (rather than relying on the architecture alone).
-/

section StrongBridgeBypass

variable {S VA VB : Type w}
variable (sem : Semantics P S)
variable (obsA : S → VA) (obsB : S → VB)
variable (targetA : P → VA)
variable (stepAt : ∀ h : P, Σ k : P, HistoryGraph.Path h k)

variable (defaultB : VB)
variable (policy : VA → Bool)
variable (decAB : VA × VB → Bool)

variable {B : Type w}
variable (bypassVisible : (StrongWorld (P := P) obsA targetA) → B)

def queryRepairFamilyBySecondMarginWithBypass :
    AutoreflexiveQueryArchitecture where
  World := StrongWorld (P := P) obsA targetA
  HistoryVisible := VA
  BypassVisible := B
  State := VA × VB
  Action := Bool
  Response := VB
  Output := BridgeOut
  historyVisible := fun w => targetA w.1
  bypassVisible := bypassVisible
  encode := fun vA => (vA, defaultB)
  query := fun s => policy s.1
  env := fun w action =>
    if action then obsB w.2.1 else defaultB
  update := fun state response => (state.1, response)
  decide := fun s => out (decAB s)

namespace QueryRepairFamilyBySecondMarginWithBypass

local notation "ArchB" =>
  queryRepairFamilyBySecondMarginWithBypass
    (P := P) (obsA := obsA) (obsB := obsB) (targetA := targetA)
    (defaultB := defaultB) (policy := policy) (decAB := decAB) (B := B) bypassVisible

def GoodFiber (h : P) : Prop :=
  policy (targetA h) = true
    ∧ StepSeparatesFiber (P := P) sem obsA targetA (stepAt h).2
    ∧ QueryRepairBySecondMargin.CorrectOnLeftFiber (P := P)
        (S := S) (VA := VA) (VB := VB)
        sem obsA obsB targetA h (stepAt h).2 decAB

structure StrongBridgeHypotheses : Prop where
  exists_good :
    ∃ h : P, GoodFiber (P := P) (sem := sem) (obsA := obsA) (obsB := obsB)
      (targetA := targetA) (stepAt := stepAt) (policy := policy) (decAB := decAB) h
  exists_false_world :
    ∃ h : P, policy (targetA h) = false ∧ Nonempty (FiberPt (P := P) obsA targetA h)
  exists_response_gap :
    ∃ w : StrongWorld (P := P) obsA targetA, obsB w.2.1 ≠ defaultB
  action_collision_sameBypass :
    ∃ w₁ w₂ : AutoreflexiveQueryArchitecture.World ArchB,
      AutoreflexiveQueryArchitecture.bypassVisible ArchB w₁ =
          AutoreflexiveQueryArchitecture.bypassVisible ArchB w₂
        ∧ AutoreflexiveQueryArchitecture.chosenAction ArchB w₁ ≠
          AutoreflexiveQueryArchitecture.chosenAction ArchB w₂
  bypassFactorsThroughHistory :
    ∃ g : VA → B, ∀ w : AutoreflexiveQueryArchitecture.World ArchB,
      AutoreflexiveQueryArchitecture.bypassVisible ArchB w = g (targetA w.1)

theorem not_decisionRecoverableFromForbiddenChannel_of_goodFiber
    {h : P}
    (hPolTrue : policy (targetA h) = true)
    (hSep : StepSeparatesFiber (P := P) sem obsA targetA (stepAt h).2)
    (hCorr :
      QueryRepairBySecondMargin.CorrectOnLeftFiber (P := P)
        (S := S) (VA := VA) (VB := VB)
        sem obsA obsB targetA h (stepAt h).2 decAB)
    (g : VA → B)
    (hg : ∀ w : AutoreflexiveQueryArchitecture.World ArchB,
      AutoreflexiveQueryArchitecture.bypassVisible ArchB w = g (targetA w.1)) :
    ¬ AutoreflexiveQueryArchitecture.DecisionRecoverableFromForbiddenChannel ArchB := by
  intro hBypass
  rcases hBypass with ⟨decideBypass, hBypass⟩
  rcases hSep with ⟨x, x', _hne, hComp, hNotComp⟩
  have hxTrue : AutoreflexiveQueryArchitecture.run ArchB ⟨h, x⟩ = out true := by
    have hDec : decAB (targetA h, obsB x.1) = true := (hCorr x).2 hComp
    have hRun : AutoreflexiveQueryArchitecture.run ArchB ⟨h, x⟩ =
        out (decAB (targetA h, obsB x.1)) := by
      dsimp [AutoreflexiveQueryArchitecture.run, AutoreflexiveQueryArchitecture.postState,
        AutoreflexiveQueryArchitecture.returnedResponse, AutoreflexiveQueryArchitecture.chosenAction,
        AutoreflexiveQueryArchitecture.preState, queryRepairFamilyBySecondMarginWithBypass]
      rw [hPolTrue]
      rfl
    have : out (decAB (targetA h, obsB x.1)) = out true :=
      congrArg out hDec
    exact hRun.trans this
  have hx'False : AutoreflexiveQueryArchitecture.run ArchB ⟨h, x'⟩ = out false := by
    cases hb : decAB (targetA h, obsB x'.1) with
    | false =>
        have hRun : AutoreflexiveQueryArchitecture.run ArchB ⟨h, x'⟩ =
            out (decAB (targetA h, obsB x'.1)) := by
          dsimp [AutoreflexiveQueryArchitecture.run, AutoreflexiveQueryArchitecture.postState,
            AutoreflexiveQueryArchitecture.returnedResponse, AutoreflexiveQueryArchitecture.chosenAction,
            AutoreflexiveQueryArchitecture.preState, queryRepairFamilyBySecondMarginWithBypass]
          rw [hPolTrue]
          rfl
        have : out (decAB (targetA h, obsB x'.1)) = out false :=
          congrArg out hb
        exact hRun.trans this
    | true =>
        have hx'Comp : Compatible (P := P) sem obsA targetA (stepAt h).2 x' := (hCorr x').1 hb
        exact False.elim (hNotComp hx'Comp)
  have hBypassEq :
      AutoreflexiveQueryArchitecture.bypassVisible ArchB ⟨h, x⟩ =
        AutoreflexiveQueryArchitecture.bypassVisible ArchB ⟨h, x'⟩ := by
    have hx : AutoreflexiveQueryArchitecture.bypassVisible ArchB ⟨h, x⟩ = g (targetA h) :=
      hg ⟨h, x⟩
    have hx' : AutoreflexiveQueryArchitecture.bypassVisible ArchB ⟨h, x'⟩ = g (targetA h) :=
      hg ⟨h, x'⟩
    exact hx.trans hx'.symm
  have hRunEq :
      AutoreflexiveQueryArchitecture.run ArchB ⟨h, x⟩ =
        AutoreflexiveQueryArchitecture.run ArchB ⟨h, x'⟩ := by
    calc
      AutoreflexiveQueryArchitecture.run ArchB ⟨h, x⟩ =
          decideBypass (AutoreflexiveQueryArchitecture.bypassVisible ArchB ⟨h, x⟩) := hBypass ⟨h, x⟩
      _ = decideBypass (AutoreflexiveQueryArchitecture.bypassVisible ArchB ⟨h, x'⟩) := by
          exact congrArg decideBypass hBypassEq
      _ = AutoreflexiveQueryArchitecture.run ArchB ⟨h, x'⟩ := (hBypass ⟨h, x'⟩).symm
  have : true = false := by
    have hEqOut : out true = out false :=
      hxTrue.symm.trans (hRunEq.trans hx'False)
    exact congrArg ULift.down hEqOut
  cases this

theorem exists_runUnder_true_ne_false_of_goodFiber
    {h : P}
    (hSep : StepSeparatesFiber (P := P) sem obsA targetA (stepAt h).2)
    (hCorr :
      QueryRepairBySecondMargin.CorrectOnLeftFiber (P := P)
        (S := S) (VA := VA) (VB := VB)
        sem obsA obsB targetA h (stepAt h).2 decAB) :
    ∃ x0 : FiberPt (P := P) obsA targetA h,
      AutoreflexiveQueryArchitecture.runUnder ArchB ⟨h, x0⟩ true ≠
        AutoreflexiveQueryArchitecture.runUnder ArchB ⟨h, x0⟩ false := by
  rcases hSep with ⟨x, x', _hne, hComp, hNotComp⟩
  have hxUnderTrue : AutoreflexiveQueryArchitecture.runUnder ArchB ⟨h, x⟩ true = out true := by
    have hDec : decAB (targetA h, obsB x.1) = true := (hCorr x).2 hComp
    have hUnder : AutoreflexiveQueryArchitecture.runUnder ArchB ⟨h, x⟩ true =
        out (decAB (targetA h, obsB x.1)) := by
      rfl
    have : out (decAB (targetA h, obsB x.1)) = out true := congrArg out hDec
    exact hUnder.trans this
  have hx'UnderTrue : AutoreflexiveQueryArchitecture.runUnder ArchB ⟨h, x'⟩ true = out false := by
    cases hb : decAB (targetA h, obsB x'.1) with
    | false =>
        have hUnder : AutoreflexiveQueryArchitecture.runUnder ArchB ⟨h, x'⟩ true =
            out (decAB (targetA h, obsB x'.1)) := by
          rfl
        have : out (decAB (targetA h, obsB x'.1)) = out false := congrArg out hb
        exact hUnder.trans this
    | true =>
        have hx'Comp : Compatible (P := P) sem obsA targetA (stepAt h).2 x' := (hCorr x').1 hb
        exact False.elim (hNotComp hx'Comp)
  cases hc : decAB (targetA h, defaultB) with
  | false =>
      refine ⟨x, ?_⟩
      intro hEq
      have hUnderFalse : AutoreflexiveQueryArchitecture.runUnder ArchB ⟨h, x⟩ false = out false := by
        have hUnder : AutoreflexiveQueryArchitecture.runUnder ArchB ⟨h, x⟩ false =
            out (decAB (targetA h, defaultB)) := by
          rfl
        have : out (decAB (targetA h, defaultB)) = out false := congrArg out hc
        exact hUnder.trans this
      have : true = false := by
        have hEqOut : out true = out false :=
          hxUnderTrue.symm.trans (hEq.trans hUnderFalse)
        exact congrArg ULift.down hEqOut
      cases this
  | true =>
      refine ⟨x', ?_⟩
      intro hEq
      have hUnderFalse : AutoreflexiveQueryArchitecture.runUnder ArchB ⟨h, x'⟩ false = out true := by
        have hUnder : AutoreflexiveQueryArchitecture.runUnder ArchB ⟨h, x'⟩ false =
            out (decAB (targetA h, defaultB)) := by
          rfl
        have : out (decAB (targetA h, defaultB)) = out true := congrArg out hc
        exact hUnder.trans this
      have : true = false := by
        have hEqOut : out true = out false :=
          hUnderFalse.symm.trans (hEq.symm.trans hx'UnderTrue)
        exact congrArg ULift.down hEqOut
      cases this

theorem not_decisionFactorsThroughPreStateChosen_of_goodFiber
    {h : P}
    (hPolTrue : policy (targetA h) = true)
    (hSep : StepSeparatesFiber (P := P) sem obsA targetA (stepAt h).2)
    (hCorr :
      QueryRepairBySecondMargin.CorrectOnLeftFiber (P := P)
        (S := S) (VA := VA) (VB := VB)
        sem obsA obsB targetA h (stepAt h).2 decAB) :
    ¬ AutoreflexiveQueryArchitecture.DecisionFactorsThroughPreStateChosen ArchB := by
  intro hCollapse
  rcases hSep with ⟨x, x', _hne, hComp, hNotComp⟩
  have hxTrue : AutoreflexiveQueryArchitecture.run ArchB ⟨h, x⟩ = out true := by
    have hDec : decAB (targetA h, obsB x.1) = true := (hCorr x).2 hComp
    have hRun : AutoreflexiveQueryArchitecture.run ArchB ⟨h, x⟩ =
        out (decAB (targetA h, obsB x.1)) := by
      dsimp [AutoreflexiveQueryArchitecture.run, AutoreflexiveQueryArchitecture.postState,
        AutoreflexiveQueryArchitecture.returnedResponse, AutoreflexiveQueryArchitecture.chosenAction,
        AutoreflexiveQueryArchitecture.preState, queryRepairFamilyBySecondMarginWithBypass]
      rw [hPolTrue]
      rfl
    have : out (decAB (targetA h, obsB x.1)) = out true := congrArg out hDec
    exact hRun.trans this
  have hx'False : AutoreflexiveQueryArchitecture.run ArchB ⟨h, x'⟩ = out false := by
    cases hb : decAB (targetA h, obsB x'.1) with
    | false =>
        have hRun : AutoreflexiveQueryArchitecture.run ArchB ⟨h, x'⟩ =
            out (decAB (targetA h, obsB x'.1)) := by
          dsimp [AutoreflexiveQueryArchitecture.run, AutoreflexiveQueryArchitecture.postState,
            AutoreflexiveQueryArchitecture.returnedResponse, AutoreflexiveQueryArchitecture.chosenAction,
            AutoreflexiveQueryArchitecture.preState, queryRepairFamilyBySecondMarginWithBypass]
          rw [hPolTrue]
          rfl
        have : out (decAB (targetA h, obsB x'.1)) = out false := congrArg out hb
        exact hRun.trans this
    | true =>
        have hx'Comp : Compatible (P := P) sem obsA targetA (stepAt h).2 x' := (hCorr x').1 hb
        exact False.elim (hNotComp hx'Comp)
  rcases hCollapse with ⟨decidePre, hCollapse⟩
  have hRunEq :
      AutoreflexiveQueryArchitecture.run ArchB ⟨h, x⟩ =
        AutoreflexiveQueryArchitecture.run ArchB ⟨h, x'⟩ := by
    calc
      AutoreflexiveQueryArchitecture.run ArchB ⟨h, x⟩ =
          decidePre (AutoreflexiveQueryArchitecture.preState ArchB ⟨h, x⟩) := hCollapse ⟨h, x⟩
      _ = decidePre (AutoreflexiveQueryArchitecture.preState ArchB ⟨h, x'⟩) := by
          rfl
      _ = AutoreflexiveQueryArchitecture.run ArchB ⟨h, x'⟩ := (hCollapse ⟨h, x'⟩).symm
  have : true = false := by
    have hEqOut : out true = out false := hxTrue.symm.trans (hRunEq.trans hx'False)
    exact congrArg ULift.down hEqOut
  cases this

theorem queryLoopOperationality_of_strongBridgeHypotheses
    (hHyp : StrongBridgeHypotheses (P := P)
      (S := S) (VA := VA) (VB := VB)
      (sem := sem) (obsA := obsA) (obsB := obsB) (targetA := targetA) (stepAt := stepAt)
      (defaultB := defaultB) (policy := policy) (decAB := decAB)
      (B := B) (bypassVisible := bypassVisible)) :
    AutoreflexiveQueryArchitecture.QueryLoopOperationality ArchB := by
  rcases hHyp.exists_good with ⟨hGood, hGood⟩
  rcases hGood with ⟨hPolTrue, hSep, hCorr⟩
  have hSep' := hSep
  rcases hSep' with ⟨x, _x', _hne, _hxComp, _hxNotComp⟩
  let wTrue : AutoreflexiveQueryArchitecture.World ArchB := ⟨hGood, x⟩
  rcases hHyp.exists_false_world with ⟨hFalse, hPolFalse, hNonempty⟩
  rcases hNonempty with ⟨xFalse⟩
  let wFalse : AutoreflexiveQueryArchitecture.World ArchB := ⟨hFalse, xFalse⟩
  have hChosenTrue : AutoreflexiveQueryArchitecture.chosenAction ArchB wTrue = true := by
    dsimp [AutoreflexiveQueryArchitecture.chosenAction, AutoreflexiveQueryArchitecture.preState,
      queryRepairFamilyBySecondMarginWithBypass, wTrue]
    exact hPolTrue
  have hChosenFalse : AutoreflexiveQueryArchitecture.chosenAction ArchB wFalse = false := by
    dsimp [AutoreflexiveQueryArchitecture.chosenAction, AutoreflexiveQueryArchitecture.preState,
      queryRepairFamilyBySecondMarginWithBypass, wFalse]
    exact hPolFalse
  have hChosenNe : AutoreflexiveQueryArchitecture.chosenAction ArchB wTrue ≠
      AutoreflexiveQueryArchitecture.chosenAction ArchB wFalse := by
    intro hEq
    have : (true : Bool) = false := hChosenTrue.symm.trans (hEq.trans hChosenFalse)
    cases this

  rcases hHyp.exists_response_gap with ⟨wGap, hGap⟩

  have hRunTF :
      ∃ x0 : FiberPt (P := P) obsA targetA hGood,
        AutoreflexiveQueryArchitecture.runUnder ArchB ⟨hGood, x0⟩ true ≠
          AutoreflexiveQueryArchitecture.runUnder ArchB ⟨hGood, x0⟩ false :=
    exists_runUnder_true_ne_false_of_goodFiber
      (P := P) (S := S) (VA := VA) (VB := VB)
      (sem := sem) (obsA := obsA) (obsB := obsB) (targetA := targetA) (stepAt := stepAt)
      (defaultB := defaultB) (policy := policy) (decAB := decAB)
      (B := B) (bypassVisible := bypassVisible)
      (h := hGood) hSep hCorr
  rcases hRunTF with ⟨x0, hRunUnderNe⟩
  let w0 : AutoreflexiveQueryArchitecture.World ArchB := ⟨hGood, x0⟩
  have hRunUnderNe0 :
      AutoreflexiveQueryArchitecture.runUnder ArchB w0 true ≠
        AutoreflexiveQueryArchitecture.runUnder ArchB w0 false := by
    intro hEq
    dsimp [w0] at hEq
    exact hRunUnderNe hEq
  have hRunUnderNe' :
      AutoreflexiveQueryArchitecture.runUnder ArchB w0 (AutoreflexiveQueryArchitecture.chosenAction ArchB wTrue) ≠
        AutoreflexiveQueryArchitecture.runUnder ArchB w0 (AutoreflexiveQueryArchitecture.chosenAction ArchB wFalse) := by
    intro hEq
    have hEq' := hEq
    rw [hChosenTrue] at hEq'
    rw [hChosenFalse] at hEq'
    exact hRunUnderNe0 hEq'

  have hAltEffect : AutoreflexiveQueryArchitecture.ExistsAlternativeActionDecisionEffect ArchB := by
    refine ⟨w0, false, ?_, ?_⟩
    · intro hEq
      have hChosen0 : AutoreflexiveQueryArchitecture.chosenAction ArchB w0 = true := by
        dsimp [AutoreflexiveQueryArchitecture.chosenAction, AutoreflexiveQueryArchitecture.preState,
          queryRepairFamilyBySecondMarginWithBypass, w0]
        exact hPolTrue
      have : (false : Bool) = true := hEq.trans hChosen0
      cases this
    · intro hEq
      have hChosen0 : AutoreflexiveQueryArchitecture.chosenAction ArchB w0 = true := by
        dsimp [AutoreflexiveQueryArchitecture.chosenAction, AutoreflexiveQueryArchitecture.preState,
          queryRepairFamilyBySecondMarginWithBypass, w0]
        exact hPolTrue
      have hRunEq : AutoreflexiveQueryArchitecture.runUnder ArchB w0 true =
          AutoreflexiveQueryArchitecture.run ArchB w0 := by
        dsimp [AutoreflexiveQueryArchitecture.runUnder, AutoreflexiveQueryArchitecture.run,
          AutoreflexiveQueryArchitecture.postStateUnder, AutoreflexiveQueryArchitecture.postState,
          AutoreflexiveQueryArchitecture.returnedResponseUnder, AutoreflexiveQueryArchitecture.returnedResponse,
          AutoreflexiveQueryArchitecture.chosenAction, AutoreflexiveQueryArchitecture.preState,
          queryRepairFamilyBySecondMarginWithBypass, w0]
        rw [hPolTrue]
        rfl
      have : AutoreflexiveQueryArchitecture.runUnder ArchB w0 true =
          AutoreflexiveQueryArchitecture.runUnder ArchB w0 false :=
        hRunEq.trans hEq.symm
      exact hRunUnderNe0 this

  rcases hHyp.bypassFactorsThroughHistory with ⟨g, hg⟩

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hRec
    rcases hHyp.action_collision_sameBypass with ⟨w1, w2, hBypassEq, hActNe⟩
    rcases hRec with ⟨queryBypass, hRec⟩
    have h1 : AutoreflexiveQueryArchitecture.chosenAction ArchB w1 =
        queryBypass (AutoreflexiveQueryArchitecture.bypassVisible ArchB w1) := hRec w1
    have h2 : AutoreflexiveQueryArchitecture.chosenAction ArchB w2 =
        queryBypass (AutoreflexiveQueryArchitecture.bypassVisible ArchB w2) := hRec w2
    have hEq : AutoreflexiveQueryArchitecture.chosenAction ArchB w1 =
        AutoreflexiveQueryArchitecture.chosenAction ArchB w2 := by
      calc
        AutoreflexiveQueryArchitecture.chosenAction ArchB w1 =
            queryBypass (AutoreflexiveQueryArchitecture.bypassVisible ArchB w1) := h1
        _ = queryBypass (AutoreflexiveQueryArchitecture.bypassVisible ArchB w2) := by
            exact congrArg queryBypass hBypassEq
        _ = AutoreflexiveQueryArchitecture.chosenAction ArchB w2 := h2.symm
    exact hActNe hEq
  · refine ⟨wGap, wTrue, wFalse, hChosenNe, ?_⟩
    intro hEq
    have : obsB wGap.2.1 = defaultB := by
      have h1 : AutoreflexiveQueryArchitecture.env ArchB wGap (AutoreflexiveQueryArchitecture.chosenAction ArchB wTrue) =
          obsB wGap.2.1 := by
        rw [hChosenTrue]
        rfl
      have h2 : AutoreflexiveQueryArchitecture.env ArchB wGap (AutoreflexiveQueryArchitecture.chosenAction ArchB wFalse) =
          defaultB := by
        rw [hChosenFalse]
        rfl
      exact h1.symm.trans (hEq.trans h2)
    exact hGap this
  · refine ⟨wGap, wTrue, wFalse, hChosenNe, ?_⟩
    intro hEq
    have hSnd :
        (AutoreflexiveQueryArchitecture.postStateUnder ArchB wGap (AutoreflexiveQueryArchitecture.chosenAction ArchB wTrue)).2 =
          (AutoreflexiveQueryArchitecture.postStateUnder ArchB wGap (AutoreflexiveQueryArchitecture.chosenAction ArchB wFalse)).2 :=
      congrArg Prod.snd hEq
    have : obsB wGap.2.1 = defaultB := by
      have h1 :
          (AutoreflexiveQueryArchitecture.postStateUnder ArchB wGap (AutoreflexiveQueryArchitecture.chosenAction ArchB wTrue)).2 =
            obsB wGap.2.1 := by
        rw [hChosenTrue]
        rfl
      have h2 :
          (AutoreflexiveQueryArchitecture.postStateUnder ArchB wGap (AutoreflexiveQueryArchitecture.chosenAction ArchB wFalse)).2 =
            defaultB := by
        rw [hChosenFalse]
        rfl
      exact h1.symm.trans (hSnd.trans h2)
    exact hGap this
  · refine ⟨w0, wTrue, wFalse, hChosenNe, ?_⟩
    exact hRunUnderNe'
  · exact hAltEffect
  · intro hCollapse
    exact (not_decisionFactorsThroughPreStateChosen_of_goodFiber
      (P := P) (S := S) (VA := VA) (VB := VB)
      (sem := sem) (obsA := obsA) (obsB := obsB) (targetA := targetA) (stepAt := stepAt)
      (defaultB := defaultB) (policy := policy) (decAB := decAB)
      (B := B) (bypassVisible := bypassVisible)
      (h := hGood) hPolTrue hSep hCorr) hCollapse
  · exact not_decisionRecoverableFromForbiddenChannel_of_goodFiber
      (P := P) (S := S) (VA := VA) (VB := VB)
      (sem := sem) (obsA := obsA) (obsB := obsB) (targetA := targetA) (stepAt := stepAt)
      (defaultB := defaultB) (policy := policy) (decAB := decAB)
      (B := B) (bypassVisible := bypassVisible)
      (h := hGood) hPolTrue hSep hCorr g hg

end QueryRepairFamilyBySecondMarginWithBypass

end StrongBridgeBypass

end Examples
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.Examples.queryRepairFamilyBySecondMargin
#print axioms PrimitiveHolonomy.Examples.QueryRepairFamilyBySecondMargin.queryLoopOperationality_of_strongBridgeHypotheses
#print axioms PrimitiveHolonomy.Examples.queryRepairFamilyBySecondMarginWithBypass
#print axioms PrimitiveHolonomy.Examples.QueryRepairFamilyBySecondMarginWithBypass.queryLoopOperationality_of_strongBridgeHypotheses
/- AXIOM_AUDIT_END -/
