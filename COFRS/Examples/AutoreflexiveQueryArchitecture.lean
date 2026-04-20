import COFRS.Examples.IndependenceRelationMediationChain

/-!
# Autoreflexive query architecture

This file introduces an explicit Lean signature for the **query-loop architecture** suggested by
`COFRS/Examples/IndependenceRelationMediationChain.lean`.

The previous file already gives a strong **autoreferential** spine:

* marginal no-go / separation,
* irreducibility of the joint dynamic truth to each margin,
* exact finite mediation on the joint interface,
* minimality, and
* non-descent of the mediator.

What is added here is the next architectural layer:

* a state is built only from a legitimate pre-query visible channel,
* an action is chosen from that state,
* the environment answers using the hidden world and the chosen action,
* the state is updated from that answer,
* and the final decision is taken only after that update.

The file is deliberately constructive and lightweight:

* it separates `World`, pre-query visible history, and a forbidden bypass channel;
* it names the exact operational chain;
* it isolates several collapse modes (response and decision collapsing back to pre-query state);
* it introduces explicit **interventional branches** that force an action, and lets us state
  "action has an effect" at the level of response / post-state / decision;
* and it shows how a query architecture still induces an autoreferential architecture on the
  post-query state, without claiming minimality.

All proofs are definitional / constructive. The `AXIOM_AUDIT` block at the end must report no axioms.
-/

namespace PrimitiveHolonomy
namespace Examples

universe u v w x y z

/--
Minimal autoreferential architecture:

a hidden world exposes a legitimate visible channel, the visible channel is encoded into an
internal mediator, and the final decision is read from that mediator.
-/
structure AutoreferentialArchitecture where
  World : Type u
  HistoryVisible : Type v
  Mediator : Type w
  Output : Type x
  historyVisible : World → HistoryVisible
  encode : HistoryVisible → Mediator
  decide : Mediator → Output

namespace AutoreferentialArchitecture

/-- State before the final decision. -/
def mediator (A : AutoreferentialArchitecture) (world : A.World) : A.Mediator :=
  A.encode (A.historyVisible world)

/-- Final decision produced by the autoreferential architecture. -/
def run (A : AutoreferentialArchitecture) (world : A.World) : A.Output :=
  A.decide (A.mediator world)

/-!
`AutoreferentialArchitecture.run` always factors through `HistoryVisible` by definition.

We keep the following lemma as a named reminder of the trivial factorization, but we do *not*
use it as a non-degeneracy / bypass criterion.
-/

theorem run_factors_through_historyVisible (A : AutoreferentialArchitecture) :
    ∃ decideVisible : A.HistoryVisible → A.Output, ∀ world : A.World,
      A.run world = decideVisible (A.historyVisible world) := by
  refine ⟨fun hv => A.decide (A.encode hv), ?_⟩
  intro world
  rfl

/-- Minimal operational hooks for the base / ablation / swap audit on the mediator. -/
structure Audit (A : AutoreferentialArchitecture) where
  ablate : A.Mediator
  swap : A.Mediator → A.Mediator

namespace Audit

/-- Base branch of the mediator audit. -/
def baseDecision {A : AutoreferentialArchitecture} (_audit : A.Audit) (world : A.World) : A.Output :=
  A.run world

/-- Ablation branch of the mediator audit. -/
def ablatedDecision {A : AutoreferentialArchitecture} (audit : A.Audit) (_world : A.World) : A.Output :=
  A.decide audit.ablate

/-- Swap branch of the mediator audit. -/
def swappedDecision {A : AutoreferentialArchitecture} (audit : A.Audit) (world : A.World) : A.Output :=
  A.decide (audit.swap (A.mediator world))

@[simp] theorem baseDecision_eq_run
    {A : AutoreferentialArchitecture} (audit : A.Audit) (world : A.World) :
    audit.baseDecision world = A.run world := rfl

end Audit

end AutoreferentialArchitecture

/--
Autoreflexive query architecture:

* `historyVisible` is the legitimate pre-query visible information;
* `bypassVisible` is a forbidden local channel that should not directly determine the query;
* `query` is chosen from the internal state;
* `env` answers using the hidden world and the chosen action;
* `update` builds the post-query state from the response;
* `decide` reads only the post-query state.
-/
structure AutoreflexiveQueryArchitecture where
  World : Type u
  HistoryVisible : Type v
  BypassVisible : Type w
  State : Type x
  Action : Type y
  Response : Type z
  Output : Type (max u (max v (max w (max x (max y z)))))
  historyVisible : World → HistoryVisible
  bypassVisible : World → BypassVisible
  encode : HistoryVisible → State
  query : State → Action
  env : World → Action → Response
  update : State → Response → State
  decide : State → Output

namespace AutoreflexiveQueryArchitecture

/-- State constructed before any action is chosen. -/
def preState (A : AutoreflexiveQueryArchitecture) (world : A.World) : A.State :=
  A.encode (A.historyVisible world)

/-- Action chosen from the pre-query state. -/
def chosenAction (A : AutoreflexiveQueryArchitecture) (world : A.World) : A.Action :=
  A.query (A.preState world)

/-- Environment response produced by the chosen action in the given world. -/
def returnedResponse (A : AutoreflexiveQueryArchitecture) (world : A.World) : A.Response :=
  A.env world (A.chosenAction world)

/-- State after incorporating the response to the chosen action. -/
def postState (A : AutoreflexiveQueryArchitecture) (world : A.World) : A.State :=
  A.update (A.preState world) (A.returnedResponse world)

/-- Final decision read after the state has been updated by the response. -/
def run (A : AutoreflexiveQueryArchitecture) (world : A.World) : A.Output :=
  A.decide (A.postState world)

/--
Recoverability from the forbidden channel:
the chosen action is reconstructible from the forbidden visible channel alone.

This is an information-level notion. It is not a "causal access" notion: it can hold even when the
architecture never reads the forbidden channel, if the world makes it reconstructible.
-/
def ActionRecoverableFromForbiddenChannel (A : AutoreflexiveQueryArchitecture) : Prop :=
  ∃ queryBypass : A.BypassVisible → A.Action, ∀ world : A.World,
    A.chosenAction world = queryBypass (A.bypassVisible world)

/-- Backwards-compatible name. -/
abbrev ActionRecoverableFromBypass (A : AutoreflexiveQueryArchitecture) : Prop :=
  A.ActionRecoverableFromForbiddenChannel

/-- Collapse mode: the returned response (under the chosen action) was already recoverable from the pre-query state. -/
def ResponseFactorsThroughPreStateChosen (A : AutoreflexiveQueryArchitecture) : Prop :=
  ∃ responsePre : A.State → A.Response, ∀ world : A.World,
    A.returnedResponse world = responsePre (A.preState world)

/-- Collapse mode: the post-query state (under the chosen action) was already recoverable from the pre-query state. -/
def PostStateFactorsThroughPreStateChosen (A : AutoreflexiveQueryArchitecture) : Prop :=
  ∃ postFromPre : A.State → A.State, ∀ world : A.World,
    A.postState world = postFromPre (A.preState world)

/-- Collapse mode: the final decision (under the chosen action) was already recoverable from the pre-query state. -/
def DecisionFactorsThroughPreStateChosen (A : AutoreflexiveQueryArchitecture) : Prop :=
  ∃ decidePre : A.State → A.Output, ∀ world : A.World,
    A.run world = decidePre (A.preState world)

/--
Recoverability from the forbidden channel:
the final decision is reconstructible from the forbidden visible channel alone.

This is an information-level notion. It is not a "causal access" notion.
-/
def DecisionRecoverableFromForbiddenChannel (A : AutoreflexiveQueryArchitecture) : Prop :=
  ∃ decideBypass : A.BypassVisible → A.Output, ∀ world : A.World,
    A.run world = decideBypass (A.bypassVisible world)

/-- Backwards-compatible name. -/
abbrev DecisionRecoverableFromBypass (A : AutoreflexiveQueryArchitecture) : Prop :=
  A.DecisionRecoverableFromForbiddenChannel

/-- Degenerate regime: for each world, the environment answer ignores the action. -/
def ResponseIndependentOfAction (A : AutoreflexiveQueryArchitecture) : Prop :=
  ∃ responseWorld : A.World → A.Response, ∀ world : A.World, ∀ action : A.Action,
    A.env world action = responseWorld world

/-- Stronger non-degeneracy: some actions actually realized by the policy lead to different answers. -/
def RealizedActionHasEffect (A : AutoreflexiveQueryArchitecture) : Prop :=
  ∃ world₀ world₁ world₂ : A.World,
    A.chosenAction world₁ ≠ A.chosenAction world₂
      ∧ A.env world₀ (A.chosenAction world₁) ≠ A.env world₀ (A.chosenAction world₂)

/-!
## Explicit interventional branches (force an action)

To reason about query-loop causality, we introduce explicit "force the action" versions of
response / post-state / decision. These definitions are purely operational and stay constructive.
-/

/-- Response if we force a particular action in a world. -/
def returnedResponseUnder (A : AutoreflexiveQueryArchitecture) (world : A.World) (action : A.Action) : A.Response :=
  A.env world action

/-- Post-query state if we force a particular action in a world. -/
def postStateUnder (A : AutoreflexiveQueryArchitecture) (world : A.World) (action : A.Action) : A.State :=
  A.update (A.preState world) (A.returnedResponseUnder world action)

/-- Final decision if we force a particular action in a world. -/
def runUnder (A : AutoreflexiveQueryArchitecture) (world : A.World) (action : A.Action) : A.Output :=
  A.decide (A.postStateUnder world action)

@[simp] theorem runUnder_chosenAction_eq_run
    (A : AutoreflexiveQueryArchitecture) (world : A.World) :
    A.runUnder world (A.chosenAction world) = A.run world := by
  rfl

/-!
### Interventional collapse (response under)

This is the response-level analogue of `PostStateFactorsThroughPreStateUnder` and
`DecisionFactorsThroughPreStateUnder`.
-/

/-- Interventional collapse at the response level: forcing actions cannot change the response. -/
def ResponseFactorsThroughPreStateUnder (A : AutoreflexiveQueryArchitecture) : Prop :=
  ∃ responsePre : A.State → A.Response, ∀ world : A.World, ∀ action : A.Action,
    A.returnedResponseUnder world action = responsePre (A.preState world)

/-!
Two interventional non-degeneracy notions:

* `RealizedActionHasEffect` is a response-level effect (already present above).
* `RealizedActionHasDecisionEffect` is the corresponding decision-level effect under forced actions.
-/

/-- Some realized actions, when forced, change the final decision in a fixed world. -/
def RealizedActionHasDecisionEffect (A : AutoreflexiveQueryArchitecture) : Prop :=
  ∃ world₀ world₁ world₂ : A.World,
    A.chosenAction world₁ ≠ A.chosenAction world₂
      ∧ A.runUnder world₀ (A.chosenAction world₁) ≠ A.runUnder world₀ (A.chosenAction world₂)

/-- Some realized actions, when forced, change the post-query state in a fixed world. -/
def RealizedActionHasPostStateEffect (A : AutoreflexiveQueryArchitecture) : Prop :=
  ∃ world₀ world₁ world₂ : A.World,
    A.chosenAction world₁ ≠ A.chosenAction world₂
      ∧ A.postStateUnder world₀ (A.chosenAction world₁) ≠ A.postStateUnder world₀ (A.chosenAction world₂)

/-!
Interventional collapse: even if we force arbitrary actions, the decision can already be computed
from the pre-query state alone. This captures the failure mode "the loop is a syntactic loop, but
has no effect at decision time".
-/

def DecisionFactorsThroughPreStateUnder (A : AutoreflexiveQueryArchitecture) : Prop :=
  ∃ decidePre : A.State → A.Output, ∀ world : A.World, ∀ action : A.Action,
    A.runUnder world action = decidePre (A.preState world)

/-- Interventional collapse at the post-state level: forcing actions cannot change `postState`. -/
def PostStateFactorsThroughPreStateUnder (A : AutoreflexiveQueryArchitecture) : Prop :=
  ∃ postPre : A.State → A.State, ∀ world : A.World, ∀ action : A.Action,
    A.postStateUnder world action = postPre (A.preState world)

/-- Under response collapse, post-state collapse follows trivially. -/
theorem postStateFactorsThroughPreStateUnder_of_responseFactorsThroughPreStateUnder
    (A : AutoreflexiveQueryArchitecture)
    (hResp : A.ResponseFactorsThroughPreStateUnder) :
    A.PostStateFactorsThroughPreStateUnder := by
  rcases hResp with ⟨responsePre, hResp⟩
  refine ⟨fun state => A.update state (responsePre state), ?_⟩
  intro world action
  dsimp [postStateUnder, preState, returnedResponseUnder]
  have h := hResp world action
  dsimp [returnedResponseUnder, preState] at h
  exact congrArg (A.update (A.encode (A.historyVisible world))) h

/-- Under post-state collapse, decision-under-forced-action collapse follows trivially. -/
theorem decisionFactorsThroughPreStateUnder_of_postStateFactorsThroughPreStateUnder
    (A : AutoreflexiveQueryArchitecture)
    (hPost : A.PostStateFactorsThroughPreStateUnder) :
    A.DecisionFactorsThroughPreStateUnder := by
  rcases hPost with ⟨postPre, hPost⟩
  refine ⟨fun state => A.decide (postPre state), ?_⟩
  intro world action
  dsimp [runUnder, postStateUnder, preState, returnedResponseUnder]
  have h := hPost world action
  dsimp [postStateUnder, returnedResponseUnder, preState] at h
  exact congrArg A.decide h

/-- Under response collapse, decision-under-forced-action collapse follows by composition. -/
theorem decisionFactorsThroughPreStateUnder_of_responseFactorsThroughPreStateUnder
    (A : AutoreflexiveQueryArchitecture)
    (hResp : A.ResponseFactorsThroughPreStateUnder) :
    A.DecisionFactorsThroughPreStateUnder := by
  exact A.decisionFactorsThroughPreStateUnder_of_postStateFactorsThroughPreStateUnder
    (A.postStateFactorsThroughPreStateUnder_of_responseFactorsThroughPreStateUnder hResp)

/-- Same-world alternative-action audit: in some world, an alternative action changes the decision. -/
def ExistsAlternativeActionDecisionEffect (A : AutoreflexiveQueryArchitecture) : Prop :=
  ∃ world : A.World, ∃ altAction : A.Action,
    altAction ≠ A.chosenAction world ∧ A.runUnder world altAction ≠ A.run world

/-- A same-world alternative-action effect rules out decision collapse under forced actions. -/
theorem not_decisionFactorsThroughPreStateUnder_of_existsAlternativeActionDecisionEffect
    (A : AutoreflexiveQueryArchitecture)
    (hAlt : A.ExistsAlternativeActionDecisionEffect) :
    ¬ A.DecisionFactorsThroughPreStateUnder := by
  intro hUnder
  rcases hUnder with ⟨decidePre, hUnder⟩
  rcases hAlt with ⟨world, altAction, _hneAlt, hneRun⟩
  have h1 : A.runUnder world altAction = decidePre (A.preState world) :=
    hUnder world altAction
  have h2 : A.run world = decidePre (A.preState world) := by
    calc
      A.run world = A.runUnder world (A.chosenAction world) := by
        symm
        exact A.runUnder_chosenAction_eq_run world
      _ = decidePre (A.preState world) :=
        hUnder world (A.chosenAction world)
  exact hneRun (h1.trans h2.symm)

/--
Operational query-loop contract.

This is intentionally stronger than a mere syntactic loop: it excludes several collapse modes
that would reduce the architecture back to a purely autoreferential computation on `preState`
(even under forced actions), or to a forbidden bypass channel.
-/
structure QueryLoopOperationality (A : AutoreflexiveQueryArchitecture) : Prop where
  noActionBypass : ¬ A.ActionRecoverableFromBypass
  realizedActionHasEffect : A.RealizedActionHasEffect
  realizedActionHasPostStateEffect : A.RealizedActionHasPostStateEffect
  realizedActionHasDecisionEffect : A.RealizedActionHasDecisionEffect
  existsAlternativeActionDecisionEffect : A.ExistsAlternativeActionDecisionEffect
  decisionUsesMoreThanPreStateChosen : ¬ A.DecisionFactorsThroughPreStateChosen
  noDecisionBypass : ¬ A.DecisionRecoverableFromBypass

@[simp] theorem preState_eq_encode_historyVisible
    (A : AutoreflexiveQueryArchitecture) (world : A.World) :
    A.preState world = A.encode (A.historyVisible world) := rfl

@[simp] theorem chosenAction_eq_query_preState
    (A : AutoreflexiveQueryArchitecture) (world : A.World) :
    A.chosenAction world = A.query (A.preState world) := rfl

@[simp] theorem returnedResponse_eq_env_world_action
    (A : AutoreflexiveQueryArchitecture) (world : A.World) :
    A.returnedResponse world = A.env world (A.chosenAction world) := rfl

@[simp] theorem postState_eq_update_preState_returnedResponse
    (A : AutoreflexiveQueryArchitecture) (world : A.World) :
    A.postState world = A.update (A.preState world) (A.returnedResponse world) := rfl

@[simp] theorem run_eq_decide_postState
    (A : AutoreflexiveQueryArchitecture) (world : A.World) :
    A.run world = A.decide (A.postState world) := rfl

/-- If the response was already recoverable from `preState` (chosen-action branch), then `postState` was too. -/
theorem postStateFactorsThroughPreStateChosen_of_responseFactorsThroughPreStateChosen
    (A : AutoreflexiveQueryArchitecture)
    (hResp : A.ResponseFactorsThroughPreStateChosen) :
    A.PostStateFactorsThroughPreStateChosen := by
  rcases hResp with ⟨responsePre, hResp⟩
  refine ⟨fun state => A.update state (responsePre state), ?_⟩
  intro world
  dsimp [postState, preState, returnedResponse, chosenAction]
  have h := hResp world
  dsimp [returnedResponse, chosenAction, preState] at h
  exact congrArg (A.update (A.encode (A.historyVisible world))) h

/-- If the post-query state was already recoverable from `preState` (chosen-action branch), then the final decision was too. -/
theorem decisionFactorsThroughPreStateChosen_of_postStateFactorsThroughPreStateChosen
    (A : AutoreflexiveQueryArchitecture)
    (hPost : A.PostStateFactorsThroughPreStateChosen) :
    A.DecisionFactorsThroughPreStateChosen := by
  rcases hPost with ⟨postFromPre, hPost⟩
  refine ⟨fun state => A.decide (postFromPre state), ?_⟩
  intro world
  dsimp [run, postState, returnedResponse, chosenAction, preState]
  have h := hPost world
  dsimp [postState, returnedResponse, chosenAction, preState] at h
  exact congrArg A.decide h

/-- Therefore response collapse already implies decision collapse. -/
theorem decisionFactorsThroughPreStateChosen_of_responseFactorsThroughPreStateChosen
    (A : AutoreflexiveQueryArchitecture)
    (hResp : A.ResponseFactorsThroughPreStateChosen) :
    A.DecisionFactorsThroughPreStateChosen := by
  exact A.decisionFactorsThroughPreStateChosen_of_postStateFactorsThroughPreStateChosen
    (A.postStateFactorsThroughPreStateChosen_of_responseFactorsThroughPreStateChosen hResp)

/-- If the environment ignores the action, then no realized action can make a difference. -/
theorem not_realizedActionHasEffect_of_responseIndependentOfAction
    (A : AutoreflexiveQueryArchitecture)
    (hIndep : A.ResponseIndependentOfAction) :
    ¬ A.RealizedActionHasEffect := by
  intro hEffect
  rcases hIndep with ⟨responseWorld, hResp⟩
  rcases hEffect with ⟨world₀, world₁, world₂, _hne, hneResp⟩
  have h1 : A.env world₀ (A.chosenAction world₁) = responseWorld world₀ := hResp world₀ (A.chosenAction world₁)
  have h2 : A.env world₀ (A.chosenAction world₂) = responseWorld world₀ := hResp world₀ (A.chosenAction world₂)
  exact hneResp (h1.trans h2.symm)

theorem not_responseIndependentOfAction_of_realizedActionHasEffect
    (A : AutoreflexiveQueryArchitecture)
    (hEff : A.RealizedActionHasEffect) :
    ¬ A.ResponseIndependentOfAction := by
  intro hIndep
  exact (A.not_realizedActionHasEffect_of_responseIndependentOfAction hIndep) hEff

theorem responseIndependentOfAction_of_responseFactorsThroughPreStateUnder
    (A : AutoreflexiveQueryArchitecture)
    (hResp : A.ResponseFactorsThroughPreStateUnder) :
    A.ResponseIndependentOfAction := by
  rcases hResp with ⟨responsePre, hResp⟩
  refine ⟨fun world => responsePre (A.preState world), ?_⟩
  intro world action
  have h := hResp world action
  dsimp [returnedResponseUnder] at h
  exact h

theorem not_realizedActionHasEffect_of_responseFactorsThroughPreStateUnder
    (A : AutoreflexiveQueryArchitecture)
    (hResp : A.ResponseFactorsThroughPreStateUnder) :
    ¬ A.RealizedActionHasEffect := by
  intro hEff
  have hIndep : A.ResponseIndependentOfAction :=
    A.responseIndependentOfAction_of_responseFactorsThroughPreStateUnder hResp
  exact (A.not_realizedActionHasEffect_of_responseIndependentOfAction hIndep) hEff

theorem not_responseFactorsThroughPreStateUnder_of_realizedActionHasEffect
    (A : AutoreflexiveQueryArchitecture)
    (hEff : A.RealizedActionHasEffect) :
    ¬ A.ResponseFactorsThroughPreStateUnder := by
  intro hResp
  exact (A.not_realizedActionHasEffect_of_responseFactorsThroughPreStateUnder hResp) hEff

theorem not_postStateFactorsThroughPreStateUnder_of_realizedActionHasPostStateEffect
    (A : AutoreflexiveQueryArchitecture)
    (hEff : A.RealizedActionHasPostStateEffect) :
    ¬ A.PostStateFactorsThroughPreStateUnder := by
  intro hPost
  rcases hPost with ⟨postPre, hPost⟩
  rcases hEff with ⟨world₀, world₁, world₂, _hneAct, hnePost⟩
  have h1 : A.postStateUnder world₀ (A.chosenAction world₁) = postPre (A.preState world₀) :=
    hPost world₀ (A.chosenAction world₁)
  have h2 : A.postStateUnder world₀ (A.chosenAction world₂) = postPre (A.preState world₀) :=
    hPost world₀ (A.chosenAction world₂)
  exact hnePost (h1.trans h2.symm)

/-!
## Basic consequences of operationality

We keep these as small lemmas:

* under operationality, chosen-action response collapse is ruled out (it would imply chosen-action decision collapse),
* and decision-under-forced-action collapse is ruled out by `realizedActionHasDecisionEffect`.
-/

theorem not_responseFactorsThroughPreStateChosen_of_queryLoopOperationality
    (A : AutoreflexiveQueryArchitecture)
    (hOp : A.QueryLoopOperationality) :
    ¬ A.ResponseFactorsThroughPreStateChosen := by
  intro hResp
  have hDec := A.decisionFactorsThroughPreStateChosen_of_responseFactorsThroughPreStateChosen hResp
  exact hOp.decisionUsesMoreThanPreStateChosen hDec

theorem not_postStateFactorsThroughPreStateChosen_of_queryLoopOperationality
    (A : AutoreflexiveQueryArchitecture)
    (hOp : A.QueryLoopOperationality) :
    ¬ A.PostStateFactorsThroughPreStateChosen := by
  intro hPost
  have hDec := A.decisionFactorsThroughPreStateChosen_of_postStateFactorsThroughPreStateChosen hPost
  exact hOp.decisionUsesMoreThanPreStateChosen hDec

theorem not_responseIndependentOfAction_of_queryLoopOperationality
    (A : AutoreflexiveQueryArchitecture)
    (hOp : A.QueryLoopOperationality) :
    ¬ A.ResponseIndependentOfAction :=
  A.not_responseIndependentOfAction_of_realizedActionHasEffect hOp.realizedActionHasEffect

theorem not_responseFactorsThroughPreStateUnder_of_queryLoopOperationality
    (A : AutoreflexiveQueryArchitecture)
    (hOp : A.QueryLoopOperationality) :
    ¬ A.ResponseFactorsThroughPreStateUnder :=
  A.not_responseFactorsThroughPreStateUnder_of_realizedActionHasEffect hOp.realizedActionHasEffect

theorem not_postStateFactorsThroughPreStateUnder_of_queryLoopOperationality
    (A : AutoreflexiveQueryArchitecture)
    (hOp : A.QueryLoopOperationality) :
    ¬ A.PostStateFactorsThroughPreStateUnder :=
  A.not_postStateFactorsThroughPreStateUnder_of_realizedActionHasPostStateEffect hOp.realizedActionHasPostStateEffect

theorem not_decisionFactorsThroughPreStateUnder_of_realizedActionHasDecisionEffect
    (A : AutoreflexiveQueryArchitecture)
    (hEff : A.RealizedActionHasDecisionEffect) :
    ¬ A.DecisionFactorsThroughPreStateUnder := by
  intro hUnder
  rcases hUnder with ⟨decidePre, hUnder⟩
  rcases hEff with ⟨world₀, world₁, world₂, hneAct, hneDec⟩
  have h1 : A.runUnder world₀ (A.chosenAction world₁) = decidePre (A.preState world₀) :=
    hUnder world₀ (A.chosenAction world₁)
  have h2 : A.runUnder world₀ (A.chosenAction world₂) = decidePre (A.preState world₀) :=
    hUnder world₀ (A.chosenAction world₂)
  exact hneDec (h1.trans h2.symm)

theorem not_decisionFactorsThroughPreStateUnder_of_queryLoopOperationality
    (A : AutoreflexiveQueryArchitecture)
    (hOp : A.QueryLoopOperationality) :
    ¬ A.DecisionFactorsThroughPreStateUnder :=
  A.not_decisionFactorsThroughPreStateUnder_of_realizedActionHasDecisionEffect hOp.realizedActionHasDecisionEffect

theorem not_decisionFactorsThroughPreStateUnder_of_queryLoopOperationality_alt
    (A : AutoreflexiveQueryArchitecture)
    (hOp : A.QueryLoopOperationality) :
    ¬ A.DecisionFactorsThroughPreStateUnder :=
  A.not_decisionFactorsThroughPreStateUnder_of_existsAlternativeActionDecisionEffect
    hOp.existsAlternativeActionDecisionEffect

/--
The query architecture induces an autoreferential architecture on the **post-query** state.

This is a factorization theorem only; it does not claim any compatibility-dimension minimality.
-/
def toAutoreferential (A : AutoreflexiveQueryArchitecture) : AutoreferentialArchitecture where
  World := A.World
  HistoryVisible := A.State
  Mediator := A.State
  Output := A.Output
  historyVisible := A.postState
  encode := id
  decide := A.decide

@[simp] theorem toAutoreferential_mediator_eq_postState
    (A : AutoreflexiveQueryArchitecture) (world : A.World) :
    (A.toAutoreferential).mediator world = A.postState world := rfl

@[simp] theorem toAutoreferential_run_eq
    (A : AutoreflexiveQueryArchitecture) (world : A.World) :
    (A.toAutoreferential).run world = A.run world := rfl

/-- The final decision always factors through the post-query state. -/
theorem run_factors_through_postState
    (A : AutoreflexiveQueryArchitecture) :
    ∃ decidePost : A.State → A.Output, ∀ world : A.World,
      A.run world = decidePost (A.postState world) := by
  refine ⟨A.decide, ?_⟩
  intro world
  rfl

/-- The query architecture decomposes explicitly into the five named operations of the loop. -/
theorem run_eq_query_loop_chain
    (A : AutoreflexiveQueryArchitecture) (world : A.World) :
    A.run world =
      A.decide
        (A.update
          (A.encode (A.historyVisible world))
          (A.env world (A.query (A.encode (A.historyVisible world))))) := by
  rfl

end AutoreflexiveQueryArchitecture

end Examples
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.Examples.AutoreferentialArchitecture.run
#print axioms PrimitiveHolonomy.Examples.AutoreflexiveQueryArchitecture.runUnder_chosenAction_eq_run
#print axioms PrimitiveHolonomy.Examples.AutoreflexiveQueryArchitecture.postStateFactorsThroughPreStateUnder_of_responseFactorsThroughPreStateUnder
#print axioms PrimitiveHolonomy.Examples.AutoreflexiveQueryArchitecture.not_responseFactorsThroughPreStateUnder_of_queryLoopOperationality
#print axioms PrimitiveHolonomy.Examples.AutoreflexiveQueryArchitecture.not_postStateFactorsThroughPreStateUnder_of_queryLoopOperationality
#print axioms PrimitiveHolonomy.Examples.AutoreflexiveQueryArchitecture.not_decisionFactorsThroughPreStateUnder_of_existsAlternativeActionDecisionEffect
#print axioms PrimitiveHolonomy.Examples.AutoreflexiveQueryArchitecture.not_responseFactorsThroughPreStateChosen_of_queryLoopOperationality
#print axioms PrimitiveHolonomy.Examples.AutoreflexiveQueryArchitecture.not_decisionFactorsThroughPreStateUnder_of_queryLoopOperationality
#print axioms PrimitiveHolonomy.Examples.AutoreflexiveQueryArchitecture.toAutoreferential_run_eq
#print axioms PrimitiveHolonomy.Examples.AutoreflexiveQueryArchitecture.run_eq_query_loop_chain
/- AXIOM_AUDIT_END -/
