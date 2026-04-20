# New Transformer architecture targeted by the project

This file describes the Transformer architecture that the project aims to validate.

This is not an external audit of existing models.
It is an architectural specification: Lean theory provides the structural contract, and empirical protocols test its validity.

Reading conventions:

- `description` = human level interpretation of the phenomenon
- `strict spec` = objects, functions, and explicit chain
- `operationality` = the exact operation that carries the term in the protocol
- `attestation` = what the test actually computes to support the property

## Theoretical preface

The architectural thesis of the project does not start from a vague intuition about internal memory. It relies on a stronger conceptual result, already formalized in the project Lean theory for the two-interface case. This theory exhibits the following chain: diagonal obstructions on each marginal certify that the targeted dynamic truth does not close on the marginal observations taken separately; this non-closure can be constructively converted into an explicit fiber separation; the resulting joint truth is reducible neither to the left projection nor to the right projection; and repairing it then requires an exact finite mediator on the joint interface, with a minimal dimension. The mediator therefore does not appear as an opportunistic latent added to predict better. It appears as the minimal internal variable required to carry a dynamic relation that the marginal visible does not contain. Moreover, if this mediator could descend back to a single margin, the joint truth would become predictable from that margin, contradicting the initial obstruction. In the binary case, this mediation even forces an interventional causal signature. The architectural meaning is then clear: when closure on the visible fails structurally, the right form is no longer visible -> output, but interface(s) -> mediator -> decision. This foundation justifies the minimal autoreferential version of the project. The autoreflexive extension is its natural continuation, when internal state is not only used to mediate the decision, but also to reconfigure subsequent access to information.

### Referential frame

This whole document is relative to a fixed referential frame:

- a decision interface (what is considered visible at decision time)
- a targeted dynamic truth (what the solver must decide correctly)

In this frame, the goal is not to classify architectures by syntactic family, but to stratify admissible solver regimes by the closure regime of the truth relative to the interface.

Working formulation:

- if the truth closes on the visible, a visible-only solver is admissible
- if the truth does not close on the visible, any correct solution must go through a mediation that does not descend to the marginals
- if this mediation admits an exact finite compression, we obtain an autoreferential regime
- if the mediation is forced by a query loop that reconfigures access to information from the internal state, we obtain an autoreflexive regime

## 1. Guiding idea

The project does not target a Transformer that decides only from the visible interface provided at decision time.

The project targets a Transformer in which:

- closure on the visible can fail structurally
- this non-closure forces the appearance of an internal mediator
- this mediator has a measurable finite capacity
- the final decision effectively depends on this mediator
- and this dependence can be tested by interventions

So the thesis is architectural:

- the right architecture is not a simple visible-to-output architecture
- the right architecture is an explicit mediation architecture

In the project vocabulary, this means from the start:

- an autoreferential architecture
- and, in its richest extension, an autoreflexive architecture

## 2. What this architecture is not

This architecture is not:

- a standard Transformer that reads an interface and directly produces an output
- a simple Transformer with more size or more data
- a system with unconstrained implicit memory
- a latent added opportunistically without a capacity contract and without causal testing

The project does not merely try to show that a model with memory can work better.
It aims to validate an architecture where internal mediation is part of the system contract.

## 3. Core of the architecture

The core of the new Transformer architecture is the following.

### 3.1 Interface encoders

The system receives one or more interfaces.
Depending on the protocols, this can be:

- a decision image
- a cue image
- multiple views
- multiple quotients or multiple partial interfaces

Each interface is encoded by a Transformer-like block, or by an equivalent module compatible with the system contract.

### 3.2 Explicit internal mediator

The architecture must produce an internal state that carries the missing information for the targeted dynamic truth.

This mediator:

- is not a hidden residue left without interpretation
- must be read as an internal decision object
- must have controllable capacity
- must support ablation and permutation tests

In the current witnesses, this role is played by `z`.

### 3.2 bis Autoreferentiality

Description:

Autoreferentiality is not a vague word here.
It denotes the following empirical fact:

- the correct decision does not close on the visible alone
- the system must go through an internal state that it carries itself
- this internal state serves as a mediator for the targeted dynamic truth
- the decision head must therefore depend on this mediator

In other words, the architecture is called autoreferential when the system must pass through its own internal mediation to decide correctly.

Operational attestation:

- the visible alone hits an explicit barrier, or a visible-only baseline saturates
- a named internal mediator is present in the protocol
- A's decision depends on this mediator structurally
- the protocol computes, on the same cases, the three branches base, ablation, swap
- ablation degrades the decision sharply
- swap breaks alignment to the original labels and instead follows the expected permutation

In practice, we consider autoreferentiality attested only if the protocol exposes the mediator and the metrics `ablation_drop`, `swap_vs_orig`, `swap_vs_perm` show that it is effectively load bearing.

Lean anchoring:

- step-local finite mediation and minimality: `CompatDimEq` and `RefiningLift` in `COFRS/Dynamics.lean`
- joint irreducibility and mediator non-descent: `COFRS/Examples/IndependenceRelationMediationChain.lean`
- minimal architectural reading of state then decision: `AutoreferentialArchitecture` in `COFRS/Examples/AutoreflexiveQueryArchitecture.lean`

Strict spec:

- `v` = input visible
- `z` = internal mediator
- `y` = final decision

Operational chain:

- `z = Encode(v)`
- `y = Decide(z)`

Word for each term:

- `v` = visible
- `z` = mediator
- `y` = decision

Strict meaning in this project:

- autoreferentiality = `v -> z -> y`
- and not `v -> y`

Strict operationality:

- the explicit operation is mediation through `z`
- in other words, the decision is computed through `z`

Test computation:

- `base` = `y = Decide(z)`
- `ablation` = `y = Decide(0)`
- `swap` = `y_i = Decide(z_j)`

Expected attestation:

- strong `ablation_drop`
- high `swap_vs_perm`
- degraded `swap_vs_orig`

Exact operation in the protocol:

- an internal mediator `z` is computed
- the final decision is read through `z`
- ablation replaces `z` by `0`
- swap replaces `z_i` by `z_j`
- decision variation explicitly measures the load of `z`

Human level reading:

- the system cannot decide correctly from the visible alone
- it must first build an internal mediator
- then the final decision is read through this mediator
- that is what makes the architecture autoreferential

So here, autoreferentiality does not merely mean:

- internal state

It means strictly:

- input visible
- then construction of an internal mediator
- then final decision read through this mediator

And its experimental attestation means strictly:

- `base` branch on `z`
- `ablation` branch on `0`
- `swap` branch on permuted `z`
- explicit comparison of the obtained outputs

### 3.3 Decision head locked by state

The most important point is that the decision head must not short-circuit the mediator.

The final decision must be produced from the mediator, or from an extended interface in which the mediator plays a structurally necessary role.

In the cleanest form of this principle:

- the head reads only the global latent `z`

In other working forms present in the repository:

- the decision is conditioned by a structured combination of the mediator and a necessary visible term

But in all cases, mediation must not be bypassable by a direct read of the visible.

### 3.4 Interventional audit of the mediator

The mediator must carry causal load.

This means the architecture must support operations such as:

- mediator ablation
- mediator permutation or swap between examples
- optionally reconfiguration of access from internal state

If the architecture is correct, the decision must follow these interventions in the expected way.

### 3.5 Autoreflexivity

Description:

Autoreflexivity denotes a stronger empirical regime here.

In this regime:

- internal state is not only used to carry missing information
- it is also used to steer subsequent access to information
- it can select a view, a quotient, a query, or a next interaction
- the final decision is therefore made under an access transformed by the system itself

Autoreflexivity extends autoreferentiality.
It adds to internal mediation an action of the system on its own conditions of access to the decision.

Operational attestation:

- internal state to choice of action
- choice of action to new observation or query result
- new observation to final decision

So this is not only a memory test.
It is a test where internal state drives an action that then modifies the empirical decision regime.

Strict spec:

- `x` = initial views
- `m` = internal state before action
- `a` = query action
- `r` = environment return
- `m'` = internal state after return
- `y` = final decision

Operational chain:

- `m = Encode(x)`
- `a = Query(m)`
- `r = Env(a)`
- `m' = Update(m, r)`
- `y = Decide(m')`

Strict spec (Lean correspondence):

- architecture: `AutoreflexiveQueryArchitecture` in `COFRS/Examples/AutoreflexiveQueryArchitecture.lean`
- execution: `preState`, `chosenAction`, `returnedResponse`, `postState`, `run`
- interventional branches: `returnedResponseUnder`, `postStateUnder`, `runUnder`
- testable effects: `RealizedActionHasEffect`, `RealizedActionHasPostStateEffect`, `RealizedActionHasDecisionEffect`, `ExistsAlternativeActionDecisionEffect`
- testable collapses: `DecisionFactorsThroughPreStateChosen`, `DecisionFactorsThroughPreStateUnder`, `DecisionRecoverableFromForbiddenChannel`

Word for each term:

- `m` = internal state
- `a` = action
- `r` = new observation
- `m'` = updated state
- `y` = decision

Strict meaning in this project:

- autoreflexivity = `m -> a -> r -> m' -> y`
- its properly autoreflexive part = `m -> a -> r`

Strict operationality:

- the explicit operation is not only `Decide`
- the explicit operation is `Query` then `Env`
- in other words, the system acts from its internal state to produce new information before deciding

Structural condition:

- there must exist a real `Query` step
- there must exist a real `Env` step
- decision must happen after `r`
- an anti bypass must forbid a short-circuit of the decision by the current visible

Anti bypass clarification:

- structural anti bypass: a forbidden data path in the architecture (the current visible cannot be read directly by the action module)
- recoverability anti bypass: an information-level, testable condition saying that the action or decision are not reconstructible from a forbidden channel alone

The file `COFRS/Examples/AutoreflexiveQueryArchitecture.lean` is explicitly at the recoverability level for `ActionRecoverableFromForbiddenChannel` and `DecisionRecoverableFromForbiddenChannel`.

Expected attestation:

- the action is computed from internal state and not from the current visible
- this action produces a new intermediate observation or result
- the final decision depends on this loop and not on a direct bypass

Exact instance in `law_v3b`:

- `m = FoldViews(view_seq)`
- `a = QueryHead(m)`
- `r = Env(a)` with return `res_tok`
- `m' = Update(m, r)`
- `y = OutHead(m')`

Exact operation in `law_v3b`:

- internal memory is built by accumulating views
- the query is chosen by `logits_query(mem_for_query)`
- the current visible is explicitly neutralized before the query by anti bypass
- the query then calls the environment and produces `res_tok`
- the final decision is then read after this transition

Human level reading:

- the model builds a state
- it chooses a query from that state
- this query makes new information appear
- then the model decides

So here, autoreflexivity does not merely mean:

- internal memory

It means strictly:

- internal memory
- then a query chosen from this memory
- then an environment return
- then a final decision under this new access

Complementary reading:

- internal state is not only used to memorize
- it is used to choose what to do next
- this action then changes what the system can effectively know
- the final decision is taken after this access transformation
- that is what makes the architecture autoreflexive

## 4. Current form in the repository

The repository contains several partial or more advanced witnesses of this architecture.

Convention for this section:

- each line below designates a contract witness
- a witness is not necessarily the complete final architecture
- but it explicitly instantiates part of the spec

### 4.1 Stateful JEPA line

Description:

In `v7` and `v8`, we already see a clear line:

- Transformer-like encoder on the inputs
- internal state updated across views
- mask head predicted from the state
- ablation and swap variants

This line shows the break from a visible-only regime.

It mostly attests autoreference in the operational sense.
It is not yet the full form of autoreflexivity, because there is not yet an explicit query policy that reconfigures access to the problem.

Strict spec of the witness:

- `x = (v_1, ..., v_T)` = sequence of views
- `m = FoldViews(x)` = accumulated internal state
- `y = MaskHead(m)` = output read from the state

Strict operationality:

- state is updated view after view
- the head reads this state to produce the output
- `ablation` and `swap` operations are applied to this state

Attestation:

- the output follows the `base` branch
- it drops under `ablation`
- it follows the permuted latent under `swap`

### 4.1 bis Autoreflexive query POMDP line

Description:

In `law_v3b`, the project already carries an explicit empirical form of autoreflexivity:

- an internal memory state is built from the view sequence
- a query action is chosen from this internal state
- this action then produces an environment result
- and the final decision is taken after this access reconfiguration

The decisive point is that the query does not read the current visible directly as the source of internal decision.
The protocol explicitly enforces an anti bypass before the query.

So this line is not only autoreferential.
It is already autoreflexive in the operational sense of the tests.

Strict spec of the witness:

- `m = FoldViews(view_seq)`
- `a = QueryHead(m)`
- `r = Env(a)`
- `m' = Update(m, r)`
- `y = OutHead(m')`

Strict operationality:

- the query is computed from `m`
- the return `r` exists only after action `a`
- the final decision is read after being updated by `r`

Attestation:

- anti bypass on the current visible
- verification of the loop `m -> a -> r -> y`
- causal audit on the memory states

### 4.2 State-locked line

Description:

In `law_v5b`, the idea is even more explicit:

- architecture A computes a global latent `z`
- the head reads only this latent
- visible baselines remain constrained to local observable-only classes

Here, mediation is not only present.
It is locked architecturally.

Strict spec of the witness:

- `z = EncoderA(v)`
- `y = Head(z)`

Strict operationality:

- the decision head does not read the visible directly
- the decision head reads only `z`
- the visible therefore cannot short-circuit mediation

Attestation:

- `base / ablation / swap` audit on `z`
- comparison against visible-only baselines

### 4.3 Min-lift line

Description:

In `vN3b`, `v9`, `v10` and their follow-ups:

- the mediator `z` has an explicit capacity
- we test that `z = n` closes
- and that `z < n` does not close

This line should not be read as the final architecture itself.
It should be read as an experimental validation of the capacity contract of the targeted architecture.

Strict spec of the witness:

- `cap(z) = k`
- compare `k = n` and `k < n`

Strict operationality:

- explicitly vary the mediator capacity
- then measure closure or non-closure of the contract

Attestation:

- `k = n` must close
- `k < n` must not close
- the difference must be stable under verification

## 5. What the tests really validate

The project tests are not meant to audit market models.

They are meant to validate that the proposed architecture satisfies its contract.

The tests verify:

- that there exists a structural barrier on the visible
- that an internal mediation restores the decision
- that this mediation has a measurable minimal capacity
- that the decision follows the mediator causally
- and, in query-type protocols, that internal state drives an action that then reconfigures what is observed or decided
- and that this structure remains stable when varying size, task families, and solver classes

In other words:

- the tests are not primarily for comparison
- they are primarily to establish that the architecture is the right one

Validation spec:

- `B0` = barrier on the visible
- `M0` = restoration by mediation
- `C0` = measurable minimal capacity
- `K0` = causal load of the mediator
- `R0` = autoreflexive loop when the protocol contains a query
- `U0` = stability of these properties when varying regimes and solvers

Operationality:

- `B0` is measured by failure of visible-only
- `M0` is measured by success of the mediated system
- `C0` is measured by explicitly varying `cap(z)`
- `K0` is measured by `base / ablation / swap`
- `R0` is measured by the chain `m -> a -> r -> y`
- `U0` is measured by repetition across families, sizes, and solver classes

## 6. Role of universality

Universality is not a final embellishment.
It is used to show that the observed properties are not local benchmark accidents.

If the program succeeds, we do not obtain only an empirical law.
We obtain a validated architecture.

Universality must show that:

- mediation is not a local hack
- minimal capacity is not an artifact of a single world
- causal gates are not a protocol curiosity
- the contract holds across multiple regimes

So the targeted result is:

- a different Transformer architecture
- defined not by its size, but by its mediation contract

Universality validation spec:

- either a family of tasks `F`
- or a family of sizes `N`
- or a family of solvers `S`
- the contract is said stable if `B0`, `M0`, `C0`, `K0` and, when applicable, `R0`, remain true across `F`, `N`, `S`

Operationality:

- universality does not build a new block
- it tests stability of already stated specs
- it therefore serves as external validation of the architectural contract

## 7. Final direction of the architecture

The final direction of the project can be formulated as:

- a Transformer should no longer be understood only as a function approximator on an interface
- it should be understood as an autoreferential system of explicit internal mediation
- this mediation must be minimal, readable, non-trivial, and testable

In a richer extension, already announced in some design notes, this architecture can become autoreflexive:

- the system carries multiple local mediators
- it can build coupling mediators
- and it can choose which interface or which quotient to query next from its internal state before the final decision

This extension does not replace the core of the project.
It is its natural continuation.

Minimal target spec for construction:

- `InterfaceEncoder_i : X_i -> T_i`
- `MediatorCore : (T_1, ..., T_k, m_prev) -> m`
- `DecisionHead : m -> y`
- `CausalAuditHooks : m -> (ablation, swap)`

Autoreflexive extension:

- `QueryPolicy : m -> a`
- `EnvironmentAdapter : a -> r`
- `StateUpdate : (m, r) -> m'`
- `DecisionHeadReflexive : m' -> y`

Construction meaning:

- the minimal autoreferential version builds `m` then decides
- the autoreflexive version builds `m`, acts via `a`, receives `r`, updates into `m'`, then decides

## 8. Short formula

The new Transformer architecture targeted by the project is an explicit mediation architecture:

- obstruction on the visible
- internal mediator with finite capacity
- autoreferential decision regime
- decision head dependent on this mediator
- causal test of the mediator load
- possible extension toward an autoreflexive regime
- validation of the stability of this contract by universality

On the autoreflexive line already present in the tests, this contract becomes:

- internal state
- action or query chosen from this state
- new observation produced by this action
- final decision under reconfigured access

Construction formulas:

- minimal autoreferential: `v -> z -> y`
- autoreflexive: `x -> m -> a -> r -> m' -> y`

## 9. Status of this document

This document is a working specification.

It states what the architecture must be in the sense of the project.
It does not claim that every final implementation detail is already frozen into a single file in the repository.

What is already fixed, however, is the structural contract that this architecture must satisfy.

## 10. What this document does not claim

This document does not claim to:

- exhaustively enumerate all Transformer variants or existing systems
- propose an absolute taxonomy of architectures in general

This document aims at:

- stratifying admissible regimes relative to a referential frame (interface and dynamic truth)
- a testable specification of the autoreferential and autoreflexive regimes in the operational sense of the repository
