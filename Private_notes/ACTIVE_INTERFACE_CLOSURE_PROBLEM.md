# Dynamic non-descent theory and the active interface closure problem

This note states the scientific framing of the project.

The theory is:

> **dynamic non-descent theory**

or, more fully:

> **a finite constructive theory of dynamic non-descent by minimal active
> mediation**

The central operational problem introduced by this theory is:

> **the active interface closure problem**

The name of the theory must not be confused with the name of the operational
problem. "Active interface closure" is the problem that dynamic non-descent
theory isolates and solves in a finite constructive setting.

The short version is:

> Dynamic non-descent theory introduces and solves a finite constructive form of
> the **active interface closure problem**: when a target truth does not descend
> to the currently observable interface in a presented finite instance class,
> certify the obstruction and construct the minimal admissible active
> mediator/query extension that makes the truth decidable.

In French:

> La theorie de la non-descente dynamique introduit et resout une forme
> finitaire constructive du **probleme de fermeture active d'une interface
> partielle** : lorsqu'une verite cible ne descend pas a l'interface observable
> courante dans une classe finie presentee, certifier l'obstruction et construire
> le mediateur actif admissible minimal, ou l'extension de requete admissible
> minimale, qui rend cette verite decidable.

## 0) Naming hierarchy

Use the following hierarchy:

```text
theory:
  dynamic non-descent theory

central problem:
  active interface closure problem

solution mechanism:
  minimal admissible active mediator/query extension

ML/world-model realization:
  active recovery architecture for missing non-descended information

certificates:
  marginal no-go, diagonal obstruction, ablation, swap, under-capacity collision
```

In French:

```text
theorie:
  theorie de la non-descente dynamique

probleme central:
  probleme de fermeture active d'une interface partielle

mecanisme de resolution:
  mediateur actif admissible minimal / extension de requete admissible minimale

realisation ML / world model:
  architecture de recuperation active de l'information non descendue

certificats:
  no-go marginal, obstruction diagonale, ablation, swap, collision de sous-capacite
```

## 1) Why the problem must be named first

The exact problem name "active interface closure" is not a standard label in the
literature.

What already exists is a dispersed family of problems:

- **identifiability**: can the hidden cause or target be recovered from the
  observable data?
- **factorization through a quotient**: is a predicate well-defined on the
  observable quotient?
- **sufficient statistics**: what summary preserves all information needed for
  a target inference?
- **POMDP belief state**: what internal state is sufficient for action under
  partial observability?
- **active sensing / information gathering**: which action should be taken to
  acquire the missing information?
- **dynamic epistemic logic**: how informational actions change what is known?
- **descent / local-to-global repair**: when can local data descend, and when is
  additional gluing or extension data required?

The move of dynamic non-descent theory is to put these fragments under one
finite, constructive and intervention-testable problem.

## 2) Mathematical core

Given:

```text
X          state space
q : X -> Q observable interface / quotient
T : X -> Prop target truth
A_n        class of admissible mediators X -> Fin n
E          class of admissible query extensions
```

The first question is closure:

```text
Does T factor through q?

Exists d : Q -> Prop such that, for all x,
  T x = d (q x)
```

Equivalently, `T` is closed on the interface if every fiber of `q` is
`T`-constant:

```text
q x = q y  =>  T x = T y
```

Non-closure is witnessed constructively by a diagonal/fiber obstruction:

```text
Exists x y,
  q x = q y
  and T x != T y
```

This witness proves that no decision rule reading only the current interface
can decide `T` on that fiber.

There are two levels:

```text
global theorem:
  T factors through q iff T is constant on q-fibers

local procedure:
  in a presented finite instance/fiber, certify a fiber obstruction and repair
  the access by an admissible mediator or query extension
```

The global statement is a quotient/fiber criterion. The local solver is the
constructive procedure that acts on the current instance or finite witness
family.

## 3) The active repair problem

Once closure fails, the scientific problem is not merely to say "more
information is needed".

The problem is to construct the smallest admissible extension of access that
repairs the decision.

The word **admissible** is essential. Without an admissibility constraint, an
arbitrary mediator could simply encode the target truth `T`, making the
minimality claim trivial or ill-posed. Minimality is always relative to the
allowed interfaces, allowed mediator channels and allowed query extensions of
the architecture:

```text
A_n = admissible mediators X -> Fin n
E   = admissible query extensions

minimal means minimal over A_n or E,
not over all arbitrary encodings.
```

There are two equivalent operational forms.

### 3.1 Mediated closure

Construct an admissible finite mediator:

```text
z : X -> Fin n
```

such that `T` factors through the refined interface:

```text
(q, z) : X -> Q x Fin n
```

and `n` is minimal among admissible mediators:

```text
Fin n suffices,
but no admissible Fin m with m < n suffices.
```

### 3.2 Active closure

Construct an admissible active query/read loop:

```text
preState = Encode(q)
action   = Query(preState)
response = Env(action)
post     = Update(preState, response)
answer   = Decide(post)
```

The active version is stronger than passive mediation when the missing
information is not present in the current interface and must be made accessible
by choosing an action.

## 4) Final problem statement

The central problem solved by dynamic non-descent theory can be stated as:

> **Active interface closure problem.** Given a partial observable interface and
> a target truth in a presented finite instance class, test or certify whether
> the target already descends to the current interface. If it does not, certify a
> fiber obstruction and construct a minimal admissible active mediator/query
> extension that retrieves the missing information and makes the target
> decidable and intervention-stable.

This is not "solve all POMDPs".
This is not "solve all identifiability".
This is not "solve the black-hole information problem".

It is the finite constructive core common to these situations:

```text
partial interface
-> target truth not closed on that interface
-> obstruction inside an observable fiber
-> minimal admissible mediator or active query extension
-> stable decision after access repair
```

## 5) What dynamic non-descent theory adds beyond known names

The known theories contain parts of the picture.

Dynamic non-descent theory adds the following conjunction:

1. **Interface closure as the decision criterion**
   - the target is not "predicted well";
   - it either factors through the current interface or it does not;
   - in the finite presented class, this descent is tested or certified by
     fiber constancy.

2. **Constructive obstruction**
   - failure is not statistical handwaving;
   - it is witnessed by two states in the same observable fiber with different
     target truth.

3. **Finite minimal admissible mediator**
   - the repair has a capacity `n`;
   - smaller admissible mediators force collisions and cannot preserve the
     decision.

4. **Active access**
   - when passive observation does not suffice, the mediator can choose a query
     or read action that changes what becomes accessible.

5. **Intervention audit**
   - ablation of the mediator must break the decision;
   - swapping the mediator must move the decision;
   - under-capacity must produce collision witnesses.

That combination is the actual contribution.

## 6) Relation to established terminology

### Identifiability

In statistics and inverse problems, non-identifiability means that different
hidden explanations can generate the same observables.

Dynamic non-descent closure failure is the target-relative version:

```text
same observable interface
different target truth
```

The project is stricter because it asks for a constructive witness and for a
minimal repair.

Reference anchor:
- Encyclopedia.com, "Statistical Identifiability":
  https://www.encyclopedia.com/social-sciences/applied-and-social-sciences-magazines/statistical-identifiability

### Sufficient statistic

A sufficient statistic preserves all information relevant to a parameter or
target.

The mediator of dynamic non-descent theory is a finite sufficient interface
extension for a target truth, relative to an admissible class of channels. The
minimality condition is the analogue of minimal sufficient structure, but with
constructive finite lower bounds and intervention tests.

Reference anchor:
- Sufficient statistic:
  https://en.wikipedia.org/wiki/Sufficient_statistic

### POMDP belief state

In a POMDP, the belief state is a sufficient state for decision under partial
observability.

Dynamic non-descent theory does not attempt to solve arbitrary POMDP planning.
It isolates a finite closure problem inside partial observability: when is the
current interface sufficient, and what active mediator/query is needed when it
is not?

Reference anchor:
- Kaelbling, Littman, Cassandra, "Planning and acting in partially observable
  stochastic domains":
  https://people.csail.mit.edu/lpk/papers/aij98-pomdp.pdf

### Active sensing

Active sensing chooses actions to obtain more informative observations.

The active mediator is not merely an information-gathering heuristic. It is
audited as load-bearing: the returned information must be necessary for the
target decision, and the mediator choosing the query must be causally charged.

Reference anchor:
- "Task-Oriented Active Sensing via Action Entropy Minimization":
  https://pmc.ncbi.nlm.nih.gov/articles/PMC6857841/

### Dynamic epistemic logic

Dynamic epistemic logic studies changes in information states caused by actions.

Dynamic non-descent theory uses the same broad idea, but in a constructive
solver architecture:
an internal state chooses an action, the action changes access, and the final
decision is read only after the update.

Reference anchor:
- Stanford Encyclopedia, "Dynamic Epistemic Logic":
  https://plato.stanford.edu/archives/sum2019/entries/dynamic-epistemic/

### Descent and quotient factorization

The mathematical phrase "the truth descends to the interface" means that it is
well-defined on the quotient induced by the interface.

Dynamic non-descent is the target-relative failure of such descent: the
interface quotient identifies states that the target truth must separate.

Reference anchors:
- nLab, "descent":
  https://ncatlab.org/nlab/show/descent
- nLab, "quotient object":
  https://ncatlab.org/nlab/show/quotient+object

## 7) Where this lives in the project

Lean layer:

- `COFRS/Examples/ReferentialInduction.lean`
  - `ReferentialProblem`
  - `Closes`
  - `DiagonalWitness`
  - `InductionStep`

- `COFRS/Dynamics.lean`
  - `CompatibleFuture`
  - `Sig`
  - `SigFactorsThrough`
  - `CompatSigDimLe`
  - `CompatSigDimEq`
  - `StepSeparatesFiber`

- `COFRS/Examples/IndependenceRelationMediationChain.lean`
  - two marginal interfaces;
  - joint fiber separation;
  - finite admissible mediator;
  - non-descent of the mediator to either margin;
  - optional causal signature.

- `COFRS/Examples/DynamicCompatDimN.lean`
  - parametric finite witness family;
  - non-vacuity of the exact finite mediator hypothesis.

Architecture/empirical layer:

- `Private_notes/NOUVELLE_ARCHITECTURE_TRANSFORMER.md`
  - `m -> a -> r -> m' -> y`;
  - internal state chooses access;
  - decision after returned context.

- `Empirical/aslmt/v20_algebra_v3b_unified_v2_strong_qforced_zread_policy_nontrivial_proofpack_v6/`
  - marginal no-go certificates;
  - structural verifier;
  - trained baseline controls;
  - ablation and swap;
  - minproof collision witnesses.

Page/black-hole reading:

- `Private_notes/PAGE_AS_CLOSURE_REGIME.md`
  - Page time as interface-relative closure transition.

- `Private_notes/DICTIONARY_CLOSURE_LAYER.md`
  - holographic dictionary as a problem of decidability by interface.

## 8) What counts as solved

The solved object is:

> a finite constructive active-interface closure problem with explicit
> obstruction, finite minimal admissible repair and intervention audit.

It is solved when the following are present:

1. **No-go**
   - same interface value;
   - different target truth.

2. **Repair**
   - mediator/query extension makes the target decidable.

3. **Minimality**
   - a finite admissible mediator of size `n` suffices;
   - any strictly smaller admissible finite mediator fails.

4. **Intervenability**
   - ablation breaks;
   - swap follows;
   - baselines constrained to the old interface fail.

5. **Traceability**
   - the proof object or experiment emits concrete witnesses;
   - the verifier independently re-runs the checks.

## 9) What is not claimed

This does not claim:

- a complete solution of all partial-observability problems;
- a general POMDP solver;
- a universal theory of all identifiability;
- a solution of quantum gravity or the black-hole information paradox;
- that every physical mediator is automatically a `CompatDimEq` mediator.

It claims:

> a rigorous finite constructive solution to the active closure problem for
> partial interfaces, with a formal spine and empirical witness families.

## 10) Announcement forms

### Technical

> We develop a finite constructive theory of dynamic non-descent. Its central
> operational problem is active interface closure: given an observable quotient
> and a target truth in a presented finite instance class, test or certify
> whether the truth descends to the current interface; if not, certify a fiber
> obstruction and construct the minimal admissible active mediator/query
> extension that makes the truth decidable and
> intervention-stable.

### Robust claim

> Dynamic non-descent theory introduces and solves a finite constructive
> **active interface closure** problem for an admissible class of partial
> interfaces and active query mediators: target descent is tested by fiber
> constancy in the presented finite class; failure is certified by a diagonal
> obstruction; repair is achieved by a minimal admissible mediator/query
> extension; and the repaired decision is audited by ablation, swap and
> under-capacity collision witnesses.

### ML-facing

> The architecture learns when the current observation is sufficient for the
> target decision. When it is not, it uses an internal mediator to choose a
> query/read action, retrieves the missing context, and decides only after this
> access repair. The mediator is audited by ablation, swap and under-capacity
> collision tests.

### Mathematical

> The result is a constructive quotient-closure theorem with active repair:
> non-factorization of a target predicate through an observable quotient yields a
> fiber obstruction; finite repair is captured by a minimal admissible mediator,
> and active repair by a query extension that changes the accessible interface.

### One sentence

> Dynamic non-descent theory solves the finite constructive problem of turning
> non-identifiability at a partial interface into stable decidability by
> constructing the minimal admissible active mediator that repairs access to the
> missing information.
