# Transformers in the COFRS sense: visible-only vs mediated (and why this is a rupture)

This note is written for readers who already know what a Transformer is, but who have not yet mapped that object onto the COFRS formal spine (obstruction → minimal mediation → intervention signature).

The goal is not to re-label existing ideas. The goal is to make a precise distinction:

- “visible-only” is a *formal regime* (a closure claim at an interface),
- diagonal obstruction is a *structural certificate* that this regime cannot work,
- the repair is a *minimal finite mediator* (not “more capacity” in the usual sense),
- and the mediator becomes *operationally auditable* via intervention-style gates.

## 1) What “visible-only” means here (it is not a statistical claim)

In COFRS, a “visible-only decision regime” is captured by `ObsPredictsStep`:

- you have an observable interface `obs : S → V`,
- you have a dynamic truth to decide, expressed via `Compatible sem obs target_obs step x`,
- and `ObsPredictsStep` means: there exists a decision rule that depends only on `V` and is correct for that dynamic truth.

This is not phrased in probabilistic language (no Pearson correlation, no mutual information). It is a structural claim: “the interface value `V` is sufficient to close the decision”.

When COFRS proves `¬ ObsPredictsStep`, it is proving: **no rule that depends only on what is visible at the interface can be correct everywhere on the relevant fiber**.

## 2) Why standard Transformers are “visible-only” in this sense

A standard Transformer (as used in typical LLM inference) is a map from a visible input to an output:

- input: tokens (plus any visible context like retrieved text, if provided),
- output: next-token distribution or a decoded string,
- internal activations exist, but there is no *separately modeled* mediator whose semantics are constrained and audited as part of the specification.

In the COFRS reading, this places the model in a visible-only regime relative to the chosen interface:

- if `obs` is “the visible prompt/context at the decision time”, then the model’s decision is a function of `obs x`,
- so it is attempting to behave as an `obs`-only predictor for whatever dynamic truth the task really requires.

This is exactly the regime COFRS attacks: if the dynamic truth varies inside a single `obs`-fiber, then any visible-only rule is provably doomed.

## 3) The obstruction is not “capacity”: it is intra-fiber separation

The key certificate is a diagonal witness (`LagEvent`) that produces a separation inside a fiber:

- two distinct states are indistinguishable at the interface (same visible value),
- but the dynamic truth differs (future compatibility differs along a chosen `step`).

Formally, the development derives `LagEvent → ¬ ObsPredictsStep` in `COFRS/Dynamics.lean` (`PrimitiveHolonomy.not_obsPredictsStep_of_lagEvent`).

Interpretation for ML: this is a rigorous “no amount of clever visible-only decoding can close the decision”, because the task’s truth is not a function of the visible interface on the relevant domain.

This is why the phenomenon is not “just correlation failure”. It is a *closure failure* certified by a witness.

## 4) The repair is a minimal finite mediator (and it is canonical)

COFRS does not stop at impossibility. It quantifies exactly how much additional information is required to repair the decision, via compatibility dimension:

- `CompatDimLe … n` / `CompatDimEq … n` measures the minimal finite capacity needed to decide the dynamic truth correctly.

Then it turns that measurement into an explicit mediator construction, via the central equivalence:

- `CompatDimLe … n ↔ RefiningLift … n`,
- with witnesses `RefiningLiftData` / `RefiningLift`,

all in `COFRS/Dynamics.lean` (see `PrimitiveHolonomy.compatDimLe_iff_refiningLift`).

Operationally, the mediator is a finite supplement `Fin n` on the observable fiber. The “extra term” is not vague: it is a minimal-capacity supplement with a proof obligation.

This is the first rupture from the usual Transformer story:

- standard practice scales parameters and hopes the representation “implicitly” contains what is needed,
- COFRS forces you to *name* the missing information as a finite mediator and prove that it is necessary and sufficient in the formal sense.

## 5) The mediator is not only sufficient: it becomes auditable (causal gates)

COFRS pushes one step further: the mediator is not treated as a mere factorization artifact.

In the binary case, the development packages an intervention-style audit (`CausalSignature2`) and proves it from:

- a separating step on the fiber,
- plus the existence of a finite lift of size `2`.

See `COFRS/Examples/DiagonalizationMediationCausalityThesis.lean` (notably `causalSignature2_of_stepSeparatesFiber_of_refiningLift2` and the end-to-end derivations).

Interpretation for ML: if a model claims to have repaired the visible-only failure by introducing a mediator, then you can test whether that mediator is load-bearing via:

- ablation: collapsing the mediator breaks correctness,
- swap/permutation: exchanging mediator classes makes the decision follow the mediator rather than the original instance.

This is the second rupture:

- the architecture is not only “bigger” or “with memory”;
- it comes with a *falsifiable audit* that distinguishes genuine mediation from shortcut behavior.

## 6) The “two independences → irreducible relation” pattern (what is new in the method)

Many frameworks talk about combining two sources. COFRS focuses on a stronger shape:

- each margin is insufficient (each interface is non-closing for the dynamic truth),
- the repair requires a third term (a mediator) that is not reconstructible from either margin alone,
- and this irreducibility can be proved (and, in the binary case, audited interventionally).

This is the “relation as an object” viewpoint:

- the missing content is not contained in either margin;
- it lives in the forced factorization through an additional term.

In Lean, this appears as “joint truth + marginal no-go + minimal joint lift”, and (in the strengthened form) as non-descend statements for the mediator itself (not only non-predictability of the truth from each margin).

This is the third rupture:

- the previous view is static (“look at a margin, decide from it”),
- the COFRS view is structural (“if the truth varies inside the fiber, the margin cannot close; the repair is a minimal mediator; the mediator is irreducible and auditable”).

## 7) What this implies for “hallucination” as a technical notion (within scope)

In this repository, “hallucination” should be read in a disciplined way:

- a model outputs a confident decision from the visible interface,
- but the dynamic truth it is supposed to decide is not closed by that interface,
- so there must exist cases where any visible-only policy fails.

The remedy, within this scope, is not “train harder”. It is:

- certify the non-closure (diagonal obstruction),
- quantify the missing information (minimal `Fin n`),
- build/force a mediator that carries it (refining lift),
- audit that the decision genuinely depends on it (causal signature).

This is not a claim about all possible LLM errors. It is a claim about a specific, formal class of failures: closure failures at a chosen interface for a chosen dynamic truth.

## 8) Where to look in the repo

- Formal obstruction and no-go: `COFRS/Dynamics.lean` (`LagEvent → ¬ ObsPredictsStep`).
- Minimal mediation and canonical lift: `COFRS/Dynamics.lean` (`CompatDim*` and `CompatDimLe ↔ RefiningLift`).
- Intervention signature (binary): `COFRS/Examples/DiagonalizationMediationCausalityThesis.lean` (`CausalSignature2`).
- Concrete diagonal instance: `COFRS/Examples/GodelByCode.lean` (a fully internal witness).
- Parametric dimension story: `COFRS/Examples/DynamicCompatDimN.lean` (scalable, `n`-ary perspective).

## 9) Bottom line (the precise rupture statement)

The rupture is not “Transformers are bad” and it is not “we added memory”.

The rupture is:

- *standard inference is a visible-only closure attempt at the chosen interface*,
- *diagonal obstruction gives a constructive, checkable certificate that this regime must fail on the targeted dynamic truth*,
- *the repair is a minimal finite mediator with an exact capacity statement (`Fin n`)*,
- *and the mediator can be made operationally auditable via intervention-style gates*.

That combination (obstruction certificate + minimal mediator + auditable causal signature) is what this repository is built to make checkable.

