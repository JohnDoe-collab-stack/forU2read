# Predictive Latents vs Minimal Joint Mediators

## Rigorous comparison between JEPA-style world models and dynamic non-descent

## Abstract

This note compares two distinct scientific objects:

```text
JEPA / V-JEPA:
  predictive latent representation

Dynamic non-descent:
  minimal joint mediator irreducible to marginals
```

The central conclusion is:

> JEPA-style world models construct useful predictive latents. Dynamic
> non-descent constructs and certifies a minimal joint mediator: a finite joint
> object that separates a target truth where the marginals fail, supports a
> refining lift, and satisfies a lower bound against smaller mediators.

The formal theorem name in the Lean file is:

```lean
PrimitiveHolonomy.Examples.endToEnd_full
```

The binary causal extension is:

```lean
PrimitiveHolonomy.Examples.endToEnd_full_with_causalSignature2
```

## 1. Objects under comparison

### 1.1 JEPA-style object

JEPA learns a representation by predicting target embeddings from context
embeddings. I-JEPA is described as a non-generative self-supervised architecture
using masking strategies to produce semantic image representations; its core
operation is context-block to target-block representation prediction. ([Hugging
Face][1])

V-JEPA extends this line to video feature prediction. Meta describes V-JEPA as
trained solely using a feature-prediction objective over video, with no
pretrained image encoder, text, negative examples, reconstruction, or other
supervision sources. ([Meta AI][2])

V-JEPA 2 moves further toward world models: it pretrains a
joint-embedding-predictive architecture on large video/image data, then
post-trains a latent action-conditioned world model, V-JEPA 2-AC, for robot
planning. ([Meta AI][3])

So the JEPA-family object is:

```text
context observation
-> latent embedding
-> prediction of target/future latent
-> downstream use for recognition, anticipation, planning
```

### 1.2 Dynamic non-descent object

The object in the Lean file is:

```text
two marginal interfaces
-> joint interface obsAB
-> target dynamic truth
-> marginal insufficiency
-> joint separation
-> finite refining lift
-> lower bound against smaller lifts
```

The principal theorem is:

```lean
PrimitiveHolonomy.Examples.endToEnd_full
```

Its conclusion has the shape:

```lean
StepSeparatesFiber ... obsA ...
∧ StepSeparatesFiber ... obsB ...
∧ ¬ LeftObsPredictsJointStep ...
∧ ¬ RightObsPredictsJointStep ...
∧ RefiningLift ... obsAB ... n
∧ ∀ m : Nat, m < n -> ¬ RefiningLift ... obsAB ... m
```

So the dynamic non-descent object is:

```text
minimal joint mediator irreducible to either marginal
```

## 2. Strict comparison table

| Criterion | JEPA / V-JEPA | Dynamic non-descent |
| --- | --- | --- |
| Core object | latent predictive embedding | minimal joint mediator |
| Formal target | predict latent target/future | decide dynamic truth on a joint fiber |
| Input structure | context/target masking | two marginal interfaces plus joint interface |
| Marginal analysis | implicit through masking/context | explicit left/right marginal irreducibility |
| Minimality | compression/usefulness learned empirically | theorem-level lower bound: for every `m < n`, lift of size `m` fails |
| Causality/intervention | planning/action in later variants | optional `CausalSignature2` theorem for binary case |
| Certificate type | downstream performance and planning success | obstruction, refining lift, lower bound, intervention audit |
| Theorem name | no theorem matching `endToEnd_full`: no left/right marginal irreducibility, no finite `RefiningLift`, no lower-bound statement `∀ m<n` | `endToEnd_full` |

## 3. What JEPA actually gives

JEPA gives a powerful representation-learning program:

```text
learn latent structure by predicting hidden or future representations
```

For I-JEPA, the target is semantic image representation from masked context; the
published description emphasizes representation prediction rather than pixel
reconstruction. ([Hugging Face][1])

For V-JEPA, the target is video feature prediction, producing visual
representations useful across video and image tasks. ([Meta AI][2])

For V-JEPA 2, the system enters the world-model regime: understanding,
prediction, action anticipation, video QA, and robot planning via an
action-conditioned latent world model. ([Meta AI][3])

The strongest fair summary:

```text
JEPA learns predictive latent states useful for perception and planning.
```

## 4. What dynamic non-descent gives

Dynamic non-descent gives a different object:

```text
minimal joint mediator
```

The theorem `endToEnd_full` combines five elements:

```text
1. two marginal diagonal obstructions;
2. constructive separation on each marginal fiber;
3. joint separation for the dynamic truth;
4. irreducibility of joint truth to left/right marginal projections;
5. finite joint RefiningLift of size n plus lower bound for every m < n.
```

This is stricter than "a good latent representation".

It says:

```text
the joint mediator exists,
the marginals cannot predict the joint truth,
the mediator has finite size n,
and smaller finite mediators cannot refine the decision.
```

## 5. Empirical realization in ASLMT v20

The ASLMT architecture implements the same spine operationally.

The algebra says: cue reveals `h`; image leaves the hidden target unresolved;
query selects an interface `a`; response bit becomes informative exactly when
`a = policy(h)`; hence residual ambiguity over `k` contracts under the correct
interface.

The model forces the query to read the discrete mediator `z`:

```python
query_logits := f(one_hot(argmax(z_logits.detach())))
```

and the decoder receives `(image, z, res_bit)`, making `z` a discrete mediator
rather than an unconstrained continuous embedding.

The proofpack frames the empirical object as structural counterexamples along
the chain:

```text
cue -> zread(detach) -> action -> res_bit(qforced) -> target
```

and checks barriers, paired discrimination, image/cue baselines, `z`-ablation,
`z`-swap, and zero-counterexample verification.

The marginal no-go and minproof parts match the theorem's conceptual spine:
each marginal alone fails; collisions in `z` under insufficient capacity force
paired-discrimination failure because decoder inputs become identical.

## 6. Non-equivalence proposition

The comparison is not between "latents" in general.

It is between:

```text
predictive latent embeddings
vs
target-relative minimal joint mediators with formal irreducibility and lower bounds
```

### Proposition

JEPA-style predictive latents and dynamic non-descent minimal joint mediators
are formally distinct.

### Reason

JEPA learns a latent `Z` such that:

```text
Z_context predicts Z_target
```

Dynamic non-descent proves the existence and minimality of a mediator `J` such
that:

```text
J refines the joint interface obsAB,
J decides the dynamic truth,
J is irreducible to obsA alone,
J is irreducible to obsB alone,
and every smaller Fin m mediator fails.
```

In theorem form:

```lean
RefiningLift ... obsAB ... n
∧ ∀ m : Nat, m < n -> ¬ RefiningLift ... obsAB ... m
∧ ¬ LeftObsPredictsJointStep ...
∧ ¬ RightObsPredictsJointStep ...
```

Therefore:

```text
JEPA latent != minimal joint mediator
```

A JEPA latent may contain, approximate, or learn something isomorphic to such a
mediator in a suitable task. The JEPA objective itself gives predictive utility.
The dynamic non-descent theorem gives minimal joint irreducibility.

## 7. Precise relation

The relation is:

```text
JEPA:
  learns useful latent predictors

Dynamic non-descent:
  specifies when a latent deserves the stronger title "minimal joint mediator"
```

A JEPA-style system would match the dynamic non-descent object only if it also
supplied:

```text
1. explicit marginal obstruction;
2. joint separation;
3. left/right irreducibility;
4. finite mediator/lift;
5. lower bound against smaller mediators;
6. intervention audit such as ablation/swap/collision.
```

ASLMT v20 supplies this structure in the finite constructive setting through
its algebra, zread architecture, proofpack, marginal no-go, and minproof
collision witnesses.

## 8. Scientific position

JEPA and V-JEPA sit in the literature as:

```text
predictive representation learning for world models
```

Dynamic non-descent sits as:

```text
minimal joint mediation theory for partial interfaces
```

The overlap:

```text
both care about latent structure useful for prediction/action
```

The separation:

```text
JEPA optimizes predictive representation;
dynamic non-descent certifies minimal joint irreducibility.
```

## 9. Final claim

The clean comparative claim is:

> JEPA learns predictive latents for world modeling. Dynamic non-descent
> characterizes a stricter object: a target-relative minimal joint mediator,
> irreducible to either marginal, equipped with a finite refining lift and a
> lower-bound certificate against smaller mediators. The ASLMT v20
> implementation realizes this object operationally by making `z` a discrete
> mediator read by the query, then testing the chain by marginal no-go,
> ablation, swap, and collision witnesses.

The shortest version:

> JEPA learns predictive latents. Dynamic non-descent proves and audits when a
> latent is a minimal joint mediator.

[1]: https://huggingface.co/papers/2301.08243 "Paper page - Self-Supervised Learning from Images with a Joint-Embedding Predictive Architecture"
[2]: https://ai.meta.com/research/publications/revisiting-feature-prediction-for-learning-visual-representations-from-video/ "Revisiting Feature Prediction for Learning Visual Representations from Video | Research - AI at Meta"
[3]: https://ai.meta.com/research/publications/v-jepa-2-self-supervised-video-models-enable-understanding-prediction-and-planning/ "V-JEPA 2: Self-Supervised Video Models Enable Understanding, Prediction and Planning | Research - AI at Meta"
