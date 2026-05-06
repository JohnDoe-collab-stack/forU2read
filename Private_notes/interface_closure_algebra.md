# Minimal access coalitions — interface closure algebra

Status: autonomous definition document.

Object: formalize a general algebra of informational access through interfaces, based on required
distinctions, interface losses, loss incidence, common residual, closure, irreducibility, and minimal
mediation.

## 1. Primitive data

Fix:

```text
X       : finite set of states
σ : X → Y : target, signature, or truth to decide
J       : finite set of interfaces
```

An interface `j ∈ J` is modeled by an observation:

```text
obs_j : X → V_j
```

Two states `x,y ∈ X` are confused by interface `j` when:

```text
obs_j(x) = obs_j(y).
```

The target `σ` distinguishes `x` and `y` when:

```text
σ(x) ≠ σ(y).
```

The theory does not start with scores. It starts with distinctions.

## 2. Required distinctions

The distinction space is:

```text
ΔX := {{x,y} | x,y ∈ X, x ≠ y}.
```

The distinctions required by the target are:

```text
R_σ := {{x,y} ∈ ΔX | σ(x) ≠ σ(y)}.
```

`R_σ` is the relevant domain of decision. An interface does not need to separate all distinctions in
`ΔX`; it must separate the distinctions required by `σ`.

The relevant total is:

```text
r_σ := #R_σ.
```

## 3. Losses of an interface

For an interface `j`, the loss relative to `σ` is:

```text
L_j := {{x,y} ∈ R_σ | obs_j(x) = obs_j(y)}.
```

Thus:

```text
L_j ⊆ R_σ.
```

Reading:

```text
d ∈ L_j
```

means that the required distinction `d` is invisible from interface `j`.

The accessibility of `j` is the relative complement:

```text
Acc_j := R_σ \ L_j.
```

Thus:

```text
d ∈ Acc_j
```

means that interface `j` separates the required distinction `d`.

## 4. Joint view

For a subfamily of interfaces `I ⊆ J`, the joint view identifies two states when all interfaces in `I`
identify them:

```text
x ≡_I y
⇔
∀ j ∈ I, obs_j(x) = obs_j(y).
```

The joint loss of `I` is therefore:

```text
Res(I) := {{x,y} ∈ R_σ | ∀ j ∈ I, obs_j(x) = obs_j(y)}.
```

In terms of marginal losses:

```text
Res(I) = ⋂_{j∈I} L_j.
```

Convention for the empty family:

```text
Res(∅) := R_σ.
```

This convention means that without any interface no required distinction is covered.

For heterogeneous interface values, the joint observation has dependent product type:

```text
Joint_I : X → Π_{j∈I} V_j
Joint_I(x) := (obs_j(x))_{j∈I}.
```

In the homogeneous case `V_j = V`, this reduces to:

```text
Joint_I : X → I → V.
```

## 5. Closure

A subfamily `I` closes the target `σ` if the target is determined by the joint view of `I`.

Functional form:

```text
Closed(I,σ)
⇔
∃ pred : (Π_{j∈I} V_j) → Y,
  ∀ x ∈ X,
    σ(x) = pred(Joint_I(x)).
```

For a propositional target `φ : X → Prop`, the corresponding form is:

```text
Closed(I,φ)
⇔
∃ pred : (Π_{j∈I} V_j) → Prop,
  ∀ x ∈ X,
    φ(x) ↔ pred(Joint_I(x)).
```

Fiber form:

```text
Closed(I,σ)
⇔
∀ x,y ∈ X,
  (∀ j ∈ I, obs_j(x) = obs_j(y)) → σ(x) = σ(y).
```

Residual form:

```text
Closed(I,σ)
⇔
Res(I) = ∅.
```

Numerical form:

```text
ρ(I) := #Res(I)
```

Then:

```text
Closed(I,σ) ⇔ ρ(I) = 0.
```

## 6. Loss incidence

The scalar `ρ(I)` does not contain the whole structure. It only indicates how many distinctions remain
lost by the whole family `I`.

The complete object is incidence:

```text
Inc_σ : R_σ → 𝒫(J)
Inc_σ(d) := { j ∈ J | d ∈ L_j }.
```

For a required distinction `d`:

```text
Inc_σ(d)
```

is the set of interfaces that lose `d`.

Dually, one may use the intersection table:

```text
W(U) := ⋂_{j∈U} L_j
```

for every subfamily `U ⊆ J`.

The quantity `ρ(U)` is then:

```text
ρ(U) = #W(U).
```

The scalar `ρ` is a projection of incidence. Incidence is the structural object.

## 7. Monotonicity

If `I ⊆ K`, then adding interfaces cannot increase the residual:

```text
Res(K) ⊆ Res(I).
```

Therefore:

```text
ρ(K) ≤ ρ(I).
```

Closure is monotone:

```text
Closed(I,σ) and I ⊆ K
⇒
Closed(K,σ).
```

## 8. Marginal gain

The marginal gain of interface `j` after subfamily `I` is:

```text
δ(I,j) := ρ(I) - ρ(I ∪ {j}).
```

Since:

```text
Res(I ∪ {j}) = Res(I) ∩ L_j,
```

one obtains:

```text
δ(I,j) = #(Res(I) \ L_j).
```

Reading:

```text
δ(I,j)
```

counts the distinctions still residual after `I` that `j` separates.

An interface is useful relative to `I` if:

```text
δ(I,j) > 0.
```

It is redundant relative to `I` if:

```text
δ(I,j) = 0.
```

Equivalently:

```text
j useful relative to I
⇔
Res(I ∪ {j}) ⊂ Res(I).
```

```text
j redundant relative to I
⇔
Res(I ∪ {j}) = Res(I).
```

## 9. Irreducible closure

A subfamily `I` is an irreducible closure of `σ` if it closes `σ` and no strict subfamily closes `σ`.

Definition:

```text
IrreducibleClosed(I,σ)
⇔
Closed(I,σ)
and
∀ K ⊂ I, not Closed(K,σ).
```

Residual form:

```text
IrreducibleClosed(I,σ)
⇔
Res(I) = ∅
and
∀ K ⊂ I, Res(K) ≠ ∅.
```

Numerical form:

```text
IrreducibleClosed(I,σ)
⇔
ρ(I) = 0
and
∀ K ⊂ I, ρ(K) > 0.
```

An irreducible closure is a minimal access coalition.

## 10. Essentiality and redundancy in a closing coalition

Let `I` be a subfamily such that:

```text
Closed(I,σ).
```

An interface `j ∈ I` is essential in `I` if removing it destroys closure:

```text
Essential(j,I)
⇔
Res(I \ {j}) ≠ ∅.
```

Numerical form:

```text
Essential(j,I)
⇔
ρ(I \ {j}) > 0.
```

An interface `j ∈ I` is redundant in `I` if removing it preserves closure:

```text
Redundant(j,I)
⇔
Res(I \ {j}) = ∅.
```

Numerical form:

```text
Redundant(j,I)
⇔
ρ(I \ {j}) = 0.
```

In an irreducible closure, every interface is essential.

## 11. Direct closure and mediated closure

Two regimes must be distinguished.

### Direct closure

The subfamily `I` directly closes `σ` when:

```text
Res(I) = ∅.
```

In this case, no additional information is required to decide `σ` from `I`.

### Mediated closure

The subfamily `I` does not directly close `σ` when:

```text
Res(I) ≠ ∅.
```

Finite mediation adds an extra observation:

```text
M : X → Fin n.
```

Equivalently, one may name the mediated family:

```text
I_M := I ∪ {M}.
```

This notation is formal shorthand only: `M` is not one of the original interfaces in `J`; it is an added
finite readout with value type `Fin n`.

The mediated joint observation is:

```text
Joint_{I,M} : X → (Π_{j∈I} V_j) × Fin n
Joint_{I,M}(x) := (Joint_I(x), M(x)).
```

The mediated family closes `σ` when there is a decision rule:

```text
Closed(I_M,σ) := Closed_M(I,M,σ)

Closed_M(I,M,σ)
⇔
∃ pred : ((Π_{j∈I} V_j) × Fin n) → Y,
  ∀ x ∈ X,
    σ(x) = pred(Joint_{I,M}(x)).
```

The mediator is minimal if:

```text
∃ M_n : X → Fin n, Closed_M(I,M_n,σ)
and
∀ m < n, ∀ M_m : X → Fin m, not Closed_M(I,M_m,σ).
```

Thus:

```text
direct closure  : Res(I) = ∅
mediated closure: Res(I) ≠ ∅, then Closed(I_{M_n},σ) with n minimal
```

## 12. Mediator non-descent

A mediator `M` descends to a subfamily `K ⊆ I` if its value is already determined by the joint interface
of `K`.

Definition:

```text
Descends(M,K)
⇔
∃ f : (Π_{j∈K} V_j) → Fin n,
  ∀ x ∈ X,
    M(x) = f(Joint_K(x)).
```

A mediator is irreducible relative to `I` if it descends to no strict subfamily:

```text
IrreducibleMediator(M,I)
⇔
∀ K ⊂ I, not Descends(M,K).
```

Non-descent means that the mediator is not disguised marginal information. It genuinely depends on the
access coalition.

## 13. Blackbox form

A blackbox is not opaque absolutely. It is opaque relative to a family of interfaces.

For a target `σ`, opacity relative to `I` is:

```text
Opaque(I,σ) ⇔ Res(I) ≠ ∅.
```

The blackbox is closed relative to `I` when:

```text
Closed(I,σ) ⇔ Res(I) = ∅.
```

The minimal explanation of a target decision is then:

```text
a subfamily I such that
Res(I) = ∅
and
∀ K ⊂ I, Res(K) ≠ ∅.
```

In the mediated regime, the minimal explanation is:

```text
a subfamily I
a finite mediator M_n
a proof that Joint_{I,M_n} closes
a proof that m<n fails
a proof that M_n descends to no relevant strict subfamily
```

## 14. Interface proof schema

A global problem can be approached by interfaces when the target `σ` admits an access decomposition:

```text
R_σ = required distinctions
L_j = interface losses
Res(I) = common losses
```

An interface proof follows the schema:

```text
1. define the interfaces;
2. identify the losses L_j;
3. compute the incidence of losses;
4. show that certain marginals do not close;
5. show that a coalition contracts the residual;
6. handle the remaining residual;
7. establish closure;
8. prove irreducibility or minimality.
```

This schema does not depend on the particular nature of `X`. It depends on the existence of:

```text
a target σ
partial interfaces
a space of required distinctions
a notion of loss by interface
a closure criterion
```

## 15. Complete finite example: XOR

Let:

```text
X = {00, 01, 10, 11}
σ(x) = xor(x)
```

The required distinctions are the unordered pairs with different XOR value:

```text
R_σ = {00|01, 00|10, 01|11, 10|11}
r_σ = 4.
```

Define two interfaces:

```text
A(x) = first bit of x
B(x) = second bit of x.
```

Losses:

```text
L_A = {00|01, 10|11}
L_B = {00|10, 01|11}.
```

Each marginal fails:

```text
Res({A}) = L_A ≠ ∅
Res({B}) = L_B ≠ ∅.
```

The joint residual is:

```text
Res({A,B})
= L_A ∩ L_B
= ∅.
```

Therefore:

```text
Closed({A,B},σ)
ρ({A,B}) = 0.
```

The closure is irreducible:

```text
ρ({A}) = 2 > 0
ρ({B}) = 2 > 0
ρ({A,B}) = 0.
```

Thus `{A,B}` is a minimal access coalition for `σ`.

The marginal gains are:

```text
δ(∅,A) = ρ(∅) - ρ({A}) = 4 - 2 = 2
δ(∅,B) = ρ(∅) - ρ({B}) = 4 - 2 = 2
δ({A},B) = ρ({A}) - ρ({A,B}) = 2 - 0 = 2
δ({B},A) = ρ({B}) - ρ({A,B}) = 2 - 0 = 2.
```

Mediated reading:

```text
I = {A}
M = B : X → Fin 2.
I_M = {A} ∪ {M}.
```

Then:

```text
Joint_{I,M}(x) = (A(x), B(x))
```

closes `σ`. A mediator of size `1` is constant, so `Joint_{I,M_1}` carries no more information than `A`
alone. Since `A` does not close `σ`, no `Fin 1` mediator closes over `{A}`.

Thus, in this presentation:

```text
M = B
```

is a finite mediator of minimal size `2`, equivalently one bit of additional access.

## 16. Formal summary

Objects:

```text
X, σ, R_σ, J, (L_j)_{j∈J}
```

Residual:

```text
Res(I) = ⋂_{j∈I} L_j
Res(∅) = R_σ
```

Closure:

```text
Closed(I,σ) ⇔ Res(I)=∅
```

Numerical projection:

```text
ρ(I)=#Res(I)
Closed(I,σ) ⇔ ρ(I)=0
```

Gain:

```text
δ(I,j)=ρ(I)-ρ(I∪{j})=#(Res(I)\L_j)
```

Irreducibility:

```text
IrreducibleClosed(I,σ)
⇔
ρ(I)=0 and ∀K⊂I, ρ(K)>0
```

Mediation:

```text
I does not directly close
Joint_{I,M_n} closes
∀m<n, Joint_{I,M_m} fails
M_n does not descend to a strict subfamily
```

Condensed formula:

```text
informational access
=
incidence of losses
+ residual contraction
+ closure
+ minimality
```
