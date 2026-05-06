# Closure by distinctions (incidence-first) — refined version

## Structural statement — what is genuinely strong

Fix:

- a target dynamic truth, i.e. what must be decided;
- one or two interfaces, or observables, `A`, `B`;
- the fiber of microstates indistinguishable through an interface;
- and a notion of “deciding from an interface” = closure/factorization: there exists a rule depending
  only on the interface value.

The intended schema is not “compute scores”, but certify three facts:

1. **Marginal no-go**: `A` alone does not close the target, and `B` alone does not close the target.
   The truth varies while the visible interface value is fixed.
2. **Composition**: the composition `A∧B` is the first level where the relevant information becomes
   either directly decidable, or localizable as a residual repairable by finite mediation.
   There are two distinct regimes:
   - **direct closure**: `A∧B` already closes the target; the truth becomes a function of the joint
     interface;
   - **mediated closure**: `A∧B` does not yet close the target; a residual remains, but there exists
     a finite mediator which, when added to the joint interface, restores the correct decision.
3. **Finite minimal mediator**: in the mediated regime, there is a finite capacity `n` sufficient for
   correct decision, and no strictly smaller capacity `m<n` can preserve the decision.

The essential point: an “orthogonality” is not a correlation. It is a **marginal closure defect** that is
resolved either by direct closure of the composition or by mediated closure, with a **minimal dimension**
in the second case.

## Role of the finite “distinction” version

The distinction calculus is an explicit finite instance which:

- makes composition effects visible through incidence: intersections and overlaps;
- avoids losing information by cardinalizing too early;
- provides operational invariants such as `ρ`, `g`, etc. in a finite model.

But quantities such as `ρ_σ(A,B)=#(L_A∩L_B)` are **coordinates** of a more general phenomenon:
closure/non-closure plus minimality of mediation. They do not replace the universal statement.

Useful landmark:

- in the **direct closure regime**, `ρ_σ(A,B)=0` is exactly the finite criterion saying that `A∧B`
  already closes the target;
- in the **mediated regime**, `ρ_σ(A,B)>0` indicates a residual of the joint view, still at the finite
  level, and the structural datum becomes the **minimal dimension** `n` of the mediator
  (COFRS spine: `CompatDimEq`).

## Alignment with the Lean / COFRS spine

In COFRS vocabulary, the structural column decomposes into separate bricks:

- **marginal no-go**: `LagEvent → ¬ ObsPredictsStep`;
- **constructive marginal separation**: given a closure failure and a finite enumeration of the fiber,
  `stepSeparatesFiber_of_not_obsPredictsStep_of_equivFin` exhibits a separation inside the fiber;
- **minimality of the joint mediator**: `CompatDimEq … n` entails `RefiningLift … n` and
  `∀ m<n, ¬ RefiningLift … m`.

The theorem
`PrimitiveHolonomy.Examples.DynamicsOnly.double_noGo_to_separation_and_minimalJointLift`
packages precisely the chain:

```text
marginal no-go (A,B) → marginal separations (A,B) → minimal joint lift (size n)
```

Separately, **separation of the joint fiber** (`StepSeparatesFiber` on `obsAB`) is a distinct hypothesis
or step. It corresponds to the mediated-closure regime: the truth still varies inside the joint fiber.
It is packaged by other statements, for example joint irreducible profiles and end-to-end versions.

---

## Appendix — finite distinction calculus

Idea: **delay cardinalization** (`ℕ`). First calculate over **distinctions**, i.e. pairs of states, and only
then apply cardinality `#`.

Arithmetic displacement:

```text
Peano cardinalizes collections.
Closure arithmetic first preserves the incidence of lost distinctions, then cardinalizes.
```

**Incidence** is the relative position of loss subsets inside `R_σ`: their overlap, disjointness,
or alignment.

Central point:

```text
joint closure depends on L_A ∩ L_B, not only on #L_A and #L_B.
```

Two slogans, dualizing losses and accessibilities:

```text
joint loss          = intersection of marginal losses
joint accessibility = union of marginal accessibilities
```

Operational reading as coverage. For a finite nonempty family of interfaces `(E_i)`:

```text
joint closure
⇔ ⋂_i L_σ(E_i) = ∅
⇔ ⋃_i Acc_σ(E_i) = R_σ.
```

Positioning: this is a coverage theory of closure over `R_σ`, where cardinalization enters only after
the incidence calculation over losses.

Formal kernel:

```text
R_σ      := required distinctions
L_A      := required distinctions lost under A
L_B      := required distinctions lost under B
ρ_σ(A,B) := #(L_A ∩ L_B)

Then:

a_{A∧B} = r_σ - ρ_σ(A,B)

Joint closure is equivalent to:

ρ_σ(A,B) = 0
```

Conjunction gain, or complementarity. Set:

```text
ℓ_A := #L_A
ℓ_B := #L_B.
```

Define:

```text
g_σ(A,B) := min(ℓ_A, ℓ_B) - ρ_σ(A,B).
```

Writing `a_A := a_σ(E_A)` and `a_B := a_σ(E_B)`, one also has:

```text
g_σ(A,B) = a_{A∧B} - max(a_A,a_B).
```

Thus `g_σ(A,B)` measures the accessibility surplus brought by `A∧B` above the best single interface.

---

## 0) Abstract signature: sorts, operations, invariants

The document defines a **derived algebra**: the computational objects are partitions and subsets of
distinctions, and numbers appear only after transporting the calculation into the space of losses.

### Canonical definition

For finite `X` and `σ : X → S`, define the closure algebra by distinctions relative to `σ` as:

```text
𝔠_σ(X)
:=
(
  Part(X), EqConf(X), 𝒫(R_σ), ℕ ;
  ≤, ∧, ∨ ; ⊆, ∩, ∪, \, # ;
  C, L_σ, Acc_σ, ρ_σ
)
```

where:

```text
C(E)      = C_E
L_σ(E)    = R_σ ∩ C_E
Acc_σ(E)  = R_σ \ L_σ(E)

ρ_σ(E₁,…,Eₙ)
  := #(⋂_{i=1}^n L_σ(E_i))

ρ_σ(A,B)
  := ρ_σ(E_A, E_B)
```

Typing note. For a strict algebraic signature, `ρ_σ` can be seen as a family of operations indexed
by `n ≥ 1`:

```text
ρ_σ^{(n)} : Part(X)^n → ℕ
ρ_σ^{(n)}(E₁,…,Eₙ) := #(⋂_{i=1}^n L_σ(E_i)).
```

The practical notation `ρ_σ(E₁,…,Eₙ)` is used.

Additional typing remarks:

```text
D_E      := ΔX \ C_E
Acc_σ(E) := R_σ \ L_σ(E)
```

Joint closure is decided by:

```text
ρ_σ(E₁,…,Eₙ) = 0  ⇔  (∧_{i=1}^n E_i) ≤ E_σ.
```

### Sorts

```text
X         : finite set of states
Part(X)   : lattice of partitions, equivalently equivalence relations on X
ΔX        : space of distinctions {x,x'} with x ≠ x'
σ : X → S : signature, or dynamic target
R_σ ⊆ ΔX  : distinctions required by σ
EqConf(X) : { C_E ⊆ ΔX | E ∈ Part(X) } admissible confusions
```

### Operations

On `Part(X)`:

```text
E ≤ F     : “finer than” order
E ∧ F     : meet = intersection of relations
E ∨ F     : join = equivalence closure of the generated union
```

Transport to distinctions:

```text
C_E ⊆ ΔX  : confusions induced by E
D_E       : preserved distinctions (= ΔX \ C_E)
```

Relative to `σ`:

```text
L_σ(E) ⊆ R_σ   : required losses (R_σ ∩ C_E)
Acc_σ(E) ⊆ R_σ : required accessibilities (R_σ \ L_σ(E))
```

Numerical projection:

```text
#        : cardinality on finite sets
ρ_σ(A,B) : #(L_σ(E_A) ∩ L_σ(E_B))
```

### Laws

```text
L_σ(E_A ∧ E_B) = L_σ(E_A) ∩ L_σ(E_B)
Acc_σ(E_A ∧ E_B) = Acc_σ(E_A) ∪ Acc_σ(E_B)

ρ_σ(A,B) = 0  ⇔  joint closure of σ by A∧B
```

## 1) Space of distinctions `ΔX`

Let `X` be a finite set of states.

```text
ΔX := {{x, x'} | x ≠ x'}
```

The calculation takes place in `𝒫(ΔX)`, the powerset of distinctions, before applying:

```text
# : 𝒫(ΔX) → ℕ
```

## 2) Partitions / interfaces as confusions

A partition `E` on `X` confuses certain pairs:

```text
C_E := {{x, x'} ∈ ΔX | x E x'}
D_E := ΔX \ C_E
```

- `C_E`: distinctions confused by `E`;
- `D_E`: distinctions preserved by `E`.

## 3) Future signature: required distinctions

For a future signature, or dynamic profile:

```text
σ : X → S
```

the minimal dynamic partition is:

```text
E_σ := Ker(σ)
```

The required distinctions, i.e. those separated by `σ`, are:

```text
R_σ := D_{E_σ}
     = {{x, x'} ∈ ΔX | σ(x) ≠ σ(x')}
```

and the relevant total is:

```text
r_σ := #R_σ
```

## 4) Losses and accessibility

Loss under an interface or partition `E`:

```text
L_σ(E) := R_σ ∩ C_E
ℓ_σ(E) := #L_σ(E)
```

Required distinctions accessible under `E`:

```text
Acc_σ(E) := R_σ \ L_σ(E)
a_σ(E) := #Acc_σ(E) = r_σ - ℓ_σ(E)
```

Canonical form:

```text
accessible = required - lost
```

where “lost” is a **subset** of `R_σ`, so incidence is preserved.

## 5) Central theorem: joint view `A∧B`

Vocabulary clarification: the **joint view** corresponds to the *meet* of partitions, not the join.

Joint view `A∧B`:

```text
E_{A∧B} := E_A ∧ E_B := E_A ∩ E_B
```

Join `A∨B`: transitive equivalence closure of the union, useful elsewhere but not here.

Notation:

```text
L_A     := L_σ(E_A)
L_B     := L_σ(E_B)
L_{A∧B} := L_σ(E_{A∧B})
```

Then:

```text
C_{A∧B} = C_A ∩ C_B
```

and therefore:

```text
L_{A∧B} = L_A ∩ L_B
```

Central thesis:

```text
the joint view A∧B loses exactly the intersection of the marginal losses.
```

Proposition:

```text
For every signature σ and all partitions E_A, E_B:

L_σ(E_A ∧ E_B) = L_σ(E_A) ∩ L_σ(E_B).
```

Proof:

```text
E_A ∧ E_B = E_A ∩ E_B.
Thus a pair is confused by E_A ∧ E_B exactly when it is confused by E_A and by E_B:
C_{A∧B} = C_A ∩ C_B.
Intersecting with R_σ:

L_σ(E_A ∧ E_B) = R_σ ∩ C_{A∧B} = (R_σ ∩ C_A) ∩ (R_σ ∩ C_B) = L_σ(E_A) ∩ L_σ(E_B).
```

## 6) Closure criterion

Predictive closure by `E`:

```text
E ≤ E_σ
⇔ L_σ(E) = ∅
⇔ Acc_σ(E) = R_σ
⇔ a_σ(E) = r_σ
```

where `E ≤ E_σ` is the “finer than” order in `Part(X)`, equivalently `E ⊆ E_σ` as relations on `X×X`.

Joint closure:

```text
L_σ(E_{A∧B}) = ∅
⇔ L_A ∩ L_B = ∅
⇔ ρ_σ(A,B) = 0
⇔ a_{A∧B} = r_σ
```

## 7) XOR example

Convention: write `00|01` for the unordered pair `{00,01}`.

For `σ(x)=xor(x)`:

```text
R_σ = {00|01, 00|10, 01|11, 10|11}
#R_σ = 4
```

For `A`, the first bit:

```text
L_A = {00|01, 10|11}
#L_A = 2
a_A = 4 - 2 = 2
```

For `B`, the second bit:

```text
L_B = {00|10, 01|11}
#L_B = 2
a_B = 4 - 2 = 2
```

For the joint view `A∧B`:

```text
L_{A∧B} = L_A ∩ L_B = ∅
#L_{A∧B} = 0
a_{A∧B} = 4 - 0 = 4
```

## 7bis) Separating example with `ρ=1`

The XOR case gives a canonical example where `ρ_σ(A,B)=0`. A second minimal example shows a **strict residual**.

Still with:

```text
X = {00,01,10,11}
σ(x) = xor(x)
R_σ = {00|01, 00|10, 01|11, 10|11}
```

Take:

```text
E_A = {{00,01},{10,11}}
```

so:

```text
L_A = {00|01, 10|11}.
```

Take:

```text
E_B = {{00,01,10},{11}}.
```

Then:

```text
L_B = {00|01, 00|10}.
```

Therefore:

```text
L_A ∩ L_B = {00|01}
ρ_σ(A,B) = 1.
```

Reading: the marginal losses have nonempty intersection, so the conjunction does not fully close `σ`.

## 8) Counterexample: identical marginal cardinalities, different diagnostics

Two configurations can have the same local Peano cardinalities `r_σ`, `#L_A`, `#L_B`, while having different
values of:

```text
#(L_A ∩ L_B).
```

The data:

```text
#L_A = 2
#L_B = 2
```

does not determine:

```text
#(L_A ∩ L_B).
```

Three typical cases:

```text
case 1: #(L_A ∩ L_B) = 0  → complete joint closure
case 2: #(L_A ∩ L_B) = 1  → residual loss
case 3: #(L_A ∩ L_B) = 2  → aligned losses
```

Thus the relevant datum for the joint is:

```text
#(L_A ∩ L_B)
```

and not merely `#L_A` and `#L_B`.

Name the critical invariant:

```text
ρ_σ(A,B) := #(L_A ∩ L_B)
```

Status. The bricks used here are classical — partitions, meet, confusions, intersections, cardinalization —
but the invariant `ρ_σ` is specific: it encodes incidence information, namely the effective overlap of losses,
which marginal quantities alone erase.

Two configurations can therefore share the same marginal cardinalities and produce opposite closure diagnostics.
The effective difference is precisely `ρ_σ(A,B)`.

Reading:

```text
ρ_σ(A,B) = residual loss of the joint view A∧B.
```

In particular, it can be read as an **invariant of joint closure defect**:

```text
ρ_σ(A,B) = 0  ⇔  A∧B closes σ
ρ_σ(A,B) > 0  ⇔  strict residual loss
```

It then plays three complementary roles:

```text
diagnostic   : closure or residual, with threshold 0
quantitative : size of the defect, value of ρ
structural   : incidence geometry of losses: disjoint, partial, aligned
```

Then:

```text
a_{A∧B} = r_σ - ρ_σ(A,B).
```

Conjunction gain. See the definition of `g_σ(A,B)` in the formal kernel: it is the surplus
`a_{A∧B} - max(a_A,a_B)`.

## 8bis) Universal bounds on `ρ_σ`

Notation:

```text
ℓ_A := #L_A
ℓ_B := #L_B
ρ   := ρ_σ(A,B) = #(L_A ∩ L_B)
```

Since `L_A, L_B ⊆ R_σ`, the intersection `L_A ∩ L_B` satisfies:

```text
max(0, ℓ_A + ℓ_B - r_σ) ≤ ρ ≤ min(ℓ_A, ℓ_B).
```

Reading: the Peano data `r_σ, ℓ_A, ℓ_B` determines only a possible interval for `ρ`.
Incidence, the effective overlap `L_A ∩ L_B`, is the datum that decides.

In XOR: `r_σ=4`, `ℓ_A=2`, `ℓ_B=2`, so:

```text
0 ≤ ρ ≤ 2.
```

The cases `ρ=0,1,2` correspond to closure, strict residual, maximal alignment.

## 9) Mechanism summary

```text
R_σ       = required distinctions
L_A       = required distinctions lost by A
L_B       = required distinctions lost by B
L_{A∧B}   = required distinctions lost by the joint view
ρ_σ(A,B)  = #(L_A ∩ L_B), joint residual loss
```

Then:

```text
L_{A∧B} = L_A ∩ L_B
```

and joint closure is read as:

```text
L_A ∩ L_B = ∅
⇔ ρ_σ(A,B) = 0
```

## 10) Technical notes: staying inside `Part(X)`

This distinction writing is useful, with two formal precisions:

1. A partition `E` is not an arbitrary subset of `ΔX`. The form `C_E ⊆ ΔX` must come from an
   **equivalence relation**, hence from an element of `Part(X)`.
2. For the join `E_A ∨ E_B`, the expression `E_A ∪ E_B` means the transitive/equivalence closure of the
   generated relation, so that one remains inside equivalence relations.

Remark: if `ΔX` is defined by excluding the diagonal `{(x,x)}`, then equivalence closure operations should be
understood as implicitly taking place on `X×X`, with the diagonal included, and then restricted back to `ΔX`.
This is what makes the components / `EqClosure` reading work.

### Admissible loss profiles

Point 1 above refines further: the losses `L_σ(E)` are not merely arbitrary subsets of `R_σ`; their form is
constrained by the blocks of the partition `E`.

If `X/E` denotes the set of blocks `B` of `E`, each block contributes an internal clique restricted to `R_σ`.
Define:

```text
R_σ[B] := {{x,x'} ∈ R_σ | x ∈ B and x' ∈ B}.
```

Then:

```text
L_σ(E) = ⋃_{B ∈ X/E} R_σ[B].
```

Thus a realizable loss profile is exactly a union of block contributions. In particular, an arbitrary subset
of `R_σ` is not necessarily of the form `L_σ(E)` for a partition `E`.

Intrinsic criterion, stability by closure. Given `L ⊆ R_σ`, set:

```text
Δ_X^diag := {(x,x) | x ∈ X}
```

then form the oriented relation:

```text
Rel(L) := Δ_X^diag ∪ {(x,x'), (x',x) | {x,x'} ∈ L}
```

and the generated equivalence:

```text
E_L := EqClosure(Rel(L)).
```

Then `L` is an admissible loss profile iff:

```text
L = R_σ ∩ C_{E_L}.
```

In that case, `L = L_σ(E_L)`: the equivalence generated by `L` creates no additional loss once restricted
to `R_σ`.

## 11) Generalization to `n` interfaces

Let `(E_i)_{i∈I}` be a finite nonempty family of interfaces, or partitions, on `X`.

### Multi-interface joint view

The joint view corresponds to the meet over the family:

```text
E_{∧I} := ∧_{i∈I} E_i
```

In `Part(X)`, this meet is the intersection of equivalence relations:

```text
E_{∧I} = ⋂_{i∈I} E_i
```

### Central formula: incidence power

At the level of confused distinctions:

```text
C_{∧I} = ⋂_{i∈I} C_i
```

Therefore, for fixed signature `σ`:

```text
L_σ(E_{∧I})
= R_σ ∩ C_{∧I}
= R_σ ∩ ⋂_{i∈I} C_i
= ⋂_{i∈I} (R_σ ∩ C_i)
= ⋂_{i∈I} L_σ(E_i).
```

In other words:

```text
L_{∧I} = ⋂_{i∈I} L_i.
```

This is the direct generalization of `L_{A∧B} = L_A ∩ L_B`.

### Multi-interface residual invariant

Define:

```text
ρ_σ(A_1,…,A_n) := #(⋂_{i=1}^n L_{A_i})
```

Reading:

```text
ρ_σ(A_1,…,A_n) = joint residual loss after conjoining n interfaces.
```

Then:

```text
a_{∧i A_i} = r_σ - ρ_σ(A_1,…,A_n).
```

### Multi-interface closure criterion

Joint closure of the family is:

```text
ρ_σ(A_1,…,A_n) = 0
```

equivalent to:

```text
⋂_{i=1}^n L_{A_i} = ∅
```

and to:

```text
a_{∧i A_i} = r_σ.
```

Empty case convention. If `I = ∅` is allowed, set:

```text
⋂_{i∈∅} L_i := R_σ
```

which corresponds to an empty joint view with no additional information, hence total loss of the required
distinctions.

### Higher-order incidence beyond `ρ`

For `n ≥ 2`, the invariant `ρ_σ(A_1,…,A_n) = #(⋂_i L_i)` is enough for the closure diagnostic,
but fine complementarity analysis also depends on partial intersections.

A compact way to encode this incidence is the unweighted nerve:

```text
𝓝_σ(E_1,…,E_n) := { J ⊆ {1,…,n} | J ≠ ∅ and ⋂_{j∈J} L_σ(E_j) ≠ ∅ }.
```

and its weighted version:

```text
w(J) := #(⋂_{j∈J} L_σ(E_j)).
```

In this language, `ρ_σ(E_1,…,E_n)` is just the weight of the maximal subfamily:

```text
ρ_σ(E_1,…,E_n) = w({1,…,n}).
```

## 11bis) Autonomous n-interface algebra

This section isolates the multi-interface algebra independently from any particular realization by partitions,
neural models, or dynamic mediators.

The starting point is not a scalar, but a family of losses:

```text
L : J → 𝒫(R_σ)
j ↦ L_j
```

where:

```text
R_σ  = set of distinctions required by the target σ
L_j  = required distinctions still lost by interface j
```

For a subfamily of interfaces `I ⊆ J`, the common residual is:

```text
Res(I) := ⋂_{j∈I} L_j.
```

With the mandatory convention:

```text
Res(∅) := R_σ.
```

This means: before any interface, all distinctions required by `σ` remain to be covered.

The associated scalar is only a projection:

```text
ρ(I) := #Res(I).
```

Closure by a subfamily is:

```text
Closed(I) ⇔ Res(I) = ∅ ⇔ ρ(I) = 0.
```

Irreducible closure is:

```text
IrreducibleClosed(I)
⇔
Res(I) = ∅
and
∀ K ⊂ I, Res(K) ≠ ∅.
```

That is, `I` closes the target, but no strict subfamily closes it.

The marginal gain of a new interface `j` after a family `I` is:

```text
δ(I,j) := ρ(I) - ρ(I ∪ {j}).
```

Equivalently:

```text
δ(I,j) = #(Res(I) \ L_j).
```

Reading: `δ(I,j)` counts the distinctions still residual after `I` which interface `j` separates.

Therefore:

```text
j useful relative to I
⇔ δ(I,j) > 0
⇔ Res(I ∪ {j}) ⊂ Res(I).
```

And:

```text
j redundant relative to I
⇔ δ(I,j) = 0
⇔ Res(I ∪ {j}) = Res(I).
```

Inside a closing family `I`, an interface `j ∈ I` is essential if ablating it recreates a residual:

```text
Essential(j,I)
⇔
Closed(I)
and
Res(I \ {j}) ≠ ∅.
```

It is redundant inside `I` if ablation does not break closure:

```text
Redundant(j,I)
⇔
Closed(I)
and
Res(I \ {j}) = ∅.
```

The complete object is therefore not `ρ(I)` alone. The complete object is the incidence of losses:

```text
d ∈ R_σ ↦ { j ∈ J | d ∈ L_j }.
```

or, dually, the intersection table:

```text
U ⊆ J ↦ ⋂_{j∈U} L_j.
```

The scalar `ρ(I)` answers only:

```text
how many distinctions remain lost by the whole family I?
```

Incidence answers the structural questions:

```text
which distinctions remain lost?
which interfaces lose them?
which interfaces separate them?
which subfamilies close?
which interfaces are essential, redundant, or complementary?
```

Condensed formulation:

```text
multi-interface = incidence algebra of losses
closure         = empty common residual
irreducibility  = minimality under strict subfamilies
gain            = contraction of the residual
redundancy      = absence of residual contraction
essentiality    = residual recreated by ablation
```

Thus the useful arithmetic is not first an arithmetic of numbers. It is an arithmetic of intersections of losses,
and only then a cardinalization.

---

## 12) Algebraic properties: lattice morphisms

### Confusion morphism: `E ↦ C_E`

Define:

```text
C : Part(X) → 𝒫(ΔX)
E ↦ C_E
```

where:

```text
C_E := {{x, x'} ∈ ΔX | x E x'}.
```

**Monotonicity.** For the “finer than” order:

```text
E ≤ F  ⇒  C_E ⊆ C_F.
```

Reading: if `E` is finer than `F`, it identifies fewer pairs, so the set of pairs confused by `E`
is included in the set confused by `F`.

**Meet preservation.** For every finite family `(E_i)`:

```text
C_{∧i E_i} = ⋂i C_{E_i}.
```

Precise formulation: `E ↦ C_E` is an order morphism preserving finite meets, i.e. a meet-semilattice
homomorphism into `(𝒫(ΔX), ⊆, ∩)`.

For the join, a fully clean notation separates two levels:

1. `C_E ⊆ ΔX` encodes unordered pairs `{x,x'}`.
2. Equivalence closure naturally lives on ordered pairs `(x,x') ∈ X×X`.

Introduce:

```text
Δ_X^diag := {(x,x) | x ∈ X}

Rel(C) := Δ_X^diag ∪ {(x,x'), (x',x) | {x,x'} ∈ C}
```

Then the join of partitions is:

```text
E_A ∨ E_B = EqClosure(Rel(C_{E_A}) ∪ Rel(C_{E_B}))
```

where `EqClosure` denotes reflexive-symmetric-transitive closure, equivalently connected components of the
generated graph.

Returning to unordered distinctions:

```text
C_{E_A ∨ E_B}
= {{x,x'} ∈ ΔX | (x,x') ∈ EqClosure(Rel(C_{E_A}) ∪ Rel(C_{E_B}))}.
```

### Relative-loss morphism: `L_σ`

For fixed signature `σ`, define:

```text
L_σ : Part(X) → 𝒫(R_σ)
E ↦ L_σ(E) := R_σ ∩ C_E.
```

Then `L_σ` is also monotone and preserves meets:

```text
E ≤ F  ⇒  L_σ(E) ⊆ L_σ(F)
```

and:

```text
L_σ(∧i E_i) = ⋂i L_σ(E_i).
```

These two properties explain why the multi-interface closure algebra reduces to an arithmetic of intersections
before cardinalization.

### Dual formula: accessibilities

Set:

```text
Acc_i := Acc_σ(E_i) = R_σ \ L_σ(E_i).
```

Then by De Morgan:

```text
Acc_σ(∧i E_i)
= R_σ \ ⋂i L_σ(E_i)
= ⋃i (R_σ \ L_σ(E_i))
= ⋃i Acc_σ(E_i).
```

Therefore:

```text
joint accessibility = union of marginal accessibilities
joint loss          = intersection of marginal losses
```

## 12bis) Image of partitions in `𝒫(ΔX)`

A partition `E ∈ Part(X)` induces a set of confusions `C_E ⊆ ΔX`. The converse is not true:
an arbitrary subset of `ΔX` need not correspond to an equivalence relation.

Define the set of admissible confusions:

```text
EqConf(X) := { C_E ⊆ ΔX | E ∈ Part(X) }.
```

Then:

```text
C : Part(X) → EqConf(X)
E ↦ C_E
```

is bijective: each partition corresponds to exactly one set of confused pairs.

Moreover, it is an isomorphism of ordered sets:

```text
E ≤ F   ⇔   C_E ⊆ C_F.
```

At the level of operations, meet is transported without loss:

```text
C_{E ∧ F} = C_E ∩ C_F.
```

Thus one can equip `EqConf(X)` with the transported meet:

```text
U ∧_Δ V := U ∩ V.
```

For join, the transported operation must pass through equivalence closure at the relation level (`X×X`),
then restrict back to distinctions `ΔX`. It can be written:

```text
U ∨_Δ V
:=
C_{ EqClosure(Rel(U) ∪ Rel(V)) }.
```

With these transported operations:

```text
Part(X) ≅ EqConf(X)
```

as lattices.

## 13) Characteristic theorems

### 13.1) Invariance under renaming

Let `X` and `X'` be finite sets and let `φ : X ≃ X'` be a bijection.
Transport:

```text
σ' := σ ∘ φ⁻¹
E' := transport(E, φ)   (relation: x' E' y' ⇔ φ⁻¹(x') E φ⁻¹(y'))
```

There is a canonical transport of distinctions and losses:

```text
R_σ  ↔ R_{σ'}
L_σ(E) ↔ L_{σ'}(E')
```

Therefore:

```text
ρ_σ(E_A, E_B) = ρ_{σ'}(E'_A, E'_B)
```

Reading: `ρ` depends only on the relative configuration of partitions, not on the names of states.

### 13.2) Immediate vs delayed cardinalization

The marginal data:

```text
#L_A, #L_B
```

does not determine the joint quantity:

```text
#(L_A ∩ L_B).
```

Thus immediate cardinalization, Peano-style, erases incidence. Delayed cardinalization preserves:

```text
L_A ⊂ R_σ,  L_B ⊂ R_σ,  L_A ∩ L_B.
```

### 13.3) Minimal classification: closure vs residual

The joint closure diagnostic reduces to:

```text
ρ_σ(A,B) = 0   (closure)
ρ_σ(A,B) > 0   (strict residual)
```

The counterexample of section 8 shows that two systems can share the same marginal values while falling on
opposite sides of this threshold.

## 14) Effective computation

The calculation can be implemented directly on bitsets indexing `R_σ ⊆ ΔX`.

For a pair `(x,x')`, index a coordinate `p ∈ {0,…,|ΔX|-1}`.

Then:

```text
bitset(R_σ)          : mask of required distinctions
bitset(C_E)          : mask of distinctions confused by E
bitset(L_σ(E))       = bitset(R_σ) AND bitset(C_E)
bitset(L_res)        = AND_i bitset(L_σ(E_i))
ρ_σ(A_1,…,A_n)        = popcount(bitset(L_res))
```

The complexity is linear in bitset size:

```text
O(|ΔX| / w)
```

where `w` is the machine word size, for example 64, with a low constant factor: `AND` plus `popcount`.
