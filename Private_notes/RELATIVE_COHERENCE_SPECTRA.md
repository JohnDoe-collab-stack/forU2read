# Relative Coherence Spectra (multi-sentence closure invariant)

This note generalizes the binary “coherence spectrum closure” invariant to **finite families** of
sentences, making the object genuinely geometric:

```text
Spec^Coh_T(Φ) ⊆ {0,1}^n
```

It is designed to sit on top of `Private_notes/COHERENCE_SPECTRUM_CLOSURE.md`.

---

## 0. Setup (meta-level)

- `T` : a (classical) first-order theory.
- `Φ = {φ₁,…,φₙ}` : a **finite** family of **closed sentences** in the language of `T`.
- `Coh(U)` : a chosen meta-level coherence predicate.
- Working assumption (local, per target): `Spec^Coh_T(Φ) ≠ ∅` (spectrum inhabitation).

### Scope convention for `Coh`

We allow three regimes (exactly as in the binary note):

```text
(A) Coh := Con_syn

or

(B) Coh := Coh_C for a fixed semantic class C, where
    Coh_C(U) := “∃ M ∈ C such that M ⊨ U”

or

(C) Coh := an abstract coherence predicate, together with the specific stability properties
    explicitly invoked in each statement below.
```

In regime (C), we do **not** assume global completeness-style properties of `Coh`. We assume only:

```text
Spec^Coh_T(Φ) ≠ ∅
```

and, in protocol dynamics, `Spec^Coh_{T_t}(Φ) ≠ ∅` whenever we need the defect to stay in a fixed range.

### A canonical semantic choice (one fixed reference case)

To make the framework **portable** (not “just a parameterized schema”), it helps to fix one canonical
semantic coherence predicate as a reference point.

In this note, the reference case will be:

```text
C := the class of transitive models of ZFC
Coh_C(U) := “U has a transitive model”.
```

This choice is canonical in set theory because it is the smallest standard semantic strengthening of
syntactic consistency that (i) supports absolute arithmetic facts, and (ii) separates semantic
branch admissibility from syntactic provability in a clean way (see §7.1).

---

## 1. Branches for a family of sentences

Let:

```text
v ∈ {0,1}^n
```

be a Boolean valuation. Define the **branch theory fragment**:

```text
Φ^v := {  φᵢ   if vᵢ = 1
        { ¬φᵢ  if vᵢ = 0
```

and the extended theory:

```text
T + Φ^v.
```

For `n=1` (binary case), this recovers the previous definition:

```text
Spec^Coh_T(φ) ⊆ {0,1}.
```

---

## 2. The multi-sentence coherence spectrum

Define:

```text
Spec^Coh_T(Φ) := { v ∈ {0,1}^n : Coh(T + Φ^v) }.
```

This is the central object: an explicit subset of the Boolean cube. It encodes:

- which **global truth-branches** are `Coh`-admissible over `T`;
- how those branches correlate across coordinates.

---

## 3. Closure defect (multi-sentence)

Assume `Spec^Coh_T(Φ) ≠ ∅`. Define:

```text
D^Coh_T(Φ) := |Spec^Coh_T(Φ)| − 1.
```

Interpretation:

- **Closure on Φ**:
  ```text
  D^Coh_T(Φ) = 0
  ```
  iff **exactly one** global branch remains `Coh`-admissible:
  ```text
  |Spec^Coh_T(Φ)| = 1.
  ```

- **Openness on Φ**:
  ```text
  D^Coh_T(Φ) > 0
  ```
  iff **multiple** global branches remain `Coh`-admissible.

Maximally open case:

```text
Spec^Coh_T(Φ) = {0,1}^n
⇒
D^Coh_T(Φ) = 2^n − 1.
```

So:

```text
binary: D ∈ {0,1}
multi-sentence: D ∈ {0,…,2^n−1}.
```

---

## 4. Collapse theorem (syntactic consistency regime)

In regime (A), `Coh := Con_syn`, we have:

```text
Spec^Con_syn_T(Φ)
=
{ v ∈ {0,1}^n : Con_syn(T + Φ^v) }.
```

In the binary case `Φ={φ}`, under `Con_syn(T)`:

```text
D^Con_syn_T(φ)=0
⇔
T ⊢ φ  or  T ⊢ ¬φ.
```

So:

```text
Coh = Con_syn
⇒
binary spectral closure = syntactic decidability.
```

### Finite-family refinement (what collapses, exactly)

For finite `Φ`, the collapse is in fact **complete** (in the usual metatheory of classical first-order
logic):

```text
Assume Φ = {φ₁,…,φₙ} is finite and Con_syn(T).

Then Spec^Con_syn_T(Φ) = {v*}
iff
T syntactically decides every coordinate φᵢ, with truth-values given by v*:

  v*_i = 1 ⇒ T ⊢ φᵢ
  v*_i = 0 ⇒ T ⊢ ¬φᵢ.
```

**Proof sketch (⇒):** fix `i`. Suppose `v*_i = 1` but `T ⊬ φᵢ`. Then `T + ¬φᵢ` is syntactically
consistent (otherwise `T ⊢ ¬¬φᵢ` and classically `T ⊢ φᵢ`). By Lindenbaum’s lemma (existence of a
complete consistent extension), extend `T + ¬φᵢ` to a complete consistent theory `T'`. In particular,
for each `j ≠ i`, `T'` contains either `φⱼ` or `¬φⱼ`, yielding a valuation `w` with `w_i = 0` and
`T + Φ^w ⊆ T'`. Hence `Con_syn(T + Φ^w)`, so `w ∈ Spec^Con_syn_T(Φ)`, contradicting uniqueness.
The case `v*_i = 0` is symmetric.

**Proof sketch (⇐):** if `T` decides each `φᵢ`, then exactly one valuation matches those decisions and
every other valuation contradicts at least one decided coordinate, hence is inconsistent.

This is the precise sense in which the invariant becomes “trivial” in regime (A).

---

## 5. Semantic theorem (model-class regime)

In regime (B), fix a semantic class `C` and define:

```text
Coh_C(U) := ∃ M ∈ C, M ⊨ U.
```

Then:

```text
Spec^Coh_C_T(Φ)
=
{ v ∈ {0,1}^n : ∃ M ∈ C, M ⊨ (T + Φ^v) }.
```

Equivalently:

```text
Spec^Coh_C_T(Φ)
is exactly the set of Boolean truth-profiles of Φ
realized by C-admissible models of T.
```

For `n=1`, on the inhabited domain `Coh_C(T)`, closure becomes “truth forced relative to `C`”:

```text
Spec^Coh_C_T(φ) = {1}
⇔
every M ∈ C with M ⊨ T also satisfies φ,
```

and similarly for `{0}` (with `¬φ`).

---

## 6. Monotonicity (branch elimination under extension)

Assume **downward heredity** for `Coh`:

```text
If U ⊆ V and Coh(V), then Coh(U).
```

Then for theory extension:

```text
T ⊆ S
⇒
Spec^Coh_S(Φ) ⊆ Spec^Coh_T(Φ).
```

Proof (one line):

```text
v ∈ Spec^Coh_S(Φ)
⇒ Coh(S+Φ^v)
⇒ Coh(T+Φ^v)
⇒ v ∈ Spec^Coh_T(Φ).
```

So:

```text
extension of theory = elimination of branches.
```

In a protocol chain:

```text
T₀ ⊆ T₁ ⊆ T₂ ⊆ …
```

we get a descending chain:

```text
Spec^Coh_{T₀}(Φ) ⊇ Spec^Coh_{T₁}(Φ) ⊇ Spec^Coh_{T₂}(Φ) ⊇ …
```

and therefore (on the inhabited domain):

```text
D^Coh_{T₀}(Φ) ≥ D^Coh_{T₁}(Φ) ≥ D^Coh_{T₂}(Φ) ≥ …
```

---

## 7. A canonical separation example (semantic closure ≠ syntactic decision)

This section exhibits the phenomenon that motivates the whole construction:

```text
semantic branch closure can strictly refine syntactic decidability.
```

Let:

```text
T := ZFC
φ := Con_syn(ZFC)
C := the class of transitive models of ZFC
Coh_C(U) := “U has a transitive model”
```

Assume `Coh_C(ZFC)` (i.e. there exists a transitive model of ZFC).

### 7.1 Separation theorem (clean statement with explicit meta-assumptions)

Let:

```text
T := ZFC
φ := Con_syn(ZFC)
```

Assume the following meta-level hypotheses:

```text
(H1) Coh_C(ZFC) holds, i.e. there exists a transitive model of ZFC.
(H2) Con_syn(ZFC) holds (ordinary syntactic consistency).
```

Then:

```text
Spec^Coh_C_ZFC(Con_syn(ZFC)) = {1}
and
Spec^Con_syn_ZFC(Con_syn(ZFC)) = {0,1}.
```

Equivalently:

```text
D^Coh_C_ZFC(Con_syn(ZFC)) = 0
but
D^Con_syn_ZFC(Con_syn(ZFC)) = 1.
```

This is the canonical separation pattern:

```text
semantic Coh-closure  ≠  syntactic decision.
```

### Claim (semantic closure in the transitive-model regime)

```text
Spec^Coh_C_ZFC(Con_syn(ZFC)) = {1}.
```

Reason (meta-level): if `M` is a transitive model of ZFC, then `ω^M = ω` is standard, so arithmetical
truth about “finite proof codes” is absolute to `M`. In particular, `M ⊨ Con_syn(ZFC)`. Hence
`ZFC + ¬Con_syn(ZFC)` has **no** transitive model, while `ZFC + Con_syn(ZFC)` does (namely `M`).

### Contrast (syntactic openness under Gödel II)

Under the usual hypotheses (e.g. `Con_syn(ZFC)` and sufficient arithmetic strength), Gödel’s second
incompleteness theorem yields:

```text
ZFC ⊬ Con_syn(ZFC).
```

So:

```text
semantic closure relative to C
≠
syntactic decision by T.
```

To make the separation fully explicit as a spectrum comparison, one can also record the
syntactic-consistency spectrum under the usual meta-hypotheses on ZFC (e.g. `Con_syn(ZFC)` and
sufficient arithmetic strength for Gödel II):

```text
Spec^Con_syn_ZFC(Con_syn(ZFC)) = {0,1},
```

i.e. both `ZFC + Con_syn(ZFC)` and `ZFC + ¬Con_syn(ZFC)` are syntactically consistent at the meta
level (the latter follows since if `ZFC + ¬Con_syn(ZFC)` were inconsistent then `ZFC ⊢ Con_syn(ZFC)`).

Thus the canonical separation takes the crisp form:

```text
Spec^Con_syn_ZFC(Con_syn(ZFC)) = {0,1}
but
Spec^Coh_C_ZFC(Con_syn(ZFC))   = {1},
```

so:

```text
D^Con_syn_ZFC(Con_syn(ZFC)) = 1
but
D^Coh_C_ZFC(Con_syn(ZFC))   = 0.
```

This is the canonical separation pattern the spectrum is built to capture.

---

## 8. Coordinate-wise openness/closure (geometry beyond cardinality)

The full subset:

```text
Spec^Coh_T(Φ) ⊆ {0,1}^n
```

is a strictly richer invariant than its cardinality. One simple refinement is coordinate openness.

Coordinate `i` is **Coh-closed** iff all spectrum points agree on it:

```text
i is closed ⇔ ∃ b ∈ {0,1}, ∀ v ∈ Spec^Coh_T(Φ), vᵢ = b.
```

Coordinate `i` is **Coh-open** iff both values occur:

```text
∃ v,w ∈ Spec^Coh_T(Φ) with vᵢ = 0 and wᵢ = 1.
```

Two spectra may have the same `D` but very different geometry, e.g.:

```text
Spec₁ = {000, 111}
Spec₂ = {000, 001}
```

Both have `|Spec|=2` hence `D=1`, but:

```text
Spec₁ : all coordinates vary together.
Spec₂ : exactly one coordinate varies.
```

So the “true” invariant is the spectrum subset itself; `D` is just the first numeric summary.

---

## 9. Spectral dependencies (“relative logical correlation”)

The spectrum also encodes dependencies between sentences, relative to `Coh`.

For two sentences `(φ, ψ)`:

- If:
  ```text
  Spec^Coh_T(φ, ψ) = {00, 11}
  ```
  then `φ` and `ψ` always share the same value on `Coh`-admissible branches.

- If:
  ```text
  Spec^Coh_T(φ, ψ) = {01, 10}
  ```
  then they always have opposite values on `Coh`-admissible branches.

- If:
  ```text
  Spec^Coh_T(φ, ψ) = {00, 01, 10, 11}
  ```
  then they are independent relative to `Coh`.

So `Spec^Coh_T(Φ)` induces a notion of “relative correlation” between statements.

---

## 10. Order-theoretic (functorial) view

Let `Th` be the poset of theories ordered by extension:

```text
T ≤ S  ⇔  T ⊆ S.
```

Fix `Φ`. Then:

```text
T ↦ Spec^Coh_T(Φ)
```

is contravariant:

```text
T ⊆ S  ⇒  Spec^Coh_S(Φ) ⊆ Spec^Coh_T(Φ).
```

So we get an order functor:

```text
Spec^Coh_Φ : Th^op → P({0,1}^n).
```

Conceptually:

```text
as the theory grows, the Coh-admissible region of the Boolean cube contracts.
```

---

## 11. Paper-ready statement (template)

```text
Theorem (Relative Coherence Spectrum Closure).

Let T be a classical first-order theory, let Φ = {φ₁,…,φₙ} be a finite family of closed sentences,
and let Coh be either:

(i) Con_syn,
(ii) Coh_C for a fixed semantic class C of structures, or
(iii) an abstract coherence predicate with downward heredity and local spectrum inhabitation.

Define:
    Spec^Coh_T(Φ) = { v ∈ {0,1}^n : Coh(T + Φ^v) }.

Then:

1) (Monotonicity) If T ⊆ S, then Spec^Coh_S(Φ) ⊆ Spec^Coh_T(Φ).
2) (Closure) |Spec^Coh_T(Φ)| = 1 characterizes Coh-closure on Φ.
3) (Openness) |Spec^Coh_T(Φ)| > 1 characterizes Coh-openness on Φ.
4) (Collapse) For Coh = Con_syn, binary closure coincides with syntactic decidability.
5) (Separation) For stronger semantic Coh, Coh-closure can strictly refine syntactic decidability.
```

---

## 12. Naming

Suggested names:

```text
Relative Coherence Spectra
Coherence Spectrum Theory
```

Core invariant:

```text
Spec^Coh_T(Φ)
```

First numeric summary:

```text
D^Coh_T(Φ) = |Spec^Coh_T(Φ)| − 1.
```

Dynamics:

```text
extension = monotone contraction of the spectrum.
closure   = uniqueness of the admissible branch.
openness  = multiplicity of admissible branches.
```
