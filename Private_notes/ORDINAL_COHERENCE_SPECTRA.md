# Ordinal Closure Ranks for Coherence Spectra

This note explains when (and how) **ordinals** arise from the monotone contraction of coherence
spectra. The key point is a sharp limitation, but it must be stated with the right quantifier:

```text
If Φ is finite, then Spec^Coh_T(Φ) is finite,
so there are only finitely many *distinct* spectra (finite spectral height).

However, the ordinal stage at which a strict drop occurs can still be transfinite
in an ordinal-indexed protocol (finite Φ does not force finite protocol time).
```

Two different “ordinal phenomena” must be separated:

- **Protocol-time ordinals** (e.g. `cl`, `stab`, `death_π`) can already be transfinite even for
  finite `Φ`, because a strict drop may occur first at a limit stage when the chosen `Coh` lacks
  limit-continuity.
- **Transfinite spectral height** (infinitely many strict drops between distinct spectra) requires
  an **infinite** spectrum space (e.g. `Φ` infinite, or a topological/type spectrum with a
  derivative process).

This note is meant to complement:

- `Private_notes/COHERENCE_SPECTRUM_CLOSURE.md` (binary spectrum)
- `Private_notes/RELATIVE_COHERENCE_SPECTRA.md` (finite-family spectrum)

---

## 0. Setup (meta-level)

- `T` : a (classical) first-order theory.
- `Coh(U)` : a fixed meta-level coherence predicate (see the scope conventions in the two notes above).
- `Φ` : a family of closed sentences.
- For each `T` and `Φ`, define:

```text
Spec^Coh_T(Φ) := { v : Φ → {0,1}  :  Coh(T + Φ^v) }.
```

When `Φ = {φ₁,…,φₙ}` is finite, we identify valuations with:

```text
v ∈ {0,1}^n.
```

---

## 1. Protocols indexed by ordinals

A (monotone) protocol is a chain of theories indexed by an ordinal:

```text
(T_α)_{α < Λ}
```

such that:

```text
α < β  ⇒  T_α ⊆ T_β.
```

At limit stages we take unions:

```text
T_λ := ⋃_{α<λ} T_α.
```

Define the spectrum process:

```text
S_α := Spec^Coh_{T_α}(Φ).
```

Under **downward heredity** for `Coh`:

```text
U ⊆ V and Coh(V) ⇒ Coh(U),
```

we get monotonicity (branch elimination):

```text
S_0 ⊇ S_1 ⊇ S_2 ⊇ … ⊇ S_α ⊇ …
```

---

## 2. Finite Φ: finite spectral height, not necessarily finite protocol time

This section distinguishes two notions:

```text
1) spectral height: the number of strict drops between *distinct* spectra
2) protocol time:   the ordinal index at which those drops occur
```

Finite `Φ` bounds (1), but not necessarily (2).

### Lemma (finite spectral height / compressed stabilization)

Assume `Φ` is finite. Then `S_0 = Spec^Coh_{T_0}(Φ)` is finite, hence every spectrum `S_α` is a subset
of the finite set `S_0`. Therefore, there are only finitely many possible distinct spectrum values
along the protocol:

```text
{ S_α : α < Λ } ⊆ P(S_0),
```

and `P(S_0)` is finite.

In particular, any descending chain

```text
S_0 ⊇ S_1 ⊇ S_2 ⊇ …
```

has only finitely many **strict drops** after compression (i.e. after deleting repeated spectra).

Equivalently, the chain of distinct spectra has finite length:

```text
S_{α₀} ⊋ S_{α₁} ⊋ … ⊋ S_{α_k}
```

for some finite `k`, where each inclusion is strict and each `S_{α_i}` is a new spectrum value.

**Reason:** a strictly descending chain of subsets of a finite set has finite length.

### Consequence

If `Φ` is finite, the number of strict branch-elimination events is finite (finite spectral height).

In particular, in a **spectrally compressed protocol** (one with no repeated spectra before it
stabilizes/terminates), closure and stabilization must occur after finitely many successor steps:

```text
if S_{α+1} ⊊ S_α whenever S_{α+1} ≠ S_α,
then the number of such strict drops is ≤ |S_0|.
```

But the **ordinal protocol time** at which those finitely many eliminations happen can still be
transfinite. For example, it is consistent with monotonicity that:

```text
S_α = {0,1} for all α < ω,
S_ω = {1}.
```

So:

```text
finite Φ ⇒ finite spectral height
finite Φ ⇏ finite ordinal protocol time.
```

### Example (finite Φ with a limit-stage drop under a non-compact Coh)

This illustrates how a strict drop can occur first at a limit stage even when `Φ={φ}` is binary.

Language:

```text
L = {R}  where R is a unary predicate.
```

Target sentence:

```text
φ := ∃x R(x).
```

Semantic coherence:

```text
C := finite L-structures
Coh_C(U) := “∃ finite M ∈ C such that M ⊨ U”.
```

For each `k≥1`, let `σ_k` assert “there exist at least k distinct elements”.

Define a protocol:

```text
T_n := { ¬φ → σ_k : 1 ≤ k ≤ n }
T_ω := ⋃_{n<ω} T_n.
```

Then for each `n<ω`, both branches are `Coh_C`-admissible (treating `n=0` separately if one wishes):

```text
T_n + φ   has a finite model (take any finite model with R nonempty),
T_n + ¬φ  has a finite model (for n≥1: take a finite model of size n with R empty;
                              for n=0: take any one-element model with R empty).
```

So:

```text
Spec^Coh_C_{T_n}(φ) = {0,1}   for all n<ω.
```

At the limit:

```text
T_ω + φ    still has a finite model,
T_ω + ¬φ   has no finite model (it would have to satisfy σ_k for all k).
```

Hence:

```text
Spec^Coh_C_{T_ω}(φ) = {1},
```

so the closure time (protocol index) is `ω`, even though there is only one strict drop.

### Remark (syntactic consistency is limit-continuous)

For `Coh = Con_syn` (ordinary first-order syntactic consistency), the above “first drop at a limit
stage” phenomenon does **not** occur for increasing chains, by compactness / finitary proofs.
Equivalently, for `Coh = Con_syn` one has **limit-continuity**:

```text
S_λ = ⋂_{α<λ} S_α.
```

So transfinite protocol-time ordinals for finite `Φ` are a feature of **non-compact** (or otherwise
non-limit-continuous) semantic coherence predicates, not of bare syntactic consistency.

---

## 3. Where transfinite spectral height becomes nontrivial

For finite `Φ`, ordinals can already appear as **protocol-time indices** (when drops happen), but
the *compressed* elimination structure has finite height (only finitely many strict drops).

To obtain **genuinely transfinite spectral height** (infinitely many strict drops between distinct
spectra), one must enlarge the object so that the spectrum space is infinite and admits a genuinely
transfinite elimination process.

Two clean routes:

### Route A: countably infinite families Φ

Let:

```text
Φ = {φ₀, φ₁, φ₂, …}
```

Then valuations live in a Cantor-like space:

```text
v ∈ {0,1}^ℕ,
```

and the spectrum:

```text
Spec^Coh_T(Φ) ⊆ {0,1}^ℕ
```

can be infinite. A protocol can then eliminate branches in a way that produces transfinite closure
or stabilization ordinals.

### Route B: replace “valuation spectra” by a topological/type spectrum

Instead of a raw Boolean valuation space, one can use an established spectral object (e.g. a Stone
space / space of types / Boolean-valued model spectrum). In such settings, transfinite ranks arise
via standard **derivatives** (Cantor–Bendixson style), producing an ordinal rank even when each stage
removes only “isolated” points.

This route is closer to classical “spectral” mathematics and aligns naturally with the term
“spectrum”.

---

## 4. Ordinal invariants from a transfinite protocol

Assume a transfinite protocol `(T_α)_{α<Λ}` and define `S_α` as above.

### 4.1 Branch death time

For a branch `v ∈ S_0`, define its **death time** (if it ever dies):

```text
death_π(v) := least α such that v ∉ S_α.
```

This is an ordinal-valued “elimination time” attached to each initial branch.

### 4.2 Closure ordinal (uniqueness time)

If the spectrum ever becomes a singleton, define:

```text
cl^Coh_π(T, Φ) := least α such that |S_α| = 1.
```

Interpretation:

```text
cl = 0  : already closed on Φ
cl = 1  : one extension step closes Φ
cl = ω  : closure after countably many extensions
```

(The `ω` case is possible even when `Φ` is finite; what is impossible for finite `Φ` is *transfinite
spectral height*, i.e. infinitely many strict drops between distinct spectra.)

### 4.3 Stability ordinal (eventual constancy)

Define the **stabilization time**:

```text
stab^Coh_π(T, Φ) := least α such that for all β ≥ α, S_β = S_α.
```

This measures when no further branch elimination occurs.

### 4.4 Global elimination rank

A natural global ordinal is the supremum of death times:

```text
SOrd^Coh_π(T, Φ)
:=
sup { death_π(v) + 1 : v ∈ S_0 and death_π(v) exists }.
```

This is an ordinal summarizing the “depth” of elimination across all branches.

---

## 5. Why this is genuinely “ordinal”

When the spectrum space is infinite, a monotone elimination process can have:

- infinitely many strict drops,
- limit stages where the process has not stabilized,
- ranks that are sensitive to the *structure* of elimination, not only cardinalities.

This is exactly the kind of situation where ordinals are the correct invariants.

---

## 6. Relationship to proof-theoretic ordinals (analogy)

Proof-theoretic ordinals measure how far a theory controls induction / well-foundedness.

Here, the ordinal ranks measure how far a **protocol** controls the elimination of `Coh`-admissible
branches of a spectrum:

```text
proof-theoretic ordinal  ~  induction/well-foundedness strength
spectral closure ordinal ~  branch-elimination strength relative to Coh
```

This is an analogy, not an identification: the definitions live at different levels, but the shape
of the invariant (ordinal rank induced by a monotone transfinite process) is the same.

---

## 7. Summary

1. With finite `Φ`, spectra are finite:

```text
Spec^Coh_T(Φ) ⊆ {0,1}^n
```

Therefore the number of **distinct** spectra (spectral height) along any monotone protocol is finite.
However, the ordinal indices where those finitely many strict drops occur can be transfinite.

2. Transfinite protocol-time ordinals can already occur for finite `Φ` under suitable non-compact
   `Coh` (drops at limit stages). To obtain **transfinite spectral height**, one must enlarge the
   object:

```text
Φ infinite
or
replace valuation spectra by a genuine topological/type spectrum.
```

3. Once the spectrum space is infinite, the following ordinal invariants are natural:

```text
death_π(v)   : when a branch v is eliminated
cl^Coh_π     : when uniqueness/closure is reached
stab^Coh_π   : when stabilization occurs
SOrd^Coh_π   : global elimination rank
```
