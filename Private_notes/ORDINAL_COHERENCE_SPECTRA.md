# Ordinal Closure Ranks for Coherence Spectra

This note explains when (and how) **ordinals** arise from the monotone contraction of coherence
spectra. The key point is a sharp limitation:

```text
If Φ is finite, then Spec^Coh_T(Φ) is finite,
so any monotone contraction stabilizes in < ω steps.
```

Nontrivial ordinal ranks require going beyond finite `Φ` (or beyond raw valuation spectra).

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

## 2. Triviality for finite Φ (no genuine transfinite depth)

### Lemma (finite-spectrum stabilization)

Assume `Φ` is finite. Then `S_0 = Spec^Coh_{T_0}(Φ)` is finite, hence every descending chain

```text
S_0 ⊇ S_1 ⊇ S_2 ⊇ …
```

stabilizes after finitely many strict inclusions.

Equivalently:

```text
There exists N < ω such that for all n ≥ N, S_n = S_N.
```

**Reason:** a strictly descending chain of finite sets can have only finitely many strict drops.

### Consequence

If `Φ` is finite, any “closure time” or “stability time” derived solely from the chain of spectra is
always a **finite ordinal**. You cannot obtain a genuinely transfinite rank (like `ω`, `ω+1`, …) from
finite `Φ` alone.

---

## 3. Where ordinals become nontrivial

To get nontrivial ordinal ranks, you must enlarge the object so that the spectrum space is infinite
and admits a genuinely transfinite elimination process.

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

(The `ω` case is impossible when `Φ` is finite by §2.)

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

so closure/stability ranks are always **finite**.

2. Nontrivial ordinals require enlarging the object:

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

