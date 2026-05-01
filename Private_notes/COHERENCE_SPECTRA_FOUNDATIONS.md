# Coherence Spectra Foundations (Coh-parametric, semantic instances, ordinal protocols)

This note is a **paper-grade unification** of three layers that were previously split across:

- `Private_notes/COHERENCE_SPECTRUM_CLOSURE.md` (binary spectrum + collapse vs non-collapse),
- `Private_notes/RELATIVE_COHERENCE_SPECTRA.md` (finite-family spectra as a geometric object),
- `Private_notes/ORDINAL_COHERENCE_SPECTRA.md` (ordinal protocol ranks and what they really mean).

The goal is to keep the framework *non-slipping*:

- we separate **ordinary syntactic consistency** from stronger “coherence” predicates;
- we keep the **subset spectrum** as the primary invariant;
- we distinguish **spectral height** from **ordinal protocol time**.

---

## 0. Objects and typing (meta-level)

Fix:

- `T` : a (classical) first-order theory in some language `L`.
- `Φ = {φ₁,…,φₙ}` : a **finite family** of **closed sentences** of `L`.
- `Coh(U)` : a chosen **meta-level** coherence predicate applied to theories `U` in the same language.

We work in one of three regimes (scope convention):

```text
(A) Coh := Con_syn

or

(B) Coh := Coh_C for a fixed semantic class C of L-structures, where
    Coh_C(U) := “∃ M ∈ C such that M ⊨ U”

or

(C) Coh := an abstract coherence predicate, together with only the specific
    stability assumptions explicitly invoked in each statement.
```

In regime (C), whenever we need to talk about “closure defect” as a number with a fixed range, we
assume **local inhabitation** for the specific target:

```text
Spec^Coh_T(Φ) ≠ ∅.
```

---

## 1. Branch encoding for a finite family Φ

Let a valuation be:

```text
v ∈ {0,1}^n.
```

Define branch literals:

```text
φᵢ^1 := φᵢ
φᵢ^0 := ¬φᵢ
```

and the branch fragment:

```text
Φ^v := { φᵢ^{vᵢ} : i = 1,…,n }.
```

The corresponding branch extension is:

```text
T + Φ^v.
```

Binary case (`n=1`) recovers `v ∈ {0,1}` and `Φ={φ}`.

---

## 2. The coherence spectrum (primary invariant)

Define the **coherence spectrum**:

```text
Spec^Coh_T(Φ) := { v ∈ {0,1}^n : Coh(T + Φ^v) }.
```

This subset of the Boolean cube is the **primary invariant** of the framework.

Everything else (defects, closure, openness, ordinals) is a projection or dynamic derived from this
subset-valued object.

---

## 3. Closure and openness (set-theoretic level)

All closure, openness, coordinate-closure, and defect notions below are evaluated on **inhabited**
spectra.

Treat the empty-spectrum case as a separate bottom state:

```text
Bot^Coh_T(Φ) :⇔ Spec^Coh_T(Φ) = ∅.
```

Assume `Spec^Coh_T(Φ) ≠ ∅`. Define the coarse numeric summary:

```text
D^Coh_T(Φ) := |Spec^Coh_T(Φ)| − 1.
```

Then:

- **Coh-closure on Φ**:
  ```text
  |Spec^Coh_T(Φ)| = 1
  ```
  (equivalently `D^Coh_T(Φ)=0`).

- **Coh-openness on Φ**:
  ```text
  |Spec^Coh_T(Φ)| > 1
  ```
  (equivalently `D^Coh_T(Φ)>0`).

### 3.1 Coordinates: closed vs open

For each coordinate `i ∈ {1,…,n}` define:

- `i` is **Coh-closed** if all admissible branches agree on that coordinate:
  ```text
  ∃ b ∈ {0,1} such that ∀ v ∈ Spec^Coh_T(Φ), vᵢ = b.
  ```

- `i` is **Coh-open** if both values appear among admissible branches:
  ```text
  ∃ v,w ∈ Spec^Coh_T(Φ) such that vᵢ = 0 and wᵢ = 1.
  ```

This coordinate structure is strictly richer than the coarse number `D`.

---

## 4. Monotonicity under theory extension (branch elimination)

Assume **downward heredity** for `Coh`:

```text
U ⊆ V and Coh(V) ⇒ Coh(U).
```

Then:

```text
T ⊆ S  ⇒  Spec^Coh_S(Φ) ⊆ Spec^Coh_T(Φ).
```

Interpretation:

```text
theory extension = monotone elimination of admissible branches.
```

This is the minimal “dynamics” statement: it holds in regime (B) automatically (any model of `S`
is a model of `T`), and in regime (C) exactly when downward heredity is assumed.

---

## 4bis. Comparison of coherence predicates

Let `Coh₁, Coh₂ : Theory_L → Prop` be two coherence predicates.

Define the **strength preorder** on coherence predicates by:

```text
Coh₂ ⪯ Coh₁  :⇔  ∀U, Coh₂(U) ⇒ Coh₁(U).
```

Thus `Coh₂ ⪯ Coh₁` means that `Coh₂` is the stronger, more restrictive coherence predicate.

This relation is a preorder:

```text
Coh ⪯ Coh
```

and

```text
(Coh₃ ⪯ Coh₂ and Coh₂ ⪯ Coh₁) ⇒ Coh₃ ⪯ Coh₁.
```

For fixed `T` and finite `Φ`, the spectrum construction is monotone with respect to this preorder:

```text
Coh₂ ⪯ Coh₁
⇒
Spec^{Coh₂}_T(Φ) ⊆ Spec^{Coh₁}_T(Φ).
```

Proof:

```text
v ∈ Spec^{Coh₂}_T(Φ)
⇒ Coh₂(T + Φ^v)
⇒ Coh₁(T + Φ^v)
⇒ v ∈ Spec^{Coh₁}_T(Φ).
```

Hence, whenever both spectra are finite:

```text
|Spec^{Coh₂}_T(Φ)| ≤ |Spec^{Coh₁}_T(Φ)|.
```

Equivalently, the assignment

```text
Coh ↦ Spec^Coh_T(Φ)
```

is order-preserving from the strength preorder into subset inclusion.

Or, using the opposite convention where weaker predicates are larger, it is contravariant.

## Relative comparison above a base theory

For a fixed base theory `T`, define:

```text
Coh₂ ⪯_T Coh₁
:⇔
∀U, (T ⊆ U and Coh₂(U)) ⇒ Coh₁(U).
```

Then the same comparison theorem holds:

```text
Coh₂ ⪯_T Coh₁
⇒
Spec^{Coh₂}_T(Φ) ⊆ Spec^{Coh₁}_T(Φ).
```

This relative form is useful when two coherence predicates are comparable only over extensions of the base theory under study.

## Semantic class specialization

For semantic predicates of the form

```text
Coh_C(U) := ∃M ∈ C such that M ⊨ U,
```

class inclusion induces coherence strength:

```text
C₂ ⊆ C₁
⇒
Coh_{C₂} ⪯ Coh_{C₁}.
```

Therefore:

```text
C₂ ⊆ C₁
⇒
Spec^{Coh_{C₂}}_T(Φ) ⊆ Spec^{Coh_{C₁}}_T(Φ).
```

So the slogan becomes:

```text
smaller semantic landscape
⇒ stronger coherence predicate
⇒ smaller admissible branch spectrum.
```

## Final clean positioning

The mature theorem package is:

```text
Theory extension:
T ⊆ S
⇒
Spec^Coh_S(Φ) ⊆ Spec^Coh_T(Φ).

Coherence strengthening:
Coh₂ ⪯ Coh₁
⇒
Spec^{Coh₂}_T(Φ) ⊆ Spec^{Coh₁}_T(Φ).

Semantic restriction:
C₂ ⊆ C₁
⇒
Spec^{Coh_{C₂}}_T(Φ) ⊆ Spec^{Coh_{C₁}}_T(Φ).
```

That gives the framework two independent contraction axes:

```text
add axioms to T
```

and

```text
strengthen Coh.
```

This is exactly the comparative engine the paper needs.

---

## 5. Regime (A): syntactic consistency and complete collapse on finite Φ

Let `Con_syn(U)` mean ordinary first-order syntactic consistency (“no finite proof of ⊥ from `U`”).
In this regime, a central non-slipping fact is:

```text
¬Con_syn(T + ψ) ⇔ T ⊢ ¬ψ
```

for closed sentences `ψ`, by the deduction theorem (external metatheorem), and with classical logic
double-negation elimination.

### 5.1 Collapse theorem (finite-family)

Assume:

```text
Coh := Con_syn
Con_syn(T)
Φ = {φ₁,…,φₙ} is finite.
```

Then:

```text
Spec^Con_syn_T(Φ) = {v*}
```

if and only if `T` syntactically decides every coordinate according to `v*`:

```text
for each i:
  v*_i = 1  ⇒  T ⊢ φᵢ
  v*_i = 0  ⇒  T ⊢ ¬φᵢ.
```

So, in regime (A) for **finite** `Φ`:

```text
Con_syn-closure on Φ  =  syntactic decision of all coordinates in Φ.
```

This is the precise sense in which “coherence spectra collapse to decidability” in the ordinary
syntactic-consistency regime.

Proof sketch (completion argument):

Assume `Con_syn(T)` and `Spec^{Con_syn}_T(Φ) = {v*}`. Fix a coordinate `i` and let `ε := 1 − v*_i`.

If `T + φᵢ^ε` were consistent, extend it to a complete consistent theory `Γ ⊇ T + φᵢ^ε` (Lindenbaum
completion). For each `j`, let `w_j` be the truth value assigned by `Γ` to `φⱼ`. Then `T + Φ^w` is
consistent, so `w ∈ Spec^{Con_syn}_T(Φ)`. But `w_i = ε ≠ v*_i`, contradicting uniqueness of `v*`.
Therefore `T + φᵢ^ε` is inconsistent, hence `T ⊢ φᵢ^{v*_i}`.

Conversely, if `T ⊢ φᵢ^{v*_i}` for every coordinate `i`, then the selected branch `T + Φ^{v*}` is
consistent (by `Con_syn(T)`), and any other branch contains a literal opposite to a theorem of `T`,
so is inconsistent. Hence `Spec^{Con_syn}_T(Φ) = {v*}`.

### 5.2 Limit-continuity (compactness of finitary proofs)

For an increasing chain of theories `(T_α)_{α<λ}` and a fixed finite family `Φ`, define:

```text
S_α := Spec^Con_syn_{T_α}(Φ).
```

Then the spectrum is **limit-continuous**:

```text
S_λ = ⋂_{α<λ} S_α
```

because inconsistency is witnessed by a finite proof using finitely many axioms, hence already
appearing at some stage `<λ`.

Consequence: in regime (A), a branch cannot “die for the first time” at a limit stage.

---

## 6. Regime (B): semantic coherence `Coh_C` and derived stability lemmas

Fix a class `C` of structures in the language of `T` and define:

```text
Coh_C(U) := “∃ M ∈ C such that M ⊨ U”.
```

Then several “stability assumptions” become lemmas:

- Branch-totality (for binary branching): if `M ⊨ T` then `M ⊨ φ` or `M ⊨ ¬φ`, so one branch is
  admissible.
- Downward heredity: any model of `V` is a model of all subsets `U ⊆ V`.
- Theorem stability: if `U ⊢ χ`, then any model of `U` satisfies `χ`.
- Soundness against contradiction: if `U` has a model, then `U` is syntactically consistent.

### 6.0 Semantic inhabitation (finite-family)

Let `Coh_C(U) := “∃M ∈ C such that M ⊨ U”`. For finite `Φ = {φ₁,…,φₙ}`:

```text
Spec^{Coh_C}_T(Φ) ≠ ∅
⇔
Coh_C(T).
```

Proof sketch:

- If `M ∈ C` and `M ⊨ T`, then `M` assigns each `φᵢ` a truth value. Let `v ∈ {0,1}^n` record those
  truth values. Then `M ⊨ T + Φ^v`, so `v ∈ Spec^{Coh_C}_T(Φ)`.
- Conversely, any `v ∈ Spec^{Coh_C}_T(Φ)` is witnessed by some `M ∈ C` with `M ⊨ T + Φ^v`, hence
  by a `C`-model of `T`.

### 6.0bis Semantic coordinate decision inside a class

Define relative semantic consequence:

```text
T ⊨_C χ
:⇔
every M ∈ C with M ⊨ T also satisfies χ.
```

Assume `Coh_C(T)` (equivalently `Spec^{Coh_C}_T(Φ) ≠ ∅` by Lemma 6.0). Then for each coordinate `i`
and bit `b ∈ {0,1}`:

```text
i is Coh_C-closed with value b
⇔
T ⊨_C φᵢ^b.
```

So, in regime (B) for finite `Φ`:

```text
Coh_C-closure on Φ
⇔
T semantically decides every coordinate of Φ inside C.
```

### 6.1 Canonical set-theoretic reference instance: transitive ZFC-model coherence

For set-theoretic targets (language `∈`, or theories interpreted there), a canonical reference
semantic strengthening is:

```text
C := the class of transitive models of ZFC

Coh_trZFC(U) := ∃ M (M is transitive, M ⊨ ZFC, and M ⊨ U).
```

This coherence predicate is strong enough to separate **semantic branch admissibility** from
syntactic provability in a clean canonical way (next section).

---

## 7. Canonical separation: syntactic openness vs transitive-model closure

This is the core “non-collapse” demonstration in a fully typed form.

### 7.1 Internal vs meta-level consistency sentence

The sentence `Con_syn(ZFC)` is a meta-level predicate. To use it inside `Spec`, we must choose an
arithmetized *internal* sentence. Fix a standard Gödel consistency sentence for ZFC, written:

```text
Con_ZFC := ¬Prov_ZFC(⌜⊥⌝)
```

(a Hilbert–Bernays–Löb consistency sentence for a standard arithmetization).

### 7.2 Separation statement

Assume:

```text
(H1) there exists a transitive model of ZFC.
(H2) Con_ZFC is chosen so Gödel II applies, and hence (given H1 ⇒ Con_syn(ZFC)):
     ZFC ⊬ Con_ZFC.
```

Let:

```text
T := ZFC
Φ := {Con_ZFC}  (binary case).
```

Then:

1) **Semantic closure (transitive-model coherence):**

```text
Spec^Coh_trZFC_ZFC(Con_ZFC) = {1}.
```

Reason: every transitive ZFC-model has standard `ω`, so the arithmetical proof predicate used in the
fixed arithmetization of `Con_ZFC` is absolute for the standard naturals; therefore every transitive
ZFC-model satisfies `Con_ZFC`. Hence the `¬Con_ZFC` branch has no transitive ZFC-model.

2) **Syntactic openness (ordinary consistency):**

```text
Spec^Con_syn_ZFC(Con_ZFC) = {0,1}.
```

Reason: the `Con_ZFC` branch is consistent by (H1). The `¬Con_ZFC` branch is consistent because if
`ZFC + ¬Con_ZFC` were inconsistent, then `ZFC ⊢ Con_ZFC`, contradicting Gödel II (H2).

So:

```text
D^Con_syn_ZFC(Con_ZFC) = 1
but
D^Coh_trZFC_ZFC(Con_ZFC) = 0.
```

This is the canonical separation:

```text
syntactic openness  ≠  semantic Coh-closure.
```

---

## 8. A non-compact semantic Coh that forces limit-stage drops (finite Φ, transfinite protocol time)

To see genuine **ordinal protocol-time** behavior already in the binary case, take a non-compact
semantic coherence predicate.

Let:

```text
C := finite structures in some fixed language L
Coh_fin(U) := “U has a finite model”.
```

Then one can build increasing chains `(T_n)_{n<ω}` such that both branches are admissible at every
finite stage, but one branch disappears at the limit union `T_ω`.

### 8.1 Concrete example (binary Φ, first strict drop at ω)

Language:

```text
L = {R}, where R is a unary predicate.
```

Target sentence:

```text
φ := ∃x R(x).
```

For each `k≥1`, let `σ_k` be the sentence “there exist at least k distinct elements”.

Index the protocol by `ω+1`:

```text
T_n := { ¬φ → σ_k : 1 ≤ k ≤ n }
T_ω := ⋃_{n<ω} T_n.
```

Now check admissibility in the class of finite models:

- For each `n<ω`, both branches are `Coh_fin`-admissible:
  - `T_n + φ` has a finite model: take any finite structure with `R` nonempty.
  - `T_n + ¬φ` has a finite model:
    - for `n≥1`: take a finite model of size `n` with `R` empty;
    - for `n=0`: take any one-element model with `R` empty.
- At the limit:
  - `T_ω + φ` still has a finite model (again take `R` nonempty);
  - `T_ω + ¬φ` has **no** finite model, because it implies `σ_k` for every `k`.

Therefore:

```text
Spec^Coh_fin_{T_n}(φ) = {0,1} for all n<ω,
Spec^Coh_fin_{T_ω}(φ) = {1}.
```

So a strict drop occurs first at the limit stage `ω`, and:

```text
cl^Coh_fin_π(T, φ) = ω,
```

even though there is only **one** strict drop (finite spectral height).

### 8.2 Moral

This is the model-theoretic mechanism behind the ordinal distinction:

```text
non-compact Coh  ⇒  “first strict drop at a limit stage” is possible,
so protocol-time ordinals can be transfinite even for binary Φ.
```

Concretely (the standard pattern exhibited above):

```text
S_n = {0,1} for all n<ω,
S_ω = {1}.
```

Therefore:

```text
cl^Coh_fin_π(T, φ) = ω
```

This shows: `finite Φ` does not force finite protocol time once `Coh` lacks limit-continuity.

---

## 9. Ordinal protocols and ordinal-valued invariants

Let a protocol be an increasing chain of theories indexed by an ordinal `Λ`:

```text
(T_α)_{α<Λ}, with α<β ⇒ T_α ⊆ T_β,
and at limits: T_λ := ⋃_{α<λ} T_α.
```

Define:

```text
S_α := Spec^Coh_{T_α}(Φ).
```

Assuming downward heredity, the spectrum contracts monotonically:

```text
S_0 ⊇ S_1 ⊇ … ⊇ S_α ⊇ …
```

### 9.1 Spectral height vs ordinal protocol time (do not conflate)

If `Φ` is finite, then `S_0 ⊆ {0,1}^n` is finite, hence there are only finitely many **distinct**
spectra `S_α`. So the **compressed** chain (deleting repeats) has finite length.

But the ordinal stages at which those finitely many strict drops occur may be transfinite (drops can
appear first at limit stages when `Coh` is not limit-continuous).

So:

```text
finite Φ ⇒ finite spectral height
finite Φ ⇏ finite ordinal protocol time.
```

### 9.2 Branch death time

For `v ∈ S_0`, define its death time (if it ever dies):

```text
death_π(v) := least α such that v ∉ S_α.
```

### 9.3 Closure ordinal

If the spectrum ever becomes a singleton, define:

```text
cl^Coh_π(T, Φ) := least α such that |S_α| = 1.
```

### 9.4 Stabilization ordinal

If eventual constancy occurs, define:

```text
stab^Coh_π(T, Φ) := least α such that for all β ≥ α, S_β = S_α.
```

For finite `Φ` and downward-hereditary `Coh`, stabilization is automatic once the protocol is
defined past all branch deaths. Since `S_0` is finite, each branch can die at most once, so the set
of defined death times is finite and has a maximum. Concretely:

```text
stab^Coh_π(T,Φ)
=
max( {0} ∪ { death_π(v) : v ∈ S₀ and death_π(v) exists } ).
```

### 9.5 Global elimination rank

Define:

```text
SOrd^Coh_π(T, Φ) := sup { death_π(v)+1 : v ∈ S_0 and death_π(v) exists }.
```

Here `death_π(v)` is the first stage where `v` has vanished; the term `death_π(v)+1` records the
successor rank of that elimination event (post-elimination rank). In particular, in the finite case
it is common that:

```text
stab^Coh_π(T,Φ) = max death times
but
SOrd^Coh_π(T,Φ) = sup of successor death ranks.
```

For the finite-model example in §8:

```text
death_π(0) = ω,
cl^Coh_fin_π(T,φ) = ω,
stab^Coh_fin_π(T,φ) = ω,
SOrd^Coh_fin_π(T,φ) = ω+1.
```

These are bona fide ordinal invariants of a monotone spectral contraction process.

---

## 10. When do we get genuinely transfinite spectral height?

For finite `Φ`, compressed spectral height is finite, so one cannot obtain *infinitely many strict
drops* between distinct spectra.

To obtain **genuinely transfinite spectral height**, enlarge the spectrum space:

- take `Φ` infinite (valuations in `{0,1}^ℕ` or `{0,1}^I`), or
- replace raw valuation spectra by a topological/type spectrum with a transfinite derivative process
  (Cantor–Bendixson style ranks).

This is the correct boundary between “ordinal protocol time” phenomena and “intrinsically transfinite
spectral height” phenomena.

---

## 11. Theorem index (what is proved where)

The framework supports (at least) the following clean theorem schema:

1) **Monotonicity (downward heredity):**
   ```text
   T ⊆ S ⇒ Spec^Coh_S(Φ) ⊆ Spec^Coh_T(Φ).
   ```

2) **Coherence-strength comparison (strength preorder):**
   ```text
   Coh₂ ⪯ Coh₁ ⇒ Spec^{Coh₂}_T(Φ) ⊆ Spec^{Coh₁}_T(Φ).
   ```

2) **Closure/openness by spectrum cardinality** (assuming inhabitation):
   ```text
   closure ⇔ |Spec| = 1
   openness ⇔ |Spec| > 1.
   ```

3) **Collapse in regime (A) for finite Φ:**
   ```text
   (Coh=Con_syn, Con_syn(T)) and |Spec|=1
   ⇔ T decides every coordinate in Φ.
   ```

4) **Semantic decision in regime (B) (finite Φ):**
   ```text
   (Coh=Coh_C, Coh_C(T)) and |Spec|=1
   ⇔ T semantically decides every coordinate in Φ inside C.
   ```

5) **Canonical separation (set theory):**
   ```text
   Spec^Con_syn_ZFC(Con_ZFC) = {0,1}
   but
   Spec^Coh_trZFC_ZFC(Con_ZFC) = {1},
   ```
   under (H1–H2).

6) **Ordinal protocol-time ranks**: death/closure/stability ordinals are well-defined whenever the
   corresponding minima exist along the protocol chain.

7) **Finite Φ bound**: finite spectral height after compression, but no bound on ordinal protocol
   time without extra assumptions (e.g. limit-continuity).

---

## 12. Practical reading (what the framework “changes”)

In regime (A), the spectrum viewpoint collapses to ordinary syntactic decision.

In regime (B), the spectrum viewpoint becomes a clean invariant of **semantic admissibility**:

```text
not only “what does T prove?”
but “which truth-branches survive in a chosen semantic landscape?”
```

And once protocols are allowed to be transfinite, the same object supports ordinal ranks measuring
the *timing* and *depth* of branch elimination.
