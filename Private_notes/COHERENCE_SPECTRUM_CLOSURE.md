# Coherence Spectrum Closure Invariant (Logic / ZFC-level)

This note records a **non-slipping** formulation of a “closure invariant” at the level of a chosen
**meta-level coherence predicate**. It also makes explicit when the spectrum **collapses** to ordinary
syntactic decidability (deduction-theorem regime).

## 0. Setup (meta-level)

- `T` : a (classical) first-order theory.
- `φ` : a **closed sentence** of the language of `T`.
- `Coh(U)` : a meta-theoretic predicate (a “coherence” notion) specified explicitly below.
- Working assumption: `Coh(T)`.

> Important: there are **two distinct regimes**. If you do not separate them, the statement becomes
> ambiguous and invites false inferences.

## 0bis. Two readings of “consistency”

### A) Ordinary syntactic consistency (deduction-theorem regime)

Let `Con_syn(U)` mean: “there is **no finite formal derivation of** `⊥` from `U`” in a fixed classical
first-order proof system (and write `¬φ := φ → ⊥`).

Then (external metatheorem: deduction theorem), for sentences `φ`:

```text
¬Con_syn(T + φ)   ⇔   T ⊢ ¬φ
¬Con_syn(T + ¬φ)  ⇔   T ⊢ ¬¬φ
```

and with classical logic:

```text
T ⊢ ¬¬φ  ⇔  T ⊢ φ.
```

So under `Con_syn(T)`, the spectrum below **collapses** to syntactic provability/decidability.

### B) Stronger “coherence” predicates (non-collapse regime)

Many foundational uses require a predicate stronger or different in kind than `Con_syn`, e.g.:

```text
Coh(U) := “U has a transitive model”
Coh(U) := “U has an ω-model”
Coh(U) := “U is consistent relative to a designated semantic class”
```

For such `Coh`, the equivalences with `T ⊢ φ` may fail. This is the regime where the spectrum view
does **not** reduce to syntactic decidability.

## 0ter. A standard “semantic” Coh and derived stability lemmas (recommended)

If you want `Coh` to carry *semantic* content (and to avoid treating “stability assumptions” as axioms),
the cleanest move is to define `Coh` from an explicit class of models.

Fix a class `C` of structures for the language of `T` (examples: transitive models of set theory,
ω-models, models produced by a forcing class, admissible sets, etc.). Define:

```text
Coh_C(U) := “there exists M ∈ C such that M ⊨ U”.
```

Then the “minimal stability assumptions” that one is tempted to postulate are *lemmas*:

**(L1) Branch-totality (derived):**

```text
Coh_C(T) ⇒ Coh_C(T+φ) or Coh_C(T+¬φ).
```

Reason: if `M ⊨ T`, then (classical semantics) `M ⊨ φ` or `M ⊨ ¬φ`, so the same witness `M` proves one branch
coherent.

**(L2) Downward heredity (derived):**

```text
If U ⊆ V and Coh_C(V), then Coh_C(U).
```

Reason: any model of `V` is a model of every subset `U`.

**(L3) Theorem stability (derived):**

```text
If Coh_C(U) and U ⊢ χ, then Coh_C(U+χ).
```

Reason: by soundness, any model of `U` satisfies `χ`, hence is also a model of `U+χ`.

**(L4) Soundness against contradiction (derived):**

```text
Coh_C(U) ⇒ Con_syn(U).
```

Reason: if `U` had a syntactic contradiction proof, soundness would imply no model exists.

In short: in the semantic regime, you can keep the note fully precise by (i) fixing `C`, (ii) setting
`Coh := Coh_C`, and (iii) treating these properties as derived facts rather than extra axioms.

## 1. Binary coherence spectrum

Define:

- `φ¹ := φ`
- `φ⁰ := ¬φ`

Then define the **coherence spectrum**:

```text
Spec^Coh_T(φ) := { v ∈ {0,1} : Coh(T + φᵛ) }.
```

Here `Coh` is fixed externally. If you take `Coh := Con_syn`, you are in regime A and the spectrum
collapses to syntactic decidability. If you take a stronger `Coh`, you are in regime B.

## 2. Closure defect (binary invariant)

Define the **closure defect**:

```text
D^Coh_T(φ) := |Spec^Coh_T(φ)| − 1.
```

Under `Coh(T)`, we have `Spec^Coh_T(φ) ≠ ∅`, hence:

```text
|Spec^Coh_T(φ)| ∈ {1,2}
and therefore
D^Coh_T(φ) ∈ {0,1}.
```

Interpretation:

- **Closure**:
  ```text
  D^Coh_T(φ)=0  ⇔  |Spec^Coh_T(φ)|=1
  ```
  i.e. **exactly one** of `T+φ` and `T+¬φ` is consistent.

- **Openness**:
  ```text
  D^Coh_T(φ)=1  ⇔  Spec^Coh_T(φ) = {0,1}
  ```
  i.e. **both** `T+φ` and `T+¬φ` are consistent.

## 3. One-way link to provability (safe direction only)

In regime B (stronger coherence predicates), the following implications are the “safe” ones to use:

```text
T ⊢ φ   ⇒  Spec^Coh_T(φ) = {1}.
T ⊢ ¬φ  ⇒  Spec^Coh_T(φ) = {0}.
```

In regime A (`Con = Con_syn`), the converses hold by the deduction theorem (so the spectrum collapses to
syntactic decidability). In regime B, the converses need not hold.

### Common pitfall: collapsing `Con` into `⊢`

It is tempting to write:

```text
¬Coh(T+φ)  ⇔  T ⊢ ¬φ
```

This is correct **only** when `Coh := Con_syn` (regime A). In regime B, it can fail and must not be
assumed.

## 4. Dynamics by extension (protocol view)

Let a protocol build a chain of theories:

```text
T₀ := T
T_{t+1} := T_t + ψ_t
```

Assume the protocol stays inside consistent theories:

```text
Coh(T_t) for all t.
```

Then **monotonicity** holds:

```text
Spec^Coh_{T_{t+1}}(φ) ⊆ Spec^Coh_{T_t}(φ)
and therefore
D^Coh_{T_{t+1}}(φ) ≤ D^Coh_{T_t}(φ).
```

Define the **killed branch set** and the **drop**:

```text
K^Coh_t(φ) := Spec^Coh_{T_t}(φ) \ Spec^Coh_{T_{t+1}}(φ)
Δ^Coh_t(φ) := D^Coh_{T_t}(φ) − D^Coh_{T_{t+1}}(φ) ∈ {0,1}.
```

In the binary coherent regime:

```text
Δ^Coh_t(φ)=1  ⇔  exactly one coherent branch is eliminated (|K^Coh_t(φ)|=1).
```

## 5. Core slogan (precise)

```text
Closure of φ relative to T
=
uniqueness of the coherent branch.

Openness of φ relative to T
=
persistence of both coherent branches.
```

Equivalently:

```text
“A protocol closes φ”  ⇔  it eliminates all but one branch in Spec^Coh_T(φ).
```

## 6. Optional examples (only as relative-consistency readings)

- These examples are meaningful **only after** choosing `Coh` (regime B). A canonical choice is:
  ```text
  Coh(U) := “U has a transitive model”
  ```

- If one accepts standard relative-consistency results under the chosen `Coh`, then “`CH` is open over `ZFC`”
  can be read as:
  ```text
  Spec^Coh_ZFC(CH) = {0,1}  hence  D^Coh_ZFC(CH)=1
  ```
  but this is a meta-level claim and depends on relative consistency assumptions.

- Similarly:
  ```text
  D^Coh_ZF(AC)=1  and  D^Coh_ZFC(AC)=0
  ```
  read as “AC is open over ZF but closed over ZFC”, again at the meta-level.
