import COFRS.Foundations
import COFRS.Examples.RelativeCoherenceSpectra

/-!
# Ordinal (protocol-time) closure ranks for coherence spectra (constructive core)

This file is the Lean-native constructive counterpart of:

- `Private_notes/ORDINAL_COHERENCE_SPECTRA.md`

It is designed to **compose** with the static spectrum core in:

- `COFRS/Examples/RelativeCoherenceSpectra.lean`

Key design choice (constructive + axiom-audited):

- We do **not** use `Ordinal` (mathlib ordinals rely on quotients/classical principles).
- Instead we work with an **abstract index type** `ι` with a preorder `≤` (protocol time).

This formalizes the part of the markdown note that is genuinely structural:

```text
protocol monotonicity (theory extension)  ⇒  spectrum antitonicity (branch elimination)
```

and provides the canonical persistence lemmas:

```text
open at a later stage  ⇒ open at all earlier stages
closed at an earlier stage + later inhabitation ⇒ closed at all later stages
```

The “least stage” ordinal ranks (`death`, `cl`, `stab`) are *definitions* in the markdown note,
but proving existence of least stages requires additional assumptions. Here we keep only the
constructive facts that are usable without classical choice.
-/

namespace PrimitiveHolonomy
namespace Examples
namespace OrdinalCoherenceSpectra

open PrimitiveHolonomy.Examples.RelativeCoherenceSpectra

universe u

variable {Sentence : Type u}
variable {n : Nat}

variable (neg : Sentence → Sentence)
variable (Coh : Theory Sentence → Prop)


/-!
## 0bis. Set-level equality for `Pow`

`Pow α` is represented as a predicate `α → Prop`. We avoid importing `Set` and we avoid
extensional equality of predicates. Instead we package *set equality* as mutual inclusion.
-/

/-- Equality of `Pow`-sets, defined as mutual inclusion. -/
def PowEq {α : Type} (A B : Pow α) : Prop :=
  Pow.Subset A B ∧ Pow.Subset B A

namespace PowEq

theorem refl {α : Type} (A : Pow α) : PowEq A A := by
  refine ⟨?_, ?_⟩ <;> intro x hx <;> exact hx

theorem symm {α : Type} {A B : Pow α} : PowEq A B → PowEq B A := by
  intro h
  exact ⟨h.2, h.1⟩

theorem trans {α : Type} {A B C : Pow α} : PowEq A B → PowEq B C → PowEq A C := by
  intro hAB hBC
  refine ⟨?_, ?_⟩
  · intro x hx
    exact hBC.1 x (hAB.1 x hx)
  · intro x hx
    exact hAB.2 x (hBC.2 x hx)

end PowEq

/-!
## 1. Protocols indexed by a preorder (protocol-time indices)

A protocol is a monotone chain of theories `T_α` indexed by an abstract preorder `(ι, ≤)`.

We keep the monotonicity assumption explicit so that all later lemmas remain constructively valid.
-/

structure Protocol (ι : Type) [Preorder ι] where
  T : ι → Theory Sentence
  mono : ∀ {α β : ι}, α ≤ β → Theory.Subset (T α) (T β)

namespace Protocol

variable {ι : Type} [Preorder ι]
variable (π : Protocol (Sentence := Sentence) (ι := ι))

/-!
## 2. Spectrum process induced by a protocol

Fix a finite family `Φ`. For each stage `α`, the spectrum is the predicate:

```text
S_α(v) :≡ Coh(T_α + Φ^v).
```

Under downward heredity of `Coh`, this yields the antitone law:

```text
α ≤ β  ⇒  S_β ⊆ S_α.
```
-/

def SpecAt (Φ : Family Sentence n) (α : ι) : Pow (Valuation n) :=
  SpecSet (n := n) neg Coh (π.T α) Φ

def SpecInhabitedAt (Φ : Family Sentence n) (α : ι) : Prop :=
  SpecInhabited (n := n) neg Coh (π.T α) Φ

def ClosedPtAt (Φ : Family Sentence n) (α : ι) : Prop :=
  ClosedPt (n := n) neg Coh (π.T α) Φ

def OpenPtAt (Φ : Family Sentence n) (α : ι) : Prop :=
  OpenPt (n := n) neg Coh (π.T α) Φ

theorem specAt_antitone_of_le
    {Φ : Family Sentence n} {α β : ι} (h : α ≤ β)
    (hDown : DownwardHeredity (Sentence := Sentence) (Coh := Coh)) :
    Pow.Subset (SpecAt (n := n) (neg := neg) (Coh := Coh) π Φ β)
      (SpecAt (n := n) (neg := neg) (Coh := Coh) π Φ α) := by
  -- `T_α ⊆ T_β` implies `Spec(T_β) ⊆ Spec(T_α)` under downward heredity.
  have hTS : Theory.Subset (π.T α) (π.T β) := π.mono h
  exact specSet_subset_of_subset (Sentence := Sentence) (n := n) (neg := neg) (Coh := Coh)
    (T := π.T α) (S := π.T β) (Φ := Φ) hTS hDown

theorem spec_antitone_at_of_le
    {Φ : Family Sentence n} {α β : ι} (h : α ≤ β)
    (hDown : DownwardHeredity (Sentence := Sentence) (Coh := Coh)) :
    ∀ v : Valuation n,
      Spec (n := n) neg Coh (π.T β) Φ v →
        Spec (n := n) neg Coh (π.T α) Φ v := by
  intro v hSpecβ
  have hTS : Theory.Subset (π.T α) (π.T β) := π.mono h
  exact spec_antitone_of_subset (Sentence := Sentence) (n := n) (neg := neg) (Coh := Coh)
    (T := π.T α) (S := π.T β) (Φ := Φ) hTS hDown v hSpecβ

/-!
## 3. Persistence lemmas (constructive protocol-time geometry)

These are the pieces used implicitly in the ordinal markdown note.

### 3.1 Openness persists backward

If two branches survive at a later stage, they also survive at every earlier stage:

```text
α ≤ β  and  OpenPtAt(β)  ⇒  OpenPtAt(α).
```
-/

theorem openPtAt_of_le
    {Φ : Family Sentence n} {α β : ι} (h : α ≤ β)
    (hDown : DownwardHeredity (Sentence := Sentence) (Coh := Coh)) :
    OpenPtAt (n := n) (neg := neg) (Coh := Coh) π Φ β →
      OpenPtAt (n := n) (neg := neg) (Coh := Coh) π Φ α := by
  intro hOpenβ
  rcases hOpenβ with ⟨v, w, hvβ, hwβ, i, hdiff⟩
  have hvα :
      Spec (n := n) neg Coh (π.T α) Φ v :=
    spec_antitone_at_of_le (Sentence := Sentence) (n := n) (neg := neg) (Coh := Coh)
      (π := π) (Φ := Φ) h hDown v hvβ
  have hwα :
      Spec (n := n) neg Coh (π.T α) Φ w :=
    spec_antitone_at_of_le (Sentence := Sentence) (n := n) (neg := neg) (Coh := Coh)
      (π := π) (Φ := Φ) h hDown w hwβ
  exact ⟨v, w, hvα, hwα, i, hdiff⟩

/-!
### 3.2 Closure persists forward under later inhabitation

If the spectrum is already pointwise closed at `α`, and the later spectrum at `β` is inhabited,
then it must also be pointwise closed at `β`:

```text
α ≤ β and ClosedPtAt(α) and SpecInhabitedAt(β)  ⇒  ClosedPtAt(β).
```

This avoids any contrapositive reasoning; it only uses:
- antitonicity `Spec_β ⊆ Spec_α`,
- the pointwise equality API (`ValEq` symmetry/transitivity),
- and a *positive* inhabitance witness at `β`.
-/

theorem closedPtAt_of_le_of_inhabited
    {Φ : Family Sentence n} {α β : ι} (h : α ≤ β)
    (hDown : DownwardHeredity (Sentence := Sentence) (Coh := Coh)) :
    ClosedPtAt (n := n) (neg := neg) (Coh := Coh) π Φ α →
    SpecInhabitedAt (n := n) (neg := neg) (Coh := Coh) π Φ β →
    ClosedPtAt (n := n) (neg := neg) (Coh := Coh) π Φ β := by
  intro hClosedα hInhβ
  rcases hClosedα with ⟨u, huα, huniqα⟩
  rcases hInhβ with ⟨v0, hv0β⟩
  have hv0α :
      Spec (n := n) neg Coh (π.T α) Φ v0 :=
    spec_antitone_at_of_le (Sentence := Sentence) (n := n) (neg := neg) (Coh := Coh)
      (π := π) (Φ := Φ) h hDown v0 hv0β
  -- We witness closure at `β` using the inhabitance witness `v0`.
  refine ⟨v0, hv0β, ?_⟩
  intro w hwβ i
  have hwα :
      Spec (n := n) neg Coh (π.T α) Φ w :=
    spec_antitone_at_of_le (Sentence := Sentence) (n := n) (neg := neg) (Coh := Coh)
      (π := π) (Φ := Φ) h hDown w hwβ
  have hu_w : ValEq (n := n) u w := huniqα w hwα
  have hu_v0 : ValEq (n := n) u v0 := huniqα v0 hv0α
  have hv0_u : ValEq (n := n) v0 u :=
    valEq_symm (n := n) (v := u) (w := v0) hu_v0
  have hv0_w : ValEq (n := n) v0 w :=
    valEq_trans (n := n) (u := v0) (v := u) (w := w) hv0_u hu_w
  exact hv0_w i

/-!
### 3.3 Immediate confinement lemma

If a stage `α` is pointwise closed with witness `u`, then every admissible valuation at any later
stage `β ≥ α` must be pointwise equal to `u`.

This expresses “once closed, the spectrum remains inside the same vertex” without needing
limit-continuity or least-stage principles.
-/

theorem valEq_of_closedPtAt_of_le
    {Φ : Family Sentence n} {α β : ι} (h : α ≤ β)
    (hDown : DownwardHeredity (Sentence := Sentence) (Coh := Coh)) :
    ClosedPtAt (n := n) (neg := neg) (Coh := Coh) π Φ α →
    ∀ v : Valuation n,
      Spec (n := n) neg Coh (π.T β) Φ v →
        ∃ u : Valuation n,
          Spec (n := n) neg Coh (π.T α) Φ u ∧ ValEq (n := n) u v := by
  intro hClosedα v hvβ
  rcases hClosedα with ⟨u, huα, huniqα⟩
  have hvα :
      Spec (n := n) neg Coh (π.T α) Φ v :=
    spec_antitone_at_of_le (Sentence := Sentence) (n := n) (neg := neg) (Coh := Coh)
      (π := π) (Φ := Φ) h hDown v hvβ
  refine ⟨u, huα, huniqα v hvα⟩


/-!
## 4. Protocol-time “ordinal” ranks as least indices (definitions)

The markdown note defines ordinal-valued ranks like `death_π`, `cl`, `stab` using “least ordinal”.

In this file we remain constructive and avoid `Ordinal`. We therefore phrase these ranks as
**least indices** in an abstract preorder `(ι, ≤)`.

We do *not* prove existence of least indices (that would require additional assumptions, e.g.
well-foundedness or choice-like principles). But once a least index is given as a hypothesis,
we can prove the standard persistence consequences constructively.
-/

/-- `IsLeast P a` means `a` is a least index satisfying `P` (in the preorder sense). -/
def IsLeast (P : ι → Prop) (a : ι) : Prop :=
  P a ∧ ∀ b : ι, P b → a ≤ b

/-- A branch `v` is dead at stage `α` if it is not admissible in the spectrum at `α`. -/
def DiesAt (π : Protocol (Sentence := Sentence) (ι := ι))
    (Φ : Family Sentence n) (v : Valuation n) (α : ι) : Prop :=
  ¬ Spec (n := n) neg Coh (π.T α) Φ v

/-- A `DeathTime` witness: `α` is a least stage at which `v` is dead (if such a stage exists). -/
def DeathTime (Φ : Family Sentence n) (v : Valuation n) (α : ι) : Prop :=
  IsLeast (P := fun a => DiesAt (Sentence := Sentence) (n := n) (neg := neg) (Coh := Coh)
    (π := π) Φ v a) α

/-- A `ClosedTime` witness: `α` is a least stage at which the spectrum is pointwise closed. -/
def ClosedTime (Φ : Family Sentence n) (α : ι) : Prop :=
  IsLeast (P := fun a => ClosedPtAt (n := n) (neg := neg) (Coh := Coh) π Φ a) α

/-- Stability from `α`: from `α` onward, no currently admissible branch is eliminated. -/
def StableFrom (π : Protocol (Sentence := Sentence) (ι := ι))
    (Φ : Family Sentence n) (α : ι) : Prop :=
  ∀ {β : ι}, α ≤ β → Pow.Subset
    (SpecAt (n := n) (neg := neg) (Coh := Coh) π Φ α)
    (SpecAt (n := n) (neg := neg) (Coh := Coh) π Φ β)

/-- A `StabTime` witness: `α` is a least stage from which stability holds (if it exists). -/
def StabTime (Φ : Family Sentence n) (α : ι) : Prop :=
  IsLeast (P := fun a => StableFrom (Sentence := Sentence) (n := n) (neg := neg) (Coh := Coh)
    (π := π) Φ a) α

/-!
### 4.1 Death persists forward

This is the constructive content of “once a branch is eliminated, it stays eliminated”.
-/

theorem diesAt_of_le_of_diesAt
    {Φ : Family Sentence n} {v : Valuation n} {α β : ι} (h : α ≤ β)
    (hDown : DownwardHeredity (Sentence := Sentence) (Coh := Coh)) :
    DiesAt (n := n) (neg := neg) (Coh := Coh) (π := π) Φ v α →
      DiesAt (n := n) (neg := neg) (Coh := Coh) (π := π) Φ v β := by
  intro hDeadα
  -- If `v ∈ S_β` then `v ∈ S_α` by antitonicity; hence `¬S_α(v)` implies `¬S_β(v)`.
  intro hSpecβ
  have hSpecα : Spec (n := n) neg Coh (π.T α) Φ v :=
    spec_antitone_at_of_le (Sentence := Sentence) (n := n) (neg := neg) (Coh := Coh)
      (π := π) (Φ := Φ) h hDown v hSpecβ
  exact hDeadα hSpecα

/-!
### 4.2 Stability gives equality of spectra on the tail

Under stability from `α`, the spectrum process is constant (as a set) on every later stage.
-/

theorem specAt_subset_of_stableFrom
    {Φ : Family Sentence n} {α β : ι} (h : α ≤ β)
    (hStable : StableFrom (Sentence := Sentence) (n := n) (neg := neg) (Coh := Coh) (π := π) Φ α) :
    Pow.Subset
      (SpecAt (n := n) (neg := neg) (Coh := Coh) π Φ α)
      (SpecAt (n := n) (neg := neg) (Coh := Coh) π Φ β) :=
  hStable h

theorem specAt_eq_of_stableFrom_of_le
    {Φ : Family Sentence n} {α β : ι} (h : α ≤ β)
    (hDown : DownwardHeredity (Sentence := Sentence) (Coh := Coh))
    (hStable : StableFrom (Sentence := Sentence) (n := n) (neg := neg) (Coh := Coh) (π := π) Φ α) :
    Pow.Subset
      (SpecAt (n := n) (neg := neg) (Coh := Coh) π Φ α)
      (SpecAt (n := n) (neg := neg) (Coh := Coh) π Φ β)
    ∧
    Pow.Subset
      (SpecAt (n := n) (neg := neg) (Coh := Coh) π Φ β)
      (SpecAt (n := n) (neg := neg) (Coh := Coh) π Φ α) := by
  refine ⟨hStable h, ?_⟩
  -- antitonicity provides the reverse inclusion
  exact specAt_antitone_of_le (Sentence := Sentence) (n := n) (neg := neg) (Coh := Coh)
    (π := π) (Φ := Φ) h hDown


/-!
### 4.2bis Stable tail equality (packaged)

We package the tail equality `S_α = S_β` as mutual inclusion (`PowEq`).
-/

theorem specAt_powEq_of_stableFrom_of_le
    {Φ : Family Sentence n} {α β : ι} (h : α ≤ β)
    (hDown : DownwardHeredity (Sentence := Sentence) (Coh := Coh))
    (hStable : StableFrom (Sentence := Sentence) (n := n) (neg := neg) (Coh := Coh) (π := π) Φ α) :
    PowEq
      (SpecAt (n := n) (neg := neg) (Coh := Coh) π Φ α)
      (SpecAt (n := n) (neg := neg) (Coh := Coh) π Φ β) := by
  have hEq := specAt_eq_of_stableFrom_of_le (Sentence := Sentence) (n := n) (neg := neg) (Coh := Coh)
    (π := π) (Φ := Φ) h hDown hStable
  exact ⟨hEq.1, hEq.2⟩
theorem stableFrom_of_le
    {Φ : Family Sentence n} {α β : ι} (h : α ≤ β)
    (hDown : DownwardHeredity (Sentence := Sentence) (Coh := Coh))
    (hStable : StableFrom (Sentence := Sentence) (n := n) (neg := neg) (Coh := Coh) (π := π) Φ α) :
    StableFrom (Sentence := Sentence) (n := n) (neg := neg) (Coh := Coh) (π := π) Φ β := by
  intro γ hβγ
  -- take `v ∈ S_β`; show `v ∈ S_γ`
  intro v hvβ
  -- `S_β ⊆ S_α` by antitonicity
  have hvα : SpecAt (n := n) (neg := neg) (Coh := Coh) π Φ α v :=
    (specAt_antitone_of_le (Sentence := Sentence) (n := n) (neg := neg) (Coh := Coh)
      (π := π) (Φ := Φ) h hDown) v hvβ
  -- `S_α ⊆ S_γ` by stability (since `α ≤ γ`)
  have hαγ : α ≤ γ :=
    Preorder.le_trans (a := α) (b := β) (c := γ) h hβγ
  exact hStable hαγ v hvα

end Protocol

end OrdinalCoherenceSpectra
end Examples
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.Examples.OrdinalCoherenceSpectra.Protocol.specAt_antitone_of_le
#print axioms PrimitiveHolonomy.Examples.OrdinalCoherenceSpectra.Protocol.openPtAt_of_le
#print axioms PrimitiveHolonomy.Examples.OrdinalCoherenceSpectra.Protocol.closedPtAt_of_le_of_inhabited
#print axioms PrimitiveHolonomy.Examples.OrdinalCoherenceSpectra.Protocol.valEq_of_closedPtAt_of_le
#print axioms PrimitiveHolonomy.Examples.OrdinalCoherenceSpectra.Protocol.diesAt_of_le_of_diesAt
#print axioms PrimitiveHolonomy.Examples.OrdinalCoherenceSpectra.Protocol.specAt_eq_of_stableFrom_of_le
#print axioms PrimitiveHolonomy.Examples.OrdinalCoherenceSpectra.Protocol.specAt_powEq_of_stableFrom_of_le
#print axioms PrimitiveHolonomy.Examples.OrdinalCoherenceSpectra.Protocol.stableFrom_of_le
/- AXIOM_AUDIT_END -/
