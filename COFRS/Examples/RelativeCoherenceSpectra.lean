/-!
# Relative Coherence Spectra (paper-isomorphic constructive core)

This file is a *Lean-native* and fully constructive formalization of the **formal core** of
`Private_notes/RELATIVE_COHERENCE_SPECTRA.md`, with matching objects and naming.

What is formalized here (constructively):

- A theory `T` as a predicate on `Sentence`.
- A finite family `Φ : Fin n → Sentence`.
- Boolean valuations `v : Fin n → Bool` (the cube `{0,1}^n`).
- Branch fragments `Φ^v`.
- Coherence spectra
  `Spec^Coh_T(Φ) ⊆ {0,1}^n`
  as a subset (i.e. predicate) on valuations.
- Closure / openness, both as:
  - uniqueness / multiplicity of admissible branches (always constructive), and
  - optional numeric defect `D := |Spec| - 1` under a *decidability* assumption for the spectrum.
- Monotonicity under extension (contravariance) assuming downward heredity of `Coh`.

What is *not* formalized here (by design, because it is syntax/meta heavy and typically classical):

- First-order syntax, provability `⊢`, ZFC, transitive models, or Gödel II.

All proofs are constructive; see the `AXIOM_AUDIT` block at the end.
-/

namespace PrimitiveHolonomy
namespace Examples
namespace RelativeCoherenceSpectra

universe u

/-!
## 0. Abstract setup

We treat "sentences" as an abstract type `Sentence`. A "theory" is a predicate on sentences.
This avoids any dependence on set extensionality lemmas (which can pull in `propext`).
-/

variable {Sentence : Type u}

/-- A theory is represented by its membership predicate on sentences. -/
abbrev Theory (Sentence : Type u) : Type u :=
  Sentence → Prop

variable {n : Nat}

/-- A finite family of sentences (indexed by `Fin n`). -/
abbrev Family (Sentence : Type u) (n : Nat) : Type u :=
  Fin n → Sentence

/-- A Boolean valuation on a finite family (a vertex of `{0,1}^n`). -/
abbrev Valuation (n : Nat) : Type :=
  Fin n → Bool

/-!
## 0bis. “Power set” codomain, ordered by inclusion

We keep the codomain `P({0,1}^n)` as a **predicate type** (no `Set` imports needed).
-/

abbrev Pow (α : Type) : Type := α → Prop

namespace Pow

def Subset {α : Type} (A B : Pow α) : Prop :=
  ∀ x : α, A x → B x

end Pow

namespace Theory

/-- Theory inclusion: `T ⊆ S` means every axiom of `T` is an axiom of `S`. -/
def Subset (T S : Theory Sentence) : Prop :=
  ∀ s : Sentence, T s → S s

/-- Theory extension by union: `T + U`. -/
def Extend (T U : Theory Sentence) : Theory Sentence :=
  fun s => T s ∨ U s

theorem subset_extend_left {T S U : Theory Sentence} (hTS : Subset T S) :
    Subset (Extend T U) (Extend S U) := by
  intro s hs
  cases hs with
  | inl hT => exact Or.inl (hTS s hT)
  | inr hU => exact Or.inr hU

end Theory

/-!
## 1. Branch fragments and spectra

We model negation at the level of sentences by an abstract operation `neg : Sentence → Sentence`.
-/

variable (neg : Sentence → Sentence)

/-!
### Literals and branch fragments (paper notation)

We follow the paper’s convention:

```text
φᵢ^1 := φᵢ
φᵢ^0 := ¬φᵢ
Φ^v := { φᵢ^{vᵢ} : i = 1..n }.
```
-/

def lit (Φ : Family Sentence n) (i : Fin n) : Bool → Sentence
  | true => Φ i
  | false => neg (Φ i)

/-- The branch fragment `Φ^v`, represented as a theory predicate. -/
def branch (Φ : Family Sentence n) (v : Valuation n) : Theory Sentence :=
  fun s => ∃ i : Fin n, s = lit (n := n) neg Φ i (v i)

variable (Coh : Theory Sentence → Prop)

/-- Membership predicate: `v ∈ Spec^Coh_T(Φ)` iff `Coh(T + Φ^v)`. -/
def Spec (T : Theory Sentence) (Φ : Family Sentence n) (v : Valuation n) : Prop :=
  Coh (Theory.Extend T (branch (n := n) neg Φ v))

/-- The spectrum as an element of `P({0,1}^n)` (i.e. a predicate on valuations). -/
def SpecSet (T : Theory Sentence) (Φ : Family Sentence n) : Pow (Valuation n) :=
  fun v => Spec (n := n) neg Coh T Φ v

/-!
### Spectrum inhabitation (paper working assumption)

The paper frequently works under the *local* assumption that the spectrum is inhabited:

```text
Spec^Coh_T(Φ) ≠ ∅.
```

We encode this as the existence of at least one admissible valuation.
-/

def SpecInhabited (T : Theory Sentence) (Φ : Family Sentence n) : Prop :=
  ∃ v : Valuation n, Spec (n := n) neg Coh T Φ v

/-!
## 2. Closure / openness (set-free, constructive)

We avoid cardinalities and finite enumeration. Instead we use:
- closure = "there is a unique admissible valuation";
- openness = "there exist two distinct admissible valuations".
-/

def Closed (T : Theory Sentence) (Φ : Family Sentence n) : Prop :=
  ∃ v : Valuation n,
    Spec (n := n) neg Coh T Φ v ∧ ∀ w : Valuation n, Spec (n := n) neg Coh T Φ w → w = v

def Open (T : Theory Sentence) (Φ : Family Sentence n) : Prop :=
  ∃ v w : Valuation n,
    Spec (n := n) neg Coh T Φ v ∧ Spec (n := n) neg Coh T Φ w ∧ v ≠ w

theorem specInhabited_of_closed {T : Theory Sentence} {Φ : Family Sentence n} :
    Closed (n := n) neg Coh T Φ → SpecInhabited (n := n) neg Coh T Φ := by
  intro h
  rcases h with ⟨v, hv, _⟩
  exact ⟨v, hv⟩

/-- Coordinate-wise closure: all admissible valuations agree at coordinate `i`. -/
def CoordClosed (T : Theory Sentence) (Φ : Family Sentence n) (i : Fin n) : Prop :=
  ∃ b : Bool, ∀ v : Valuation n, Spec (n := n) neg Coh T Φ v → v i = b

/-- Coordinate-wise openness: both Boolean values occur at coordinate `i` on admissible valuations. -/
def CoordOpen (T : Theory Sentence) (Φ : Family Sentence n) (i : Fin n) : Prop :=
  (∃ v : Valuation n, Spec (n := n) neg Coh T Φ v ∧ v i = false) ∧
  (∃ v : Valuation n, Spec (n := n) neg Coh T Φ v ∧ v i = true)

/-!
## 2bis. Optional numeric defect `D := |Spec| - 1` (requires decidability)

The paper also uses the numeric summary:

```text
D^Coh_T(Φ) := |Spec^Coh_T(Φ)| − 1
```

Computing `|Spec|` requires decidability of membership in the spectrum. We keep this *optional*:
all structural statements above and below do not depend on it.
-/

def emptyValuation : Valuation 0 := fun i => Fin.elim0 i

def extendValuation {n : Nat} (b : Bool) (v : Valuation n) : Valuation (n + 1) :=
  fun i =>
    match i with
    | ⟨0, _hm⟩ => b
    | ⟨Nat.succ k, hm⟩ =>
        have hk : k < n := Nat.lt_of_succ_lt_succ hm
        v ⟨k, hk⟩

def allValuations : (n : Nat) → List (Valuation n)
  | 0 => [emptyValuation]
  | Nat.succ n =>
      let vs := allValuations n
      (vs.map (extendValuation (n := n) true)) ++ (vs.map (extendValuation (n := n) false))

/-!
### Booleanization (to stay axiom-free)

To **compute** `|Spec|` we need decidability. In Lean, a naïve use of `DecidablePred (Spec ...)`
interacts badly with definitional equality of `Decidable` instances and can force `propext` /
`Quot.sound` into proofs about fold/count monotonicity.

This repository forbids such axioms. Therefore we expose the “decidable spectrum” as an explicit
Boolean predicate `SpecB` together with a correctness lemma.
-/

/-- A Boolean decision procedure for spectrum membership. -/
abbrev SpecB : Type :=
  Valuation n → Bool

/-- Correctness of a Boolean spectrum decision procedure. -/
def SpecB_Correct (T : Theory Sentence) (Φ : Family Sentence n) (specB : SpecB (n := n)) : Prop :=
  ∀ v : Valuation n, specB v = true ↔ Spec (n := n) neg Coh T Φ v

/-- Count admissible branches using a Boolean spectrum predicate. -/
def specCountB (_T : Theory Sentence) (_Φ : Family Sentence n) (specB : SpecB (n := n)) : Nat :=
  (allValuations n).foldl
    (fun acc v => if specB v then acc.succ else acc)
    0

/-- Numeric defect `D := |Spec| - 1`, computed via a Boolean spectrum predicate. -/
def DefectB (T : Theory Sentence) (Φ : Family Sentence n) (specB : SpecB (n := n)) : Nat :=
  (specCountB (n := n) T Φ specB) - 1

/-!
## 2ter. Spectral dependencies (relative “correlation” predicates)

The paper uses the subset `Spec^Coh_T(Φ) ⊆ {0,1}^n` as the *true* invariant, with cardinal
summaries like `D` as secondary. One simple family of refinements are “dependency predicates”
between coordinates, all defined constructively.
-/

def AlwaysSame (T : Theory Sentence) (Φ : Family Sentence n) (i j : Fin n) : Prop :=
  ∀ v : Valuation n, Spec (n := n) neg Coh T Φ v → v i = v j

def AlwaysOpposite (T : Theory Sentence) (Φ : Family Sentence n) (i j : Fin n) : Prop :=
  ∀ v : Valuation n, Spec (n := n) neg Coh T Φ v → v i = (!v j)

def VaryFreely (T : Theory Sentence) (Φ : Family Sentence n) (i j : Fin n) : Prop :=
  (∃ v : Valuation n, Spec (n := n) neg Coh T Φ v ∧ v i = false ∧ v j = false) ∧
  (∃ v : Valuation n, Spec (n := n) neg Coh T Φ v ∧ v i = false ∧ v j = true) ∧
  (∃ v : Valuation n, Spec (n := n) neg Coh T Φ v ∧ v i = true ∧ v j = false) ∧
  (∃ v : Valuation n, Spec (n := n) neg Coh T Φ v ∧ v i = true ∧ v j = true)

/-!
## 3. Monotonicity under extension

Downward heredity for coherence:
if `U ⊆ V` and `Coh(V)` then `Coh(U)`.

This yields the contravariant monotonicity:
`T ⊆ S` implies `Spec_S(Φ) ⊆ Spec_T(Φ)`.
-/

def DownwardHeredity : Prop :=
  ∀ {U V : Theory Sentence}, Theory.Subset U V → Coh V → Coh U

theorem spec_antitone_of_subset
    {T S : Theory Sentence} {Φ : Family Sentence n} (hTS : Theory.Subset T S)
    (hDown : DownwardHeredity (Sentence := Sentence) (Coh := Coh)) :
    ∀ v : Valuation n,
      Spec (n := n) neg Coh S Φ v → Spec (n := n) neg Coh T Φ v := by
  intro v hSpecS
  have hSub : Theory.Subset (Theory.Extend T (branch (n := n) neg Φ v))
                            (Theory.Extend S (branch (n := n) neg Φ v)) :=
    Theory.subset_extend_left (Sentence := Sentence) (T := T) (S := S) (U := branch (n := n) neg Φ v) hTS
  exact hDown hSub hSpecS

theorem specSet_subset_of_subset
    {T S : Theory Sentence} {Φ : Family Sentence n} (hTS : Theory.Subset T S)
    (hDown : DownwardHeredity (Sentence := Sentence) (Coh := Coh)) :
    Pow.Subset (SpecSet (n := n) neg Coh S Φ) (SpecSet (n := n) neg Coh T Φ) := by
  intro v hv
  exact spec_antitone_of_subset (Sentence := Sentence) (n := n) (neg := neg) (Coh := Coh)
    (T := T) (S := S) (Φ := Φ) hTS hDown v hv

/-!
## 3bis. Defect monotonicity (optional, requires decidability)

On the inhabited domain, the paper notes that along a chain of theory extensions, the numeric defect
`D := |Spec| - 1` is monotone decreasing. We can prove the corresponding inequality whenever
membership in both spectra is decidable.

In this file, we express “decidability” as a Boolean spectrum predicate `SpecB` with a correctness
lemma (see §2bis), in order to keep the development axiom-free.
-/

theorem countBool_mono_init {α : Type} (xs : List α) (p : α → Bool) {a b : Nat} (hab : a ≤ b) :
    xs.foldl (fun acc x => if p x then acc.succ else acc) a
      ≤ xs.foldl (fun acc x => if p x then acc.succ else acc) b := by
  induction xs generalizing a b with
  | nil =>
      exact hab
  | cons x xs ih =>
      dsimp [List.foldl]
      cases hp : p x with
      | false =>
          exact ih (a := a) (b := b) hab
      | true =>
          have hab' : a.succ ≤ b.succ := Nat.succ_le_succ hab
          exact ih (a := a.succ) (b := b.succ) hab'

theorem countBool_le_of_imp {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ x : α, p x = true → q x = true) (a : Nat) :
    xs.foldl (fun acc x => if p x then acc.succ else acc) a
      ≤ xs.foldl (fun acc x => if q x then acc.succ else acc) a := by
  induction xs generalizing a with
  | nil =>
      exact Nat.le_refl _
  | cons x xs ih =>
      dsimp [List.foldl]
      cases hp : p x with
      | false =>
          cases hq : q x with
          | false =>
              exact ih (a := a)
          | true =>
              have h0 :
                  xs.foldl (fun acc y => if p y then acc.succ else acc) a
                    ≤ xs.foldl (fun acc y => if q y then acc.succ else acc) a :=
                ih (a := a)
              have h1 :
                  xs.foldl (fun acc y => if q y then acc.succ else acc) a
                    ≤ xs.foldl (fun acc y => if q y then acc.succ else acc) a.succ :=
                countBool_mono_init (xs := xs) (p := q) (a := a) (b := a.succ) (Nat.le_succ a)
              exact Nat.le_trans h0 h1
      | true =>
          have hqTrue : q x = true := h x hp
          cases hq : q x with
          | false =>
              -- contradiction: true = false
              have htf : (true : Bool) = false := hqTrue.symm.trans hq
              cases htf
          | true =>
              exact ih (a := a.succ)

theorem specCount_le_of_imp
    {T S : Theory Sentence} {Φ : Family Sentence n}
    {specBT : SpecB (n := n)}
    {specBS : SpecB (n := n)}
    (h : ∀ v : Valuation n, specBS v = true → specBT v = true) :
    specCountB (n := n) S Φ specBS ≤ specCountB (n := n) T Φ specBT := by
  -- the lemma is purely combinatorial on the finite list of valuations
  unfold specCountB
  exact countBool_le_of_imp (xs := allValuations n) (p := specBS) (q := specBT) h 0

theorem defect_le_of_imp
    {T S : Theory Sentence} {Φ : Family Sentence n}
    {specBT : SpecB (n := n)}
    {specBS : SpecB (n := n)}
    (h : ∀ v : Valuation n, specBS v = true → specBT v = true) :
    DefectB (n := n) S Φ specBS ≤ DefectB (n := n) T Φ specBT := by
  unfold DefectB
  exact Nat.sub_le_sub_right (specCount_le_of_imp (n := n) (Sentence := Sentence) (Φ := Φ) h) 1

theorem defect_le_of_subset
    {T S : Theory Sentence} {Φ : Family Sentence n}
    {specBT : SpecB (n := n)}
    {specBS : SpecB (n := n)}
    (hSpecS : SpecB_Correct (n := n) (Sentence := Sentence) (neg := neg) (Coh := Coh) S Φ specBS)
    (hSpecT : SpecB_Correct (n := n) (Sentence := Sentence) (neg := neg) (Coh := Coh) T Φ specBT)
    (hTS : Theory.Subset T S)
    (hDown : DownwardHeredity (Sentence := Sentence) (Coh := Coh)) :
    DefectB (n := n) S Φ specBS ≤ DefectB (n := n) T Φ specBT := by
  apply defect_le_of_imp (n := n) (Sentence := Sentence) (Φ := Φ)
  intro v hvS
  have hPropS : Spec (n := n) neg Coh S Φ v := (hSpecS v).1 hvS
  have hPropT : Spec (n := n) neg Coh T Φ v :=
    spec_antitone_of_subset (Sentence := Sentence) (n := n) (neg := neg) (Coh := Coh)
      (T := T) (S := S) (Φ := Φ) hTS hDown v hPropS
  exact (hSpecT v).2 hPropT

end RelativeCoherenceSpectra
end Examples
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.Examples.RelativeCoherenceSpectra.spec_antitone_of_subset
#print axioms PrimitiveHolonomy.Examples.RelativeCoherenceSpectra.countBool_le_of_imp
#print axioms PrimitiveHolonomy.Examples.RelativeCoherenceSpectra.specCount_le_of_imp
#print axioms PrimitiveHolonomy.Examples.RelativeCoherenceSpectra.defect_le_of_subset
/- AXIOM_AUDIT_END -/
