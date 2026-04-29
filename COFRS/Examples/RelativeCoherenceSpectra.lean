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

/-!
## 0ter. Scope convention for `Coh` (paper alignment, comment-only)

The markdown note `Private_notes/RELATIVE_COHERENCE_SPECTRA.md` uses a *scope convention* for the
meta-level coherence predicate `Coh`, allowing three regimes:

```text
(A) Coh := Con_syn                       (ordinary syntactic consistency)

(B) Coh := Coh_C for a fixed class C,    Coh_C(U) := “∃ M ∈ C, M ⊨ U”

(C) Coh := an abstract predicate, together with the specific stability properties
    (e.g. downward heredity) explicitly assumed in each statement.
```

This Lean file intentionally stays at the abstract level (C): `Coh` is an arbitrary predicate on
theory predicates. This keeps the development constructive and axiom-free.

The semantic material (models, satisfaction, ZFC, Gödel II) lives in the markdown note, not here.
-/

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

/-!
### Lean-native pointwise variants (avoid `funext`)

In the paper, valuations are vertices of the cube `{0,1}^n`, and “uniqueness of a valuation” is
usually read extensionally. In Lean, our valuations are functions:

```lean
Valuation n := Fin n → Bool
```

Equality of such functions is extensional. Proving it from coordinate-wise equality typically uses
function extensionality (`funext`), which depends on `Quot.sound` and is forbidden by this repo.

Therefore we introduce pointwise equality as a primitive relation, and formulate closure/openness
using it.
-/

/-- Pointwise equality of valuations (coordinate-wise equality). -/
def ValEq (v w : Valuation n) : Prop :=
  ∀ i : Fin n, v i = w i

/-- Pointwise closure: uniqueness of the admissible valuation up to `ValEq`. -/
def ClosedPt (T : Theory Sentence) (Φ : Family Sentence n) : Prop :=
  ∃ v : Valuation n,
    Spec (n := n) neg Coh T Φ v ∧
    ∀ w : Valuation n, Spec (n := n) neg Coh T Φ w → ValEq (n := n) v w

/-- Pointwise openness: existence of two admissible valuations differing at some coordinate. -/
def OpenPt (T : Theory Sentence) (Φ : Family Sentence n) : Prop :=
  ∃ v w : Valuation n,
    Spec (n := n) neg Coh T Φ v ∧
    Spec (n := n) neg Coh T Φ w ∧
    ∃ i : Fin n, v i ≠ w i

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
Coordinate openness implies pointwise openness: if both values occur at some coordinate among
admissible valuations, then there exist two admissible valuations that differ at that coordinate.

This lemma is geometrically natural and stays constructive without `funext`.
-/

theorem openPt_of_coordOpen
    {T : Theory Sentence} {Φ : Family Sentence n} {i : Fin n} :
    CoordOpen (n := n) neg Coh T Φ i →
    OpenPt (n := n) neg Coh T Φ := by
  intro h
  rcases h with ⟨h0, h1⟩
  rcases h0 with ⟨v, hv, hvi⟩
  rcases h1 with ⟨w, hw, hwi⟩
  refine ⟨v, w, hv, hw, i, ?_⟩
  intro heq
  have hfalse : (false : Bool) = true := by
    calc
      (false : Bool) = v i := hvi.symm
      _ = w i := heq
      _ = true := hwi
  cases hfalse

/-!
### Small API bridges for the pointwise layer

These lemmas make the `ValEq` / `ClosedPt` / `OpenPt` layer convenient to use while staying
axiom-free.
-/

theorem valEq_refl (v : Valuation n) : ValEq (n := n) v v := by
  intro i
  rfl

theorem valEq_symm {v w : Valuation n} :
    ValEq (n := n) v w → ValEq (n := n) w v := by
  intro h i
  exact (h i).symm

theorem valEq_trans {u v w : Valuation n} :
    ValEq (n := n) u v → ValEq (n := n) v w → ValEq (n := n) u w := by
  intro huv hvw i
  exact (huv i).trans (hvw i)

theorem specInhabited_of_closedPt {T : Theory Sentence} {Φ : Family Sentence n} :
    ClosedPt (n := n) neg Coh T Φ → SpecInhabited (n := n) neg Coh T Φ := by
  intro h
  rcases h with ⟨v, hv, _⟩
  exact ⟨v, hv⟩

theorem closedPt_of_closed {T : Theory Sentence} {Φ : Family Sentence n} :
    Closed (n := n) neg Coh T Φ → ClosedPt (n := n) neg Coh T Φ := by
  intro h
  rcases h with ⟨v, hv, huniq⟩
  refine ⟨v, hv, ?_⟩
  intro w hw i
  have hEq : w = v := huniq w hw
  -- After rewriting `w` to `v`, the goal is reflexive.
  cases hEq
  rfl

theorem coordClosed_of_closedPt
    {T : Theory Sentence} {Φ : Family Sentence n}
    (h : ClosedPt (n := n) neg Coh T Φ) :
    ∀ i : Fin n, CoordClosed (n := n) neg Coh T Φ i := by
  intro i
  rcases h with ⟨v, hv, huniq⟩
  refine ⟨v i, ?_⟩
  intro w hw
  exact (huniq w hw i).symm

theorem closedPt_of_specInhabited_of_forall_coordClosed
    {T : Theory Sentence} {Φ : Family Sentence n}
    (hInh : SpecInhabited (n := n) neg Coh T Φ)
    (hCoord : ∀ i : Fin n, CoordClosed (n := n) neg Coh T Φ i) :
    ClosedPt (n := n) neg Coh T Φ := by
  rcases hInh with ⟨v, hv⟩
  refine ⟨v, hv, ?_⟩
  intro w hw i
  rcases hCoord i with ⟨b, hb⟩
  have hvb : v i = b := hb v hv
  have hwb : w i = b := hb w hw
  exact hvb.trans hwb.symm

theorem closedPt_iff_specInhabited_and_forall_coordClosed
    {T : Theory Sentence} {Φ : Family Sentence n} :
    ClosedPt (n := n) neg Coh T Φ ↔
      SpecInhabited (n := n) neg Coh T Φ ∧
        ∀ i : Fin n, CoordClosed (n := n) neg Coh T Φ i := by
  constructor
  · intro h
    refine ⟨specInhabited_of_closedPt (n := n) (neg := neg) (Coh := Coh) h,
      coordClosed_of_closedPt (n := n) (neg := neg) (Coh := Coh) h⟩
  · intro h
    exact closedPt_of_specInhabited_of_forall_coordClosed
      (n := n) (neg := neg) (Coh := Coh) h.1 h.2

/-!
### Openness equivalences

`OpenPt` is “witnessed” openness: two admissible valuations differ at an explicit coordinate. This
is equivalent to the existence of an open coordinate.
-/

theorem exists_coordOpen_of_openPt
    {T : Theory Sentence} {Φ : Family Sentence n} :
    OpenPt (n := n) neg Coh T Φ →
    ∃ i : Fin n, CoordOpen (n := n) neg Coh T Φ i := by
  intro h
  rcases h with ⟨v, w, hv, hw, i, hdiff⟩
  refine ⟨i, ?_⟩
  cases hvi : v i with
  | false =>
      cases hwi : w i with
      | false =>
          have : v i = w i := by
            -- both sides reduce to `false`
            rw [hvi, hwi]
          exact False.elim (hdiff this)
      | true =>
          exact ⟨⟨v, hv, hvi⟩, ⟨w, hw, hwi⟩⟩
  | true =>
      cases hwi : w i with
      | true =>
          have : v i = w i := by
            -- both sides reduce to `true`
            rw [hvi, hwi]
          exact False.elim (hdiff this)
      | false =>
          -- swap the witnesses to match the `false`/`true` ordering of `CoordOpen`
          exact ⟨⟨w, hw, hwi⟩, ⟨v, hv, hvi⟩⟩

theorem openPt_iff_exists_coordOpen
    {T : Theory Sentence} {Φ : Family Sentence n} :
    OpenPt (n := n) neg Coh T Φ ↔
      ∃ i : Fin n, CoordOpen (n := n) neg Coh T Φ i := by
  constructor
  · exact exists_coordOpen_of_openPt (n := n) (neg := neg) (Coh := Coh)
  · intro h
    rcases h with ⟨i, hi⟩
    exact openPt_of_coordOpen (n := n) (neg := neg) (Coh := Coh) hi

/-!
### Safe bridge to paper-level `Open`

From a pointwise witness of difference we can derive extensional inequality (by contradiction).
The converse direction would require an extensionality principle and is therefore not part of this
axiom-free core.
-/

theorem open_of_openPt {T : Theory Sentence} {Φ : Family Sentence n} :
    OpenPt (n := n) neg Coh T Φ → Open (n := n) neg Coh T Φ := by
  intro h
  rcases h with ⟨v, w, hv, hw, i, hdiff⟩
  refine ⟨v, w, hv, hw, ?_⟩
  intro hEq
  have : v i = w i := congrArg (fun f : Valuation n => f i) hEq
  exact hdiff this

/-!
### Incompatibility lemmas (closure vs openness)

These are useful to keep the internal geometry sharp:

```text
ClosedPt excludes OpenPt
CoordClosed excludes CoordOpen
```
-/

theorem closedPt_openPt_absurd
    {T : Theory Sentence} {Φ : Family Sentence n} :
    ClosedPt (n := n) neg Coh T Φ →
    OpenPt (n := n) neg Coh T Φ →
    False := by
  intro hClosed hOpen
  rcases hClosed with ⟨u, hu, huniq⟩
  rcases hOpen with ⟨v, w, hv, hw, i, hdiff⟩
  have huv : u i = v i := huniq v hv i
  have huw : u i = w i := huniq w hw i
  have hvw : v i = w i := huv.symm.trans huw
  exact hdiff hvw

theorem coordClosed_coordOpen_absurd
    {T : Theory Sentence} {Φ : Family Sentence n} {i : Fin n} :
    CoordClosed (n := n) neg Coh T Φ i →
    CoordOpen (n := n) neg Coh T Φ i →
    False := by
  intro hClosed hOpen
  rcases hClosed with ⟨b, hb⟩
  rcases hOpen with ⟨h0, h1⟩
  rcases h0 with ⟨v, hv, hvfalse⟩
  rcases h1 with ⟨w, hw, hwtrue⟩
  have hfalse_true : (false : Bool) = true := by
    calc
      (false : Bool) = v i := hvfalse.symm
      _ = b := hb v hv
      _ = w i := (hb w hw).symm
      _ = true := hwtrue
  cases hfalse_true

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
### Enumeration brick (optional)

To relate `specCountB` to a true finite cardinality `|Spec|`, one typically needs to show that
`allValuations n` enumerates every valuation **without duplicates**.

In this repository, we deliberately avoid `funext` (it depends on `Quot.sound`) and avoid `propext`.
As a result, proving a full `NoDup` statement for *function-valued* valuations
`Valuation n := Fin n → Bool` is nontrivial.

We nevertheless record a basic structural fact that is still useful and completely constructive:
the enumeration has the expected length `2^n`.
-/

/-!
#### Axiom-free list length lemmas

The standard library lemmas `List.length_map` and `List.length_append` currently depend on `propext`
in core. Since this repository forbids `propext`, we re-prove the two length facts we need by
structural recursion.
-/

theorem length_map_noaxioms {α β : Type} (f : α → β) :
    ∀ xs : List α, (xs.map f).length = xs.length
  | [] => rfl
  | x :: xs => by
      change List.length (List.map f (x :: xs)) = List.length (x :: xs)
      dsimp [List.map, List.length]
      exact congrArg Nat.succ (length_map_noaxioms f xs)

theorem length_append_noaxioms {α : Type} :
    ∀ as bs : List α, (as ++ bs).length = as.length + bs.length
  | [], bs => by
      exact (Nat.zero_add bs.length).symm
  | a :: as, bs => by
      change List.length (List.append (a :: as) bs) = List.length (a :: as) + List.length bs
      dsimp [List.append, List.length]
      -- Goal after unfolding is:
      --   (as ++ bs).length + 1 = as.length + 1 + bs.length
      -- Use the induction hypothesis and reassociate.
      have ih := length_append_noaxioms as bs
      -- rewrite the LHS using `ih`
      rw [ih]
      -- Now solve the arithmetic reshuffling.
      -- (as.length + bs.length) + 1 = as.length + 1 + bs.length
      calc
        as.length + bs.length + 1
            = as.length + (bs.length + 1) := by
                exact Nat.add_assoc _ _ _
        _ = as.length + (1 + bs.length) := by
                -- commute `bs.length` and `1`
                rw [Nat.add_comm bs.length 1]
        _ = as.length + 1 + bs.length := by
                exact (Nat.add_assoc _ _ _).symm

theorem allValuations_length : (n : Nat) → (allValuations n).length = Nat.pow 2 n
  | 0 => by
      rfl
  | Nat.succ n => by
      -- Now compute the length of the unfolded definition using the local lemmas above.
      dsimp [allValuations]
      -- `vs := allValuations n`
      have hvs : (let vs := allValuations n
                  (vs.map (extendValuation (n := n) true) ++
                    vs.map (extendValuation (n := n) false))).length
                =
                (allValuations n).length + (allValuations n).length := by
        -- unfold `let` and use the local length lemmas (not the stdlib ones)
        dsimp
        -- length of append
        have h0 :
            ((allValuations n).map (extendValuation (n := n) true) ++
              (allValuations n).map (extendValuation (n := n) false)).length
            =
            ((allValuations n).map (extendValuation (n := n) true)).length +
              ((allValuations n).map (extendValuation (n := n) false)).length := by
          exact length_append_noaxioms _ _
        -- length of maps
        have h1 :
            ((allValuations n).map (extendValuation (n := n) true)).length = (allValuations n).length := by
          exact length_map_noaxioms _ _
        have h2 :
            ((allValuations n).map (extendValuation (n := n) false)).length = (allValuations n).length := by
          exact length_map_noaxioms _ _
        -- combine
        calc
          ((allValuations n).map (extendValuation (n := n) true) ++
              (allValuations n).map (extendValuation (n := n) false)).length
              =
              ((allValuations n).map (extendValuation (n := n) true)).length +
                ((allValuations n).map (extendValuation (n := n) false)).length := h0
          _ = (allValuations n).length + (allValuations n).length := by
                -- rewrite both summands
                rw [h1, h2]

      -- Finish with the induction hypothesis and the arithmetic identity `a + a = a * 2`.
      -- Note: `Nat.pow_succ` gives `2^(n+1) = 2^n * 2`.
      -- Our `hvs` gives `length = 2^n + 2^n`.
      -- We rewrite both sides to match.
      -- Step 1: rewrite the `let`-form length to the actual `allValuations (n+1)` length.
      -- (This is definitional after `dsimp` above.)
      -- Step 2: use IH and `Nat.mul_two`.
      -- The proof below uses explicit rewriting and local list-length lemmas.
      -- After rewriting, close by `Nat.mul_two`.
      have ih := allValuations_length n
      -- Reduce to arithmetic.
      -- We keep it explicit to avoid `simp` pulling in global lemmas.
      -- `hvs` already contains the unfolded expression, so we can rewrite directly.
      -- First, rewrite the LHS to `allValuations (Nat.succ n)`.
      -- Then substitute IH and `Nat.pow_succ`.
      -- Finally use `Nat.mul_two`.
      -- Start:
      --   (allValuations (n+1)).length = 2^(n+1)
      -- becomes:
      --   (2^n + 2^n) = 2^n * 2
      -- which is `Nat.mul_two (2^n)` symm.
      -- Implementation:
      calc
        (allValuations (Nat.succ n)).length
            =
            (allValuations n).length + (allValuations n).length := by
              -- convert from the let-form `hvs` to the definitional unfolding (no `simp`)
              change
                (let vs := allValuations n;
                  (vs.map (extendValuation (n := n) true) ++
                    vs.map (extendValuation (n := n) false))).length
                  =
                  (allValuations n).length + (allValuations n).length
              exact hvs
        _ = Nat.pow 2 n + Nat.pow 2 n := by
              -- rewrite both copies using IH
              calc
                (allValuations n).length + (allValuations n).length
                    = Nat.pow 2 n + (allValuations n).length := by
                        rw [ih]
                _ = Nat.pow 2 n + Nat.pow 2 n := by
                        rw [ih]
        _ = Nat.pow 2 n * 2 := by
              exact (Nat.mul_two (Nat.pow 2 n)).symm
        _ = Nat.pow 2 (Nat.succ n) := by
              -- rewrite `2^(n+1)` using `pow_succ`
              -- `Nat.pow_succ` gives `2^(n+1) = 2^n * 2`
              -- We rewrite the RHS using it (symmetry).
              exact (Nat.pow_succ 2 n).symm

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
**Precision note (paper vs Lean).** In this file, `specCountB` / `DefectB` are *enumeration-based*
counts of admissible **listed** valuations (using `allValuations n`). To interpret them as the
true finite cardinality `|Spec^Coh_T(Φ)|`, one additionally needs an adequacy theorem stating that
`allValuations n` enumerates every valuation without duplicates (in an equality notion compatible
with the chosen representation of valuations).

We intentionally do **not** prove that full adequacy result here, because valuations are functions
`Fin n → Bool` and proving equality of functions from pointwise equality typically uses `funext`,
which depends on `Quot.sound` and is forbidden by this repo.
-/

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
## 3ter. Functorial / order-theoretic packaging (paper `Spec^Coh_Φ`)

The paper fixes `Φ` and views

```text
T ↦ Spec^Coh_T(Φ)
```

as a contravariant assignment from theories ordered by extension into the inclusion-ordered
power-set `P({0,1}^n)`.

We keep this packaging fully explicit (no typeclass `Preorder` instances needed).
-/

/-- Fixing `Φ`, the spectrum map `Spec^Coh_Φ : Theory → P({0,1}^n)`. -/
def SpecΦ (Φ : Family Sentence n) (T : Theory Sentence) : Pow (Valuation n) :=
  SpecSet (n := n) neg Coh T Φ

/-- Contravariance (antitonicity) of `SpecΦ` under extension, assuming downward heredity. -/
theorem specΦ_antitone_of_subset
    {T S : Theory Sentence} {Φ : Family Sentence n} (hTS : Theory.Subset T S)
    (hDown : DownwardHeredity (Sentence := Sentence) (Coh := Coh)) :
    Pow.Subset (SpecΦ (n := n) neg Coh Φ S) (SpecΦ (n := n) neg Coh Φ T) := by
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
#print axioms PrimitiveHolonomy.Examples.RelativeCoherenceSpectra.specΦ_antitone_of_subset
#print axioms PrimitiveHolonomy.Examples.RelativeCoherenceSpectra.openPt_of_coordOpen
#print axioms PrimitiveHolonomy.Examples.RelativeCoherenceSpectra.closedPt_iff_specInhabited_and_forall_coordClosed
#print axioms PrimitiveHolonomy.Examples.RelativeCoherenceSpectra.openPt_iff_exists_coordOpen
#print axioms PrimitiveHolonomy.Examples.RelativeCoherenceSpectra.open_of_openPt
#print axioms PrimitiveHolonomy.Examples.RelativeCoherenceSpectra.closedPt_openPt_absurd
#print axioms PrimitiveHolonomy.Examples.RelativeCoherenceSpectra.coordClosed_coordOpen_absurd
#print axioms PrimitiveHolonomy.Examples.RelativeCoherenceSpectra.length_map_noaxioms
#print axioms PrimitiveHolonomy.Examples.RelativeCoherenceSpectra.length_append_noaxioms
#print axioms PrimitiveHolonomy.Examples.RelativeCoherenceSpectra.allValuations_length
#print axioms PrimitiveHolonomy.Examples.RelativeCoherenceSpectra.countBool_le_of_imp
#print axioms PrimitiveHolonomy.Examples.RelativeCoherenceSpectra.specCount_le_of_imp
#print axioms PrimitiveHolonomy.Examples.RelativeCoherenceSpectra.defect_le_of_subset
/- AXIOM_AUDIT_END -/
