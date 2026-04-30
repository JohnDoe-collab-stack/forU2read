import COFRS.Examples.RelativeCoherenceSpectra

/-!
# Finite compressed spectral height for Boolean spectra (constructive combinatorics)

This file provides the purely combinatorial lemma used implicitly in
`Private_notes/ORDINAL_COHERENCE_SPECTRA.md`:

```text
finite Φ ⇒ finite number of strict drops between distinct spectra
```

In a constructive setting, we phrase this for **Boolean** spectra over a fixed finite list `xs`.

- A “spectrum” is a Boolean predicate `p : α → Bool`.
- `p` is *pointwise stronger* than `q` if `q x = true → p x = true` for all `x`.
- A *strict drop* from `p` to `q` (relative to `xs`) means there exists a witness in `xs` where
  `p` holds but `q` fails.

Then every strict drop decreases the Boolean count on `xs`, hence there can be only finitely many
strict drops. This is the constructive core of “finite compressed spectral height”.
-/

namespace PrimitiveHolonomy
namespace Examples
namespace FiniteSpectralHeight

open PrimitiveHolonomy.Examples.RelativeCoherenceSpectra

/-- Count how many elements of `xs` satisfy `p`. -/
def countTrue {α : Type} (xs : List α) (p : α → Bool) : Nat :=
  match xs with
  | [] => 0
  | x :: xs =>
      match p x with
      | true => Nat.succ (countTrue xs p)
      | false => countTrue xs p

/-- `q` implies `p` pointwise: whenever `q` is true, `p` is true. -/
def BoolImp {α : Type} (p q : α → Bool) : Prop :=
  ∀ x : α, q x = true → p x = true

/-- A strict drop from `p` to `q`, witnessed inside the finite list `xs`. -/
def StrictDropOn {α : Type} (xs : List α) (p q : α → Bool) : Prop :=
  ∃ x : α, x ∈ xs ∧ p x = true ∧ q x = false

namespace countTrue

theorem cons_false {α : Type} (xs : List α) (p : α → Bool) (x : α) (hx : p x = false) :
    countTrue (x :: xs) p = countTrue xs p := by
  -- `p x = false` ⇒ head does not increment the accumulator
  dsimp [countTrue]
  rw [hx]

theorem cons_true {α : Type} (xs : List α) (p : α → Bool) (x : α) (hx : p x = true) :
    countTrue (x :: xs) p = (countTrue xs p).succ := by
  -- `p x = true` ⇒ head increments once.
  dsimp [countTrue]
  rw [hx]

theorem le_of_imp
    {α : Type} (xs : List α) (p q : α → Bool)
    (hImp : BoolImp p q) :
    countTrue xs q ≤ countTrue xs p := by
  induction xs with
  | nil =>
      exact Nat.le_refl 0
  | cons x xs ih =>
      dsimp [countTrue]
      cases hqx : q x with
      | false =>
          -- left does not increment
          cases hpx : p x with
          | false =>
              -- both sides do not increment
              exact ih
          | true =>
              -- right increments
              exact Nat.le_trans ih (Nat.le_succ _)
      | true =>
          -- q x = true ⇒ p x = true by implication
          have hpx : p x = true := hImp x hqx
          -- both sides increment
          rw [hpx]
          exact Nat.succ_le_succ ih

end countTrue

/-!
## Strict drop ⇒ strict decrease of the finite count

If `q ⇒ p` and there exists an `x ∈ xs` with `p x = true` and `q x = false`, then `q` counts
strictly fewer witnesses than `p` on `xs`.
-/

theorem countTrue_lt_of_imp_and_drop
    {α : Type} (xs : List α) (p q : α → Bool)
    (hImp : BoolImp p q)
    (hDrop : StrictDropOn xs p q) :
    countTrue xs q < countTrue xs p := by
  induction xs with
  | nil =>
      rcases hDrop with ⟨x, hx, _⟩
      cases hx
  | cons y ys ih =>
      rcases hDrop with ⟨x, hxmem, hpx, hqx⟩
      cases hxmem with
      | head =>
          -- witness is the head
          have hqy : q y = false := hqx
          have hpy : p y = true := hpx
          -- tail monotonicity: countTrue ys q ≤ countTrue ys p
          have hle :
              countTrue ys q ≤ countTrue ys p := by
            exact countTrue.le_of_imp (xs := ys) (p := p) (q := q) hImp
          -- Now: countTrue (y::ys) q = countTrue ys q
          -- and countTrue (y::ys) p = succ (countTrue ys p).
          have hL : countTrue (y :: ys) q = countTrue ys q :=
            countTrue.cons_false (xs := ys) (p := q) (x := y) hqy
          have hR : countTrue (y :: ys) p = (countTrue ys p).succ :=
            countTrue.cons_true (xs := ys) (p := p) (x := y) hpy
          -- conclude: countTrue ys q < succ (countTrue ys p)
          have : countTrue ys q < (countTrue ys p).succ := Nat.lt_succ_of_le hle
          -- rewrite the goal into the tail inequality, without using `simp` on propositions.
          rw [hL, hR]
          exact this
      | tail =>
          rename_i hxmem_in_ys
          -- witness in the tail
          have hDrop' : StrictDropOn ys p q := ⟨x, hxmem_in_ys, hpx, hqx⟩
          have ih_lt : countTrue ys q < countTrue ys p := ih hDrop'
          -- split on q y
          cases hqy : q y with
          | false =>
              -- left does not increment
              have hL : countTrue (y :: ys) q = countTrue ys q :=
                countTrue.cons_false (xs := ys) (p := q) (x := y) hqy
              -- right may increment or not; either way it is ≥ countTrue ys p
              cases hpy : p y with
              | false =>
                  have hR : countTrue (y :: ys) p = countTrue ys p :=
                    countTrue.cons_false (xs := ys) (p := p) (x := y) hpy
                  rw [hL, hR]
                  exact ih_lt
              | true =>
                  have hR : countTrue (y :: ys) p = (countTrue ys p).succ :=
                    countTrue.cons_true (xs := ys) (p := p) (x := y) hpy
                  have : countTrue ys q < (countTrue ys p).succ :=
                    Nat.lt_trans ih_lt (Nat.lt_succ_self _)
                  rw [hL, hR]
                  exact this
          | true =>
              -- q y = true ⇒ p y = true by implication; both sides increment, preserve strictness by succ.
              have hpyTrue : p y = true := hImp y hqy
              have hL : countTrue (y :: ys) q = (countTrue ys q).succ :=
                countTrue.cons_true (xs := ys) (p := q) (x := y) hqy
              have hR : countTrue (y :: ys) p = (countTrue ys p).succ :=
                countTrue.cons_true (xs := ys) (p := p) (x := y) hpyTrue
              have : (countTrue ys q).succ < (countTrue ys p).succ := Nat.succ_lt_succ ih_lt
              rw [hL, hR]
              exact this

/-!
## Drop chains and finite height

A strict-drop chain is a finite sequence of spectra where each transition is a strict drop.

The number of strict drops is bounded by the initial count, hence finite.
-/

inductive DropChain {α : Type} (xs : List α) : (α → Bool) → List (α → Bool) → Prop
  | nil (p : α → Bool) : DropChain xs p []
  | step {p q : α → Bool} {rest : List (α → Bool)}
      (hImp : BoolImp p q)
      (hDrop : StrictDropOn xs p q)
      (hRest : DropChain xs q rest) :
      DropChain xs p (q :: rest)

theorem dropChain_len_le
    {α : Type} (xs : List α) :
    ∀ (p : α → Bool) (rest : List (α → Bool)),
      DropChain xs p rest →
        rest.length ≤ countTrue xs p := by
  intro p rest h
  induction h with
  | nil =>
      -- `rest = []` by construction, so `rest.length = 0`.
      exact Nat.zero_le _
  | step hImp hDrop hRest ih =>
      rename_i p0 q0 rest0
      have hlt : countTrue xs q0 < countTrue xs p0 :=
        countTrue_lt_of_imp_and_drop (xs := xs) (p := p0) (q := q0) hImp hDrop
      have hle : Nat.succ (countTrue xs q0) ≤ countTrue xs p0 := Nat.succ_le_of_lt hlt
      have hstep : Nat.succ rest0.length ≤ Nat.succ (countTrue xs q0) := Nat.succ_le_succ ih
      have : Nat.succ rest0.length ≤ countTrue xs p0 := Nat.le_trans hstep hle
      -- goal is `(q0 :: rest0).length ≤ countTrue xs p0`
      -- and `(q0 :: rest0).length = Nat.succ rest0.length` by definition.
      change Nat.succ rest0.length ≤ countTrue xs p0
      exact this

end FiniteSpectralHeight
end Examples
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.Examples.FiniteSpectralHeight.countTrue_lt_of_imp_and_drop
#print axioms PrimitiveHolonomy.Examples.FiniteSpectralHeight.dropChain_len_le
/- AXIOM_AUDIT_END -/
