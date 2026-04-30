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
strict drops.

This is exactly the “finite spectral height after compression” claim, in the decidable/Boolean
regime (which is the part that can be proved without classical axioms).
-/

import COFRS.Examples.RelativeCoherenceSpectra

namespace PrimitiveHolonomy
namespace Examples
namespace FiniteSpectralHeight

open PrimitiveHolonomy.Examples.RelativeCoherenceSpectra

/-- Count how many elements of `xs` satisfy `p`. -/
def countTrue {α : Type} (xs : List α) (p : α → Bool) : Nat :=
  xs.foldl (fun acc x => if p x then acc.succ else acc) 0

/-- `q` implies `p` pointwise: whenever `q` is true, `p` is true. -/
def BoolImp {α : Type} (p q : α → Bool) : Prop :=
  ∀ x : α, q x = true → p x = true

/-- A strict drop from `p` to `q`, witnessed inside the finite list `xs`. -/
def StrictDropOn {α : Type} (xs : List α) (p q : α → Bool) : Prop :=
  ∃ x : α, x ∈ xs ∧ p x = true ∧ q x = false

/-- If `q ⇒ p` and there is a strict drop witness in `xs`, then `countTrue xs q < countTrue xs p`. -/
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
          -- x = y
          -- q y = false, p y = true.
          have hqy : q y = false := by
            -- rewrite via x=y
            simpa using hqx
          have hpy : p y = true := by
            simpa using hpx
          -- counts: q does not increment, p increments.
          dsimp [countTrue]
          -- Expand foldl step for head.
          -- countTrue (y::ys) q = countTrue ys q
          -- countTrue (y::ys) p = countTrue ys p + 1
          -- use `countBool_le_of_imp` (from RelativeCoherenceSpectra) to get `countTrue ys q ≤ countTrue ys p`.
          have hle :
              ys.foldl (fun acc z => if q z then acc.succ else acc) 0
                ≤ ys.foldl (fun acc z => if p z then acc.succ else acc) 0 := by
            -- specialize the library lemma with `p := q`, `q := p`.
            exact countBool_le_of_imp (xs := ys) (p := q) (q := p) (a := 0)
              (by intro z hz; exact hImp z hz)
          -- now finish by rewriting head contributions.
          -- left:
          have hL :
              (List.foldl (fun acc z => if q z then acc.succ else acc)
                (if q y then 1 else 0) ys)
                = ys.foldl (fun acc z => if q z then acc.succ else acc) 0 := by
            -- since q y = false
            simp [hqy]
          have hR :
              (List.foldl (fun acc z => if p z then acc.succ else acc)
                (if p y then 1 else 0) ys)
                = ys.foldl (fun acc z => if p z then acc.succ else acc) 0 + 1 := by
            -- since p y = true
            simp [hpy, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          -- rewrite and compare
          -- left = countTrue ys q
          -- right = countTrue ys p + 1
          have : ys.foldl (fun acc z => if q z then acc.succ else acc) 0
              < ys.foldl (fun acc z => if p z then acc.succ else acc) 0 + 1 := by
            exact Nat.lt_succ_of_le hle
          -- re-express countTrue
          simpa [countTrue, hqy, hpy] using this
      | tail hxmemYs =>
          -- x in ys
          have hDrop' : StrictDropOn ys p q := ⟨x, hxmemYs, hpx, hqx⟩
          have ih_lt : countTrue ys q < countTrue ys p := ih hDrop'
          -- now handle head y
          dsimp [countTrue]
          -- split on q y
          cases hqy : q y with
          | false =>
              -- left count is unchanged
              cases hpy : p y with
              | false =>
                  -- both unchanged, use IH
                  simpa [hqy, hpy, countTrue] using ih_lt
              | true =>
                  -- right increments, so still strict
                  have : countTrue ys q < countTrue ys p + 1 :=
                    Nat.lt_trans ih_lt (Nat.lt_succ_self _)
                  simpa [hqy, hpy, countTrue] using this
          | true =>
              -- q y true implies p y true, so both increment; preserve strictness by succ.
              have hpyTrue : p y = true := hImp y (by simpa using hqy)
              have : (countTrue ys q).succ < (countTrue ys p).succ := Nat.succ_lt_succ ih_lt
              simpa [hqy, hpyTrue, countTrue] using this

/-- A strict-drop chain of Boolean predicates over a fixed finite list. -/
inductive DropChain {α : Type} (xs : List α) : List (α → Bool) → Prop
  | nil : DropChain xs []
  | single (p : α → Bool) : DropChain xs [p]
  | cons {p q : α → Bool} {rest : List (α → Bool)}
      (hImp : BoolImp p q)
      (hDrop : StrictDropOn xs p q)
      (hRest : DropChain xs (q :: rest)) :
      DropChain xs (p :: q :: rest)

/-- In a strict-drop chain, the length is bounded by the initial count + 1. -/
theorem dropChain_length_le
    {α : Type} (xs : List α) :
    ∀ ps : List (α → Bool),
      DropChain xs ps →
      ∃ p0 : α → Bool,
        ps = [] ∨ (ps.head? = some p0 ∧ ps.length ≤ countTrue xs p0 + 1) := by
  intro ps h
  cases h with
  | nil =>
      refine ⟨(fun _ => false), ?_⟩
      exact Or.inl rfl
  | single p =>
      refine ⟨p, ?_⟩
      right
      refine ⟨?_, ?_⟩
      · rfl
      · -- length [p] = 1 ≤ countTrue xs p + 1
        simp [countTrue]
  | cons hImp hDrop hRest =>
      -- ps = p :: q :: rest
      rcases dropChain_length_le (ps := (q :: rest)) hRest with ⟨p0, hcase⟩
      -- here `p0` will be `q`
      -- We'll produce the bound using the strict count decrease.
      refine ⟨p, ?_⟩
      right
      refine ⟨?_, ?_⟩
      · rfl
      · -- show: length (p::q::rest) ≤ countTrue xs p + 1
        -- First get IH bound for tail.
        have htail : (q :: rest).length ≤ countTrue xs q + 1 := by
          cases hcase with
          | inl hnil =>
              cases hnil
          | inr hcons =>
              exact hcons.2
        -- Strict drop decreases count: countTrue xs q < countTrue xs p
        have hlt : countTrue xs q < countTrue xs p :=
          countTrue_lt_of_imp_and_drop (xs := xs) (p := p) (q := q) hImp hDrop
        have hle : countTrue xs q + 1 ≤ countTrue xs p := Nat.succ_le_of_lt hlt
        -- Now length:
        -- (p::q::rest).length = (q::rest).length + 1
        -- ≤ (countTrue xs q + 1) + 1
        -- ≤ countTrue xs p + 1
        have : (p :: q :: rest).length ≤ countTrue xs p + 1 := by
          -- rewrite lengths
          simp [List.length] at *
          -- from htail: 1 + rest.length ≤ countTrue xs q + 1
          -- so 2 + rest.length ≤ countTrue xs q + 2
          -- then use hle.
          have h1 : 1 + rest.length ≤ countTrue xs q + 1 := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htail
          have h2 : 2 + rest.length ≤ countTrue xs q + 2 := by
            -- add 1 to both sides
            exact Nat.succ_le_succ h1
          -- countTrue xs q + 2 ≤ countTrue xs p + 1 ?
          -- since countTrue xs q + 1 ≤ countTrue xs p, add 1.
          have h3 : countTrue xs q + 2 ≤ countTrue xs p + 1 := by
            -- rewrite as (countTrue xs q + 1) + 1 ≤ countTrue xs p + 1
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.add_le_add_right hle 1
          exact Nat.le_trans h2 h3
        exact this

end FiniteSpectralHeight
end Examples
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.Examples.FiniteSpectralHeight.countTrue_lt_of_imp_and_drop
#print axioms PrimitiveHolonomy.Examples.FiniteSpectralHeight.dropChain_length_le
/- AXIOM_AUDIT_END -/
