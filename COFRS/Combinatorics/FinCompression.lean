/-!
# Primitive Holonomy (curated): finitary compression lemmas on `Fin`

This file is intended to stay *axiom-free* and *constructive*.

It provides:
- a canonical embedding `Fin m → Fin n` for `m ≤ n`;
- a constructive pigeonhole/collision lemma for functions `Fin n → Fin m` when `m < n`.
-/

namespace PrimitiveHolonomy
namespace Combinatorics

/-- Canonical embedding `Fin m → Fin n` when `m ≤ n`. -/
def finEmbed {m n : Nat} (h : m ≤ n) : Fin m → Fin n :=
  fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

theorem finEmbed_injective {m n : Nat} (h : m ≤ n) : Function.Injective (finEmbed h) := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun x => x.val) hij

/-- The first element of `Fin (n+1)`, avoiding `OfNat` numerals. -/
def finFirst (n : Nat) : Fin (n + 1) :=
  ⟨0, Nat.succ_pos n⟩

/-- The last element of `Fin (n+1)`, avoiding `Fin.last`. -/
def finLast (n : Nat) : Fin (n + 1) :=
  ⟨n, Nat.lt_succ_self n⟩

/--
Decidable existence over `Fin n` (constructive search by induction on `n`).

This avoids triggering non-constructive reasoning when doing `by_cases` on an existential over a finite type.
-/
def decidableExistsFin {n : Nat} (P : Fin n → Prop) (decP : ∀ i, Decidable (P i)) :
    Decidable (∃ i : Fin n, P i) := by
  induction n with
  | zero =>
      refine isFalse ?_
      intro h
      rcases h with ⟨i, _⟩
      exact Fin.elim0 i
  | succ n ih =>
      let z : Fin (n + 1) := finFirst n
      cases decP z with
      | isTrue hz =>
          exact isTrue ⟨z, hz⟩
      | isFalse hz =>
          cases (ih (P := fun i : Fin n => P i.succ) (decP := fun i => decP i.succ)) with
          | isTrue h =>
              exact isTrue (Exists.elim h (fun i hi => ⟨i.succ, hi⟩))
          | isFalse h =>
              refine isFalse ?_
              intro hex
              rcases hex with ⟨i, hi⟩
              cases i with
              | mk v hv =>
                  cases v with
                  | zero =>
                      have hEq : (⟨0, hv⟩ : Fin (n + 1)) = z := by
                        apply Fin.ext
                        rfl
                      have : P z := Eq.ndrec hi hEq
                      exact hz this
                  | succ v =>
                      have hv' : v < n := Nat.lt_of_succ_lt_succ hv
                      let j : Fin n := ⟨v, hv'⟩
                      have hEq : (⟨Nat.succ v, hv⟩ : Fin (n + 1)) = j.succ := by
                        apply Fin.ext
                        rfl
                      have : P j.succ := Eq.ndrec hi hEq
                      exact h ⟨j, this⟩

private theorem fin_one_val_eq_zero (x : Fin 1) : x.val = 0 := by
  cases x with
  | mk v hv =>
      cases v with
      | zero => rfl
      | succ v =>
          have : False := Nat.not_lt_zero v (Nat.lt_of_succ_lt_succ hv)
          exact this.elim

private theorem nat_sub_one_lt_of_lt_succ {m b : Nat} (hm : 0 < m) (hb : b < m + 1) :
    b - 1 < m := by
  cases b with
  | zero =>
      rw [Nat.zero_sub 1]
      exact hm
  | succ b =>
      rw [Nat.succ_sub_one]
      exact Nat.lt_of_succ_lt_succ hb

/--
Remove one distinguished value `a : Fin (m+1)` from `Fin (m+1)` to get a map into `Fin m`.
-/
def finRemove (m : Nat) (hm : 0 < m) (a : Fin (m + 1)) : Fin (m + 1) → Fin m :=
  fun b =>
    if hlt : b.val < a.val then
      ⟨b.val, Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ a.isLt)⟩
    else
      ⟨b.val - 1, nat_sub_one_lt_of_lt_succ (m := m) hm b.isLt⟩

theorem finRemove_injective_of_ne
    {m : Nat} (hm : 0 < m) (a : Fin (m + 1))
    {b c : Fin (m + 1)}
    (hb : b ≠ a) (hc : c ≠ a)
    (hbc : finRemove m hm a b = finRemove m hm a c) : b = c := by
  have hValEq : (finRemove m hm a b).val = (finRemove m hm a c).val :=
    congrArg (fun x => x.val) hbc

  have hbv_ne : b.val ≠ a.val := by
    intro hEq
    apply hb
    apply Fin.ext
    exact hEq

  have hcv_ne : c.val ≠ a.val := by
    intro hEq
    apply hc
    apply Fin.ext
    exact hEq

  by_cases hbLt : b.val < a.val
  · by_cases hcLt : c.val < a.val
    · -- both `< a.val`
      have hbVal : (finRemove m hm a b).val = b.val := by
        dsimp [finRemove]
        rw [dif_pos hbLt]
      have hcVal : (finRemove m hm a c).val = c.val := by
        dsimp [finRemove]
        rw [dif_pos hcLt]
      have hbcVal : b.val = c.val := by
        calc
          b.val = (finRemove m hm a b).val := hbVal.symm
          _ = (finRemove m hm a c).val := hValEq
          _ = c.val := hcVal
      apply Fin.ext
      exact hbcVal

    · -- `b.val < a.val ≤ c.val` contradicts equality of removed values
      have hbVal : (finRemove m hm a b).val = b.val := by
        dsimp [finRemove]
        rw [dif_pos hbLt]
      have hcVal : (finRemove m hm a c).val = c.val - 1 := by
        dsimp [finRemove]
        rw [dif_neg hcLt]

      have ha_le_cv : a.val ≤ c.val := Nat.le_of_not_gt hcLt
      have ha_lt_cv : a.val < c.val := Nat.lt_of_le_of_ne ha_le_cv (Ne.symm hcv_ne)
      have ha_le_cv_sub : a.val ≤ c.val - 1 := Nat.le_pred_of_lt ha_lt_cv

      have hbEq : b.val = c.val - 1 := by
        calc
          b.val = (finRemove m hm a b).val := hbVal.symm
          _ = (finRemove m hm a c).val := hValEq
          _ = c.val - 1 := hcVal

      have ha_le_bv : a.val ≤ b.val := by
        rw [hbEq]
        exact ha_le_cv_sub

      exact False.elim ((Nat.not_le_of_lt hbLt) ha_le_bv)

  · have ha_le_bv : a.val ≤ b.val := Nat.le_of_not_gt hbLt
    have ha_lt_bv : a.val < b.val := Nat.lt_of_le_of_ne ha_le_bv (Ne.symm hbv_ne)

    by_cases hcLt : c.val < a.val
    · -- symmetric contradiction
      have hcVal : (finRemove m hm a c).val = c.val := by
        dsimp [finRemove]
        rw [dif_pos hcLt]
      have hbVal : (finRemove m hm a b).val = b.val - 1 := by
        dsimp [finRemove]
        rw [dif_neg hbLt]

      have ha_le_bv_sub : a.val ≤ b.val - 1 := Nat.le_pred_of_lt ha_lt_bv

      have hbEq : b.val - 1 = c.val := by
        calc
          b.val - 1 = (finRemove m hm a b).val := hbVal.symm
          _ = (finRemove m hm a c).val := hValEq
          _ = c.val := hcVal

      have ha_le_cv : a.val ≤ c.val := by
        rw [← hbEq]
        exact ha_le_bv_sub

      exact False.elim ((Nat.not_le_of_lt hcLt) ha_le_cv)

    · -- both `≥ a.val`
      have hbVal : (finRemove m hm a b).val = b.val - 1 := by
        dsimp [finRemove]
        rw [dif_neg hbLt]
      have hcVal : (finRemove m hm a c).val = c.val - 1 := by
        dsimp [finRemove]
        rw [dif_neg hcLt]

      have hsub : b.val - 1 = c.val - 1 := by
        calc
          b.val - 1 = (finRemove m hm a b).val := hbVal.symm
          _ = (finRemove m hm a c).val := hValEq
          _ = c.val - 1 := hcVal

      cases hbv : b.val with
      | zero =>
          have ha0 : a.val = 0 := by
            have : a.val ≤ 0 := by
              rw [hbv] at ha_le_bv
              exact ha_le_bv
            exact Nat.eq_zero_of_le_zero this
          exact False.elim (hb (Fin.ext (hbv.trans ha0.symm)))
      | succ bv' =>
          cases hcv : c.val with
          | zero =>
              have ha_le_cv : a.val ≤ c.val := Nat.le_of_not_gt hcLt
              have ha0 : a.val = 0 := by
                have : a.val ≤ 0 := by
                  rw [hcv] at ha_le_cv
                  exact ha_le_cv
                exact Nat.eq_zero_of_le_zero this
              exact False.elim (hc (Fin.ext (hcv.trans ha0.symm)))
          | succ cv' =>
              rw [hbv, hcv] at hsub
              have hb1 : Nat.succ bv' - 1 = bv' := Nat.succ_sub_one bv'
              have hc1 : Nat.succ cv' - 1 = cv' := Nat.succ_sub_one cv'
              have hv : bv' = cv' := by
                have hsub' := hsub
                rw [hb1, hc1] at hsub'
                exact hsub'
              apply Fin.ext
              rw [hbv, hcv]
              exact congrArg Nat.succ hv

/--
Constructive pigeonhole principle for `Fin`:
if `m < n`, any map `Fin n → Fin m` has a collision.
-/
theorem exists_ne_map_eq_of_lt_fin
    {m n : Nat} (h : m < n) (f : Fin n → Fin m) :
    ∃ i j : Fin n, i ≠ j ∧ f i = f j := by
  induction n generalizing m with
  | zero =>
      exact (Nat.not_lt_zero _ h).elim
  | succ n ih =>
      cases m with
      | zero =>
          have : False := Fin.elim0 (f (finFirst n))
          exact False.elim this
      | succ m =>
          let emb : Fin n → Fin (n + 1) := finEmbed (Nat.le_succ n)
          let last : Fin (n + 1) := finLast n
          let a : Fin (m + 1) := f last

          cases decidableExistsFin
              (P := fun i : Fin n => f (emb i) = a)
              (decP := fun i => (inferInstance : Decidable (f (emb i) = a))) with
          | isTrue hex =>
              rcases hex with ⟨i, hi⟩
              refine ⟨emb i, last, ?_, hi⟩
              intro hEq
              have hv0 : (emb i).val = last.val := congrArg (fun x => x.val) hEq
              have hv : i.val = n := by
                dsimp [emb, last, finEmbed, finLast] at hv0
                exact hv0
              exact Nat.ne_of_lt i.isLt hv
          | isFalse hex =>
              have hno : ∀ i : Fin n, f (emb i) ≠ a := by
                intro i hEq
                exact hex ⟨i, hEq⟩
              cases m with
              | zero =>
                  have hnpos : 0 < n := Nat.lt_of_succ_lt_succ h
                  let i0 : Fin n := ⟨0, hnpos⟩
                  have : f (emb i0) = a := by
                    apply Fin.ext
                    have hf0 : (f (emb i0)).val = 0 := fin_one_val_eq_zero (f (emb i0))
                    have ha0 : a.val = 0 := fin_one_val_eq_zero a
                    exact hf0.trans ha0.symm
                  exact False.elim (hno i0 this)
              | succ m =>
                  have hmpos : 0 < (m + 1) := Nat.succ_pos m
                  let down : Fin (m + 2) → Fin (m + 1) := finRemove (m := m + 1) hmpos a
                  let g : Fin n → Fin (m + 1) := fun i => down (f (emb i))
                  have hmn : (m + 1) < n := Nat.lt_of_succ_lt_succ h


                  rcases ih (m := m + 1) hmn g with ⟨i, j, hij, hg⟩
                  refine ⟨emb i, emb j, ?_, ?_⟩
                  · intro hEq
                    dsimp [emb] at hEq
                    have : i = j := finEmbed_injective (Nat.le_succ n) hEq
                    exact hij this
                  ·
                    have hfi : f (emb i) ≠ a := hno i
                    have hfj : f (emb j) ≠ a := hno j
                    exact finRemove_injective_of_ne (m := m + 1) hmpos a hfi hfj hg

end Combinatorics
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
Auto-generated: `#print axioms` for each non-private `def`/`theorem` in this file.
-/
#print axioms PrimitiveHolonomy.Combinatorics.finEmbed
#print axioms PrimitiveHolonomy.Combinatorics.finEmbed_injective
#print axioms PrimitiveHolonomy.Combinatorics.finFirst
#print axioms PrimitiveHolonomy.Combinatorics.finLast
#print axioms PrimitiveHolonomy.Combinatorics.decidableExistsFin
#print axioms PrimitiveHolonomy.Combinatorics.finRemove
#print axioms PrimitiveHolonomy.Combinatorics.finRemove_injective_of_ne
#print axioms PrimitiveHolonomy.Combinatorics.exists_ne_map_eq_of_lt_fin
/- AXIOM_AUDIT_END -/
