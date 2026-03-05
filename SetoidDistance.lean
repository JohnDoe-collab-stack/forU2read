import forU2read.main

/-!
# Setoid-only distance on the probe quotient (no `Quot`)

This file formalizes the following setoid-first idea (constructively, with no `Quot`):

*The operational quotient is a `Setoid R`. A “distance on the quotient” is therefore a function
`d : α → α → D` that is constant on `R`-equivalence classes in each argument.*

Once `d` respects the setoid, any algebraic law stated on representatives (triangle inequality,
symmetry, separation, …) is stable under changing representatives, i.e. it “descends” to the
quotient in the setoid-only sense.
-/

universe u v w

namespace PrimitiveHolonomy

section SetoidOnly

variable {α : Type u}

/-!
## 1) Well-definedness on a setoid quotient
-/

/-- `d` is well-defined on the setoid-quotient `α / R` iff it is invariant under `R` in both args. -/
def RespectsSetoid {β : Sort w} (R : Setoid α) (d : α → α → β) : Prop :=
  ∀ ⦃x x' y y' : α⦄, R.r x x' → R.r y y' → d x y = d x' y'

/-!
## 2) Triangle inequality: stability under changing representatives

We avoid equality of propositions (which would require `propext`) and use `↔`.
-/

section Triangle

variable {D : Type v} [LE D] [Add D]
variable (R : Setoid α) (d : α → α → D)

/-- Triangle inequality on representatives. -/
def Triangle : Prop :=
  ∀ x y z : α, d x z ≤ d x y + d y z

theorem triangle_transport
    (hresp : RespectsSetoid (α := α) R d)
    {x x' y y' z z' : α}
    (hx : R.r x x') (hy : R.r y y') (hz : R.r z z') :
    (d x z ≤ d x y + d y z) ↔ (d x' z' ≤ d x' y' + d y' z') := by
  have hxz : d x z = d x' z' := hresp hx hz
  have hxy : d x y = d x' y' := hresp hx hy
  have hyz : d y z = d y' z' := hresp hy hz
  constructor
  · intro h
    simpa [hxz, hxy, hyz] using h
  · intro h
    simpa [hxz.symm, hxy.symm, hyz.symm] using h

theorem triangle_descends
    (hresp : RespectsSetoid (α := α) R d)
    (htri : Triangle (α := α) d)
    {x x' y y' z z' : α}
    (hx : R.r x x') (hy : R.r y y') (hz : R.r z z') :
    d x' z' ≤ d x' y' + d y' z' := by
  have h : d x z ≤ d x y + d y z := htri x y z
  exact (triangle_transport (R := R) (d := d) hresp hx hy hz).1 h

end Triangle

/-!
## 3) Canonical discrete distance on a decidable setoid

To get a numeric (Nat-valued) “discrete distance”, we assume `[DecidableRel R.r]`.
-/

section DiscreteNat

variable (R : Setoid α) [DecidableRel R.r]

/-- Discrete distance induced by a decidable setoid: `0` on-equivalence, `1` otherwise. -/
def discreteDist : α → α → Nat :=
  fun x y => if R.r x y then 0 else 1

theorem discreteDist_respectsSetoid :
    RespectsSetoid (α := α) R (discreteDist (R := R)) := by
  intro x x' y y' hx hy
  unfold discreteDist
  by_cases hxy : R.r x y
  · have hx'y' : R.r x' y' :=
      R.iseqv.trans (R.iseqv.trans (R.iseqv.symm hx) hxy) hy
    rw [if_pos hxy, if_pos hx'y']
  · have hx'y' : ¬ R.r x' y' := by
      intro hx'y'
      have : R.r x y :=
        R.iseqv.trans (R.iseqv.trans hx hx'y') (R.iseqv.symm hy)
      exact hxy this
    rw [if_neg hxy, if_neg hx'y']

theorem discreteDist_refl (x : α) : discreteDist (R := R) x x = 0 := by
  unfold discreteDist
  rw [if_pos (R.iseqv.refl x)]

theorem discreteDist_symm (x y : α) :
    discreteDist (R := R) x y = discreteDist (R := R) y x := by
  unfold discreteDist
  by_cases hxy : R.r x y
  · have hyx : R.r y x := R.iseqv.symm hxy
    rw [if_pos hxy, if_pos hyx]
  · have hyx : ¬ R.r y x := by
      intro hyx
      exact hxy (R.iseqv.symm hyx)
    rw [if_neg hxy, if_neg hyx]

theorem discreteDist_triangle (x y z : α) :
    discreteDist (R := R) x z ≤ discreteDist (R := R) x y + discreteDist (R := R) y z := by
  unfold discreteDist
  by_cases hxz : R.r x z
  · rw [if_pos hxz]
    exact Nat.zero_le _
  · by_cases hxy : R.r x y
    · by_cases hyz : R.r y z
      · exact False.elim (hxz (R.iseqv.trans hxy hyz))
      · rw [if_neg hxz, if_pos hxy, if_neg hyz]
    ·
      rw [if_neg hxz, if_neg hxy]
      -- goal: `1 ≤ 1 + (if R.r y z then 0 else 1)`
      exact Nat.le_add_right 1 (if R.r y z then 0 else 1)

theorem discreteDist_zero_iff (x y : α) :
    discreteDist (R := R) x y = 0 ↔ R.r x y := by
  unfold discreteDist
  by_cases hxy : R.r x y
  · constructor
    · intro _h0
      exact hxy
    · intro _h
      rw [if_pos hxy]
  · constructor
    · intro h0
      rw [if_neg hxy] at h0
      cases h0
    · intro h
      exact False.elim (hxy h)

end DiscreteNat

/-!
## 4) Packaging: a setoid-first “metric” and its induced notions

We now package the setoid-first viewpoint as a structure and re-introduce the usual metric
constructions (balls / topology / Cauchy) in a form that is *intrinsically* compatible with
the operational quotient `R`.

Everything remains setoid-only: we never form `α / R` as a type.
-/

section SetoidMetricPack

variable {D : Type v} [Preorder D] [Add D] [Zero D]

/-- A metric-like structure whose separation axiom is relative to a setoid `R` (setoid-first). -/
structure SetoidMetric (R : Setoid α) where
  d : α → α → D
  respects : RespectsSetoid (α := α) R d
  symm : ∀ x y, d x y = d y x
  tri : ∀ x y z, d x z ≤ d x y + d y z
  sep : ∀ x y, d x y = 0 ↔ R.r x y

namespace SetoidMetric

variable {R : Setoid α} (M : SetoidMetric (α := α) (D := D) R)

theorem d_self (x : α) : M.d x x = 0 :=
  (M.sep x x).2 (R.iseqv.refl x)

theorem d_eq_zero_iff (x y : α) : M.d x y = 0 ↔ R.r x y :=
  M.sep x y

end SetoidMetric

/-!
### Balls and saturation
-/

/-- Pointwise equivalence of sets (constructive stand-in for set equality). -/
def SetEq (U V : Set α) : Prop := ∀ x, x ∈ U ↔ x ∈ V

/-- `U` is `R`-saturated (closed under changing representatives). -/
def IsSat (R : Setoid α) (U : Set α) : Prop :=
  ∀ ⦃x y : α⦄, x ∈ U → R.r x y → y ∈ U

/-- Saturation of a set under a setoid. -/
def Sat (R : Setoid α) (U : Set α) : Set α :=
  { x | ∃ y, y ∈ U ∧ R.r y x }

theorem subset_sat (R : Setoid α) (U : Set α) : U ⊆ Sat (α := α) R U := by
  intro x hx
  refine ⟨x, hx, R.iseqv.refl x⟩

theorem sat_isSat (R : Setoid α) (U : Set α) : IsSat (α := α) R (Sat (α := α) R U) := by
  intro x z hx hz
  rcases hx with ⟨y, hyU, hyx⟩
  refine ⟨y, hyU, R.iseqv.trans hyx hz⟩

namespace SetoidMetric

variable {R : Setoid α} (M : SetoidMetric (α := α) (D := D) R)

/-- Open ball on representatives. -/
def Ball (x : α) (r : D) : Set α :=
  { y | M.d x y < r }

theorem ball_isSat_right (x : α) (r : D) : IsSat (α := α) R (M.Ball x r) := by
  intro y y' hy hyR
  have hx : R.r x x := R.iseqv.refl x
  have hxy : M.d x y = M.d x y' := M.respects hx hyR
  -- rewrite the inequality using `hxy`
  simpa [SetoidMetric.Ball, hxy] using hy

theorem ball_congr_left {x x' : α} (hx : R.r x x') (r : D) :
    SetEq (α := α) (M.Ball x r) (M.Ball x' r) := by
  intro y
  have hy : R.r y y := R.iseqv.refl y
  have hxy : M.d x y = M.d x' y := M.respects hx hy
  constructor <;> intro h <;> simpa [SetoidMetric.Ball, hxy] using h

end SetoidMetric

/-!
### A setoid-topology (open sets must be saturated)

We define a minimal “topology” structure whose opens are subsets of `α` and are required
to be `R`-saturated. This is the right setoid-first substitute for a topology on the
quotient `α / R`.
-/

structure SetoidTopology (R : Setoid α) where
  IsOpen : Set α → Prop
  isOpen_univ : IsOpen Set.univ
  isOpen_inter : ∀ U V, IsOpen U → IsOpen V → IsOpen (U ∩ V)
  isOpen_sUnion : ∀ S : Set (Set α), (∀ U, U ∈ S → IsOpen U) → IsOpen (Set.sUnion S)
  sat : ∀ U, IsOpen U → IsSat (α := α) R U

/-- The canonical “saturated topology”: opens are exactly the saturated sets. -/
def saturatedTopology (R : Setoid α) : SetoidTopology (α := α) R where
  IsOpen := IsSat (α := α) R
  isOpen_univ := by
    intro x y _hx hy
    exact trivial
  isOpen_inter := by
    intro U V hU hV x y hxy hyR
    exact ⟨hU hxy.1 hyR, hV hxy.2 hyR⟩
  isOpen_sUnion := by
    intro S hS x y hx hyR
    rcases hx with ⟨U, hUS, hxU⟩
    refine ⟨U, hUS, ?_⟩
    exact (hS U hUS) hxU hyR
  sat := by
    intro U hU
    exact hU

/-!
### Metric-open sets (general definition)

We do *not* claim this is a topology for an arbitrary `D`: proving closure under `∩` typically
requires extra structure (min/halving radii, etc.). We only need the definition and then
show that for the *discrete* setoid-distance on `Nat`, it collapses exactly to saturation.
-/

namespace SetoidMetric

variable {R : Setoid α} (M : SetoidMetric (α := α) (D := D) R)

def MetricIsOpen (U : Set α) : Prop :=
  IsSat (α := α) R U ∧
    ∀ x, x ∈ U → ∃ r : D, 0 < r ∧ ∀ y, M.d x y < r → y ∈ U

theorem metricIsOpen_sat {U : Set α} (h : M.MetricIsOpen U) : IsSat (α := α) R U :=
  h.1

end SetoidMetric

/-!
### Cauchy sequences (setoid-stable)
-/

namespace SetoidMetric

variable {R : Setoid α} (M : SetoidMetric (α := α) (D := D) R)

def CauchySeq (u : Nat → α) : Prop :=
  ∀ ε : D, 0 < ε →
    ∃ N : Nat, ∀ m n : Nat, N ≤ m → N ≤ n → M.d (u m) (u n) < ε

/-- Convergence on representatives (setoid-first). -/
def ConvergesTo (u : Nat → α) (ℓ : α) : Prop :=
  ∀ ε : D, 0 < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n → M.d (u n) ℓ < ε

theorem converges_transport_of_pointwise
    {u v : Nat → α}
    (hresp : ∀ n, R.r (u n) (v n)) (ℓ : α) :
    M.ConvergesTo u ℓ ↔ M.ConvergesTo v ℓ := by
  constructor
  · intro hu ε hε
    rcases hu ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hdn : M.d (u n) ℓ = M.d (v n) ℓ :=
      M.respects (hresp n) (R.iseqv.refl ℓ)
    have : M.d (u n) ℓ < ε := hN n hn
    simpa [hdn] using this
  · intro hv ε hε
    rcases hv ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hdn : M.d (v n) ℓ = M.d (u n) ℓ :=
      M.respects (R.iseqv.symm (hresp n)) (R.iseqv.refl ℓ)
    have : M.d (v n) ℓ < ε := hN n hn
    simpa [hdn] using this

theorem converges_transport_of_limit
    {u : Nat → α} {ℓ ℓ' : α} (hℓ : R.r ℓ ℓ') :
    M.ConvergesTo u ℓ ↔ M.ConvergesTo u ℓ' := by
  constructor
  · intro hu ε hε
    rcases hu ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hdn : M.d (u n) ℓ = M.d (u n) ℓ' :=
      M.respects (R.iseqv.refl (u n)) hℓ
    have : M.d (u n) ℓ < ε := hN n hn
    simpa [hdn] using this
  · intro hu ε hε
    rcases hu ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hdn : M.d (u n) ℓ' = M.d (u n) ℓ :=
      M.respects (R.iseqv.refl (u n)) (R.iseqv.symm hℓ)
    have : M.d (u n) ℓ' < ε := hN n hn
    simpa [hdn] using this

theorem cauchy_transport_of_pointwise
    {u v : Nat → α}
    (hresp : ∀ n, R.r (u n) (v n)) :
    M.CauchySeq u ↔ M.CauchySeq v := by
  constructor
  · intro hu ε hε
    rcases hu ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m n hm hn
    have hdmn : M.d (u m) (u n) = M.d (v m) (v n) :=
      M.respects (hresp m) (hresp n)
    have : M.d (u m) (u n) < ε := hN m n hm hn
    simpa [hdmn] using this
  · intro hv ε hε
    rcases hv ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m n hm hn
    have hdmn : M.d (v m) (v n) = M.d (u m) (u n) :=
      M.respects (R.iseqv.symm (hresp m)) (R.iseqv.symm (hresp n))
    have : M.d (v m) (v n) < ε := hN m n hm hn
    simpa [hdmn] using this

end SetoidMetric

/-!
### Discrete setoid-metric on `Nat` and its topology/Cauchy behavior

This is the canonical “quotient geometry”: it measures *discrete variability* at the setoid level:
two points are at distance `0` iff they are `R`-equivalent, otherwise distance `1`.
-/

section DiscreteDerived

variable (R : Setoid α) [DecidableRel R.r]

def discreteSetoidMetric : SetoidMetric (α := α) (D := Nat) R where
  d := discreteDist (α := α) (R := R)
  respects := discreteDist_respectsSetoid (α := α) (R := R)
  symm := discreteDist_symm (α := α) (R := R)
  tri := discreteDist_triangle (α := α) (R := R)
  sep := discreteDist_zero_iff (α := α) (R := R)

def EventualRTo (u : Nat → α) (ℓ : α) : Prop :=
  ∃ N : Nat, ∀ n : Nat, N ≤ n → R.r (u n) ℓ

theorem discreteDist_lt_one_iff (x y : α) :
    discreteDist (α := α) (R := R) x y < 1 ↔ R.r x y := by
  unfold discreteDist
  by_cases hxy : R.r x y
  · rw [if_pos hxy]
    constructor
    · intro _h
      exact hxy
    · intro _h
      exact Nat.zero_lt_one
  · rw [if_neg hxy]
    constructor
    · intro h
      exact False.elim (Nat.lt_irrefl 1 h)
    · intro h
      exact False.elim (hxy h)

theorem converges_discrete_iff_eventualRTo (u : Nat → α) (ℓ : α) :
    (discreteSetoidMetric (α := α) R).ConvergesTo u ℓ ↔ EventualRTo (α := α) (R := R) u ℓ := by
  constructor
  · intro hu
    rcases hu 1 Nat.zero_lt_one with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hlt : discreteDist (α := α) (R := R) (u n) ℓ < 1 := by
      simpa [SetoidMetric.ConvergesTo, discreteSetoidMetric] using hN n hn
    exact (discreteDist_lt_one_iff (α := α) (R := R) (u n) ℓ).1 hlt
  · rintro ⟨N, hN⟩ ε hε
    refine ⟨N, ?_⟩
    intro n hn
    have hR : R.r (u n) ℓ := hN n hn
    -- discrete distance is `0` on `R`, hence `< ε` for any `ε > 0`.
    simpa [SetoidMetric.ConvergesTo, discreteSetoidMetric, discreteDist, hR] using hε

theorem converges_discrete_unique_modR {u : Nat → α} {ℓ₁ ℓ₂ : α} :
    (discreteSetoidMetric (α := α) R).ConvergesTo u ℓ₁ →
      (discreteSetoidMetric (α := α) R).ConvergesTo u ℓ₂ → R.r ℓ₁ ℓ₂ := by
  intro h₁ h₂
  rcases (converges_discrete_iff_eventualRTo (α := α) (R := R) u ℓ₁).1 h₁ with ⟨N1, hN1⟩
  rcases (converges_discrete_iff_eventualRTo (α := α) (R := R) u ℓ₂).1 h₂ with ⟨N2, hN2⟩
  refine R.iseqv.trans (R.iseqv.symm (hN1 (Nat.max N1 N2) (Nat.le_max_left _ _))) ?_
  exact hN2 (Nat.max N1 N2) (Nat.le_max_right _ _)

theorem metricIsOpen_discrete_iff_isSat (U : Set α) :
    (discreteSetoidMetric (α := α) R).MetricIsOpen U ↔ IsSat (α := α) R U := by
  constructor
  · intro h
    exact h.1
  · intro hSat
    refine ⟨hSat, ?_⟩
    intro x hx
    refine ⟨1, Nat.zero_lt_one, ?_⟩
    intro y hy
    have : R.r x y := (discreteDist_lt_one_iff (α := α) (R := R) x y).1 hy
    exact hSat hx this

def discreteTopology : SetoidTopology (α := α) R where
  IsOpen := (discreteSetoidMetric (α := α) R).MetricIsOpen
  isOpen_univ := (metricIsOpen_discrete_iff_isSat (α := α) (R := R) Set.univ).2 (by
    intro x y _hx _hy
    trivial)
  isOpen_inter := by
    intro U V hU hV
    -- reduce to saturation
    have hSU : IsSat (α := α) R U := (metricIsOpen_discrete_iff_isSat (α := α) (R := R) U).1 hU
    have hSV : IsSat (α := α) R V := (metricIsOpen_discrete_iff_isSat (α := α) (R := R) V).1 hV
    exact
      (metricIsOpen_discrete_iff_isSat (α := α) (R := R) (U ∩ V)).2 (by
        intro x y hxy hyR
        exact ⟨hSU hxy.1 hyR, hSV hxy.2 hyR⟩)
  isOpen_sUnion := by
    intro S hS
    refine (metricIsOpen_discrete_iff_isSat (α := α) (R := R) (Set.sUnion S)).2 ?_
    intro x y hx hyR
    rcases hx with ⟨U, hUS, hxU⟩
    have hSatU : IsSat (α := α) R U :=
      (metricIsOpen_discrete_iff_isSat (α := α) (R := R) U).1 (hS U hUS)
    exact ⟨U, hUS, hSatU hxU hyR⟩
  sat := by
    intro U hU
    exact (metricIsOpen_discrete_iff_isSat (α := α) (R := R) U).1 hU

namespace SetoidMetric

def EventualPairwiseR (u : Nat → α) : Prop :=
  ∃ N : Nat, ∀ m n : Nat, N ≤ m → N ≤ n → R.r (u m) (u n)

theorem eventualPairwiseR_of_cauchy_discrete (u : Nat → α) :
    (discreteSetoidMetric (α := α) R).CauchySeq u → EventualPairwiseR (α := α) (R := R) u := by
  intro hC
  rcases hC 1 Nat.zero_lt_one with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m n hm hn
  have hlt : discreteDist (α := α) (R := R) (u m) (u n) < 1 := hN m n hm hn
  exact (discreteDist_lt_one_iff (α := α) (R := R) (u m) (u n)).1 hlt

theorem cauchy_discrete_of_eventualPairwiseR (u : Nat → α) :
    EventualPairwiseR (α := α) (R := R) u → (discreteSetoidMetric (α := α) R).CauchySeq u := by
  rintro ⟨N, hN⟩ ε hε
  refine ⟨N, ?_⟩
  intro m n hm hn
  have hmn : R.r (u m) (u n) := hN m n hm hn
  -- `discreteDist = 0` on equivalent points, hence `< ε` for any `ε > 0`.
  change discreteDist (α := α) (R := R) (u m) (u n) < ε
  unfold discreteDist
  rw [if_pos hmn]
  exact hε

theorem converges_discrete_of_eventualRTo (u : Nat → α) (ℓ : α) :
    EventualRTo (α := α) (R := R) u ℓ → (discreteSetoidMetric (α := α) R).ConvergesTo u ℓ := by
  intro h
  exact (converges_discrete_iff_eventualRTo (α := α) (R := R) u ℓ).2 h

theorem cauchy_discrete_exists_limit (u : Nat → α) :
    (discreteSetoidMetric (α := α) R).CauchySeq u →
      ∃ ℓ : α, (discreteSetoidMetric (α := α) R).ConvergesTo u ℓ := by
  intro hC
  rcases eventualPairwiseR_of_cauchy_discrete (α := α) (R := R) u hC with ⟨N, hN⟩
  refine ⟨u N, ?_⟩
  refine (converges_discrete_iff_eventualRTo (α := α) (R := R) u (u N)).2 ?_
  refine ⟨N, ?_⟩
  intro n hn
  have : R.r (u N) (u n) := hN N n (le_rfl) hn
  exact R.iseqv.symm this

theorem cauchy_discrete_iff_eventualPairwiseR (u : Nat → α) :
    (discreteSetoidMetric (α := α) R).CauchySeq u ↔ EventualPairwiseR (α := α) (R := R) u := by
  constructor
  · exact eventualPairwiseR_of_cauchy_discrete (α := α) (R := R) u
  · exact cauchy_discrete_of_eventualPairwiseR (α := α) (R := R) u

end SetoidMetric

end DiscreteDerived

end SetoidMetricPack

end SetoidOnly

/-!
## Axiom audit

This file is setoid-only (no `Quot`) and should not depend on `propext`.
-/

#print axioms PrimitiveHolonomy.RespectsSetoid
#print axioms PrimitiveHolonomy.triangle_descends
#print axioms PrimitiveHolonomy.discreteDist_triangle
#print axioms PrimitiveHolonomy.SetoidMetric
#print axioms PrimitiveHolonomy.SetoidMetric.cauchy_discrete_iff_eventualPairwiseR

end PrimitiveHolonomy
