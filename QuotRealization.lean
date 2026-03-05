import forU2read.main

/-!
# PrimitiveHolonomy: Probe Quotient Realization via `Quot`

`RevHalt/Theory/PrimitiveHolonomy/Main.lean` develops the probe quotient *setoid-first*.
This file provides the optional **type-level realization**:

* define `FiberQuot := Quot (ProbeSetoid ...)`,
* prove the usual universal properties as maps of types,
* package the canonical quotient equivalence induced by coefficient cover.

This layer depends on the kernel axiom `Quot.sound` (soundness of quotient types).
-/

universe u v w uQ

namespace PrimitiveHolonomy

/-!
## Probe quotient (realized as `Quot`)
-/

/-- Quotient of a fiber by two-sided probe indistinguishability. -/
def FiberQuot {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S)
    (obs : S → V) (target_obs : P → V) (h : P) :=
  Quot (ProbeSetoid (P := P) C fam obs target_obs h)

/-- Quotient of a fiber by two-sided probe indistinguishability on `C0`. -/
def FiberQuotOn {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S) (C0 : Set C.Obj)
    (obs : S → V) (target_obs : P → V) (h : P) :=
  Quot (ProbeSetoidOn (P := P) C fam C0 obs target_obs h)

section ProbeQuotientUniversal

variable {P : Type u} [HistoryGraph P]
variable {S V : Type w}
variable (C : CoeffCat) (fam : SemFamily C P S)
variable (obs : S → V) (target_obs : P → V)
variable {h : P}

/-!
### Universal properties

Since `FiberQuot` / `FiberQuotOn` are defined as `Quot`, they inherit the standard universal
property: any function constant on the induced setoid factors uniquely through the quotient.

We also isolate the “largest quotient making holonomy tests invariant” terminality statement:
any holonomy-compatible setoid quotient maps uniquely into `FiberQuot`.
-/

/-- Universal property (existence + uniqueness) of the full probe quotient `FiberQuot`. -/
theorem fiberQuot_lift_existsUnique {X : Type _}
    (f : FiberPt (P := P) obs target_obs h → X)
    (hf :
      ∀ x y : FiberPt (P := P) obs target_obs h,
        ProbeIndistinguishable (P := P) C fam obs target_obs h x y → f x = f y) :
    ∃! fbar : FiberQuot (P := P) C fam obs target_obs h → X,
      ∀ x : FiberPt (P := P) obs target_obs h,
        fbar (Quot.mk (ProbeSetoid (P := P) C fam obs target_obs h) x) = f x := by
  let fbar : FiberQuot (P := P) C fam obs target_obs h → X :=
    Quot.lift f (by
      intro x y hxy
      exact hf x y hxy)
  refine ⟨fbar, ?_, ?_⟩
  · intro x
    rfl
  · intro g hg
    funext q
    refine Quot.inductionOn q (fun x => ?_)
    calc
      g (Quot.mk (ProbeSetoid (P := P) C fam obs target_obs h) x) = f x := hg x
      _ = fbar (Quot.mk (ProbeSetoid (P := P) C fam obs target_obs h) x) := by
        rfl

/-- Universal property (existence + uniqueness) of the restricted probe quotient `FiberQuotOn`. -/
theorem fiberQuotOn_lift_existsUnique {C0 : Set C.Obj} {X : Type _}
    (f : FiberPt (P := P) obs target_obs h → X)
    (hf :
      ∀ x y : FiberPt (P := P) obs target_obs h,
        ProbeIndistinguishableOn (P := P) C fam C0 obs target_obs h x y → f x = f y) :
    ∃! fbar : FiberQuotOn (P := P) C fam C0 obs target_obs h → X,
      ∀ x : FiberPt (P := P) obs target_obs h,
        fbar (Quot.mk (ProbeSetoidOn (P := P) C fam C0 obs target_obs h) x) = f x := by
  let fbar : FiberQuotOn (P := P) C fam C0 obs target_obs h → X :=
    Quot.lift f (by
      intro x y hxy
      exact hf x y hxy)
  refine ⟨fbar, ?_, ?_⟩
  · intro x
    rfl
  · intro g hg
    funext q
    refine Quot.inductionOn q (fun x => ?_)
    calc
      g (Quot.mk (ProbeSetoidOn (P := P) C fam C0 obs target_obs h) x) = f x := hg x
      _ = fbar (Quot.mk (ProbeSetoidOn (P := P) C fam C0 obs target_obs h) x) := by
        rfl

/--
Terminality among holonomy-compatible quotients:
any holonomy-compatible fiber setoid quotient maps uniquely into the probe quotient `FiberQuot`.
-/
theorem fiberQuot_terminal_among_holonomyCompatible
    (R : Setoid (FiberPt (P := P) obs target_obs h))
    (hR : HolonomyCompatibleSetoid (P := P) (C := C) fam obs target_obs (h := h) R) :
    ∃! φ : Quot R → FiberQuot (P := P) C fam obs target_obs h,
      ∀ x : FiberPt (P := P) obs target_obs h,
        φ (Quot.mk R x) = Quot.mk (ProbeSetoid (P := P) C fam obs target_obs h) x := by
  let φ : Quot R → FiberQuot (P := P) C fam obs target_obs h :=
    Quot.lift
      (fun x => Quot.mk (ProbeSetoid (P := P) C fam obs target_obs h) x)
      (by
        intro x y hxy
        apply Quot.sound
        exact
          probeIndistinguishable_of_holonomyCompatibleSetoid
            (P := P) (C := C) fam obs target_obs (h := h)
            R hR hxy)
  refine ⟨φ, ?_, ?_⟩
  · intro x
    rfl
  · intro ψ hψ
    funext q
    refine Quot.inductionOn q (fun x => ?_)
    simpa using hψ x

end ProbeQuotientUniversal

/-!
## Coefficient cover ⇒ quotient equivalence

This is the type-level counterpart of the setoid-level reduction lemma
`probeIndistinguishable_iff_probeIndistinguishableOn_of_coeffCovers` from `Main.lean`.
-/

/-- Canonical map from the full probe quotient to the restricted one. -/
def fiberQuotToOn {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S) (C0 : Set C.Obj)
    (obs : S → V) (target_obs : P → V) (h : P)
    (hCover : CoeffCovers (P := P) C fam C0 obs target_obs) :
    FiberQuot (P := P) C fam obs target_obs h →
      FiberQuotOn (P := P) C fam C0 obs target_obs h :=
  Quot.map id (fun x y hxy =>
    (probeIndistinguishable_iff_probeIndistinguishableOn_of_coeffCovers
      (P := P) C fam C0 obs target_obs h hCover x y).1 hxy)

/-- Canonical map from the restricted probe quotient to the full one. -/
def fiberQuotFromOn {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S) (C0 : Set C.Obj)
    (obs : S → V) (target_obs : P → V) (h : P)
    (hCover : CoeffCovers (P := P) C fam C0 obs target_obs) :
    FiberQuotOn (P := P) C fam C0 obs target_obs h →
      FiberQuot (P := P) C fam obs target_obs h :=
  Quot.map id (fun x y hxy =>
    (probeIndistinguishable_iff_probeIndistinguishableOn_of_coeffCovers
      (P := P) C fam C0 obs target_obs h hCover x y).2 hxy)

theorem fiberQuotFromOn_leftInverse_fiberQuotToOn
    {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S) (C0 : Set C.Obj)
    (obs : S → V) (target_obs : P → V) (h : P)
    (hCover : CoeffCovers (P := P) C fam C0 obs target_obs) :
    Function.LeftInverse
      (fiberQuotFromOn (P := P) C fam C0 obs target_obs h hCover)
      (fiberQuotToOn (P := P) C fam C0 obs target_obs h hCover) := by
  intro q
  refine Quot.inductionOn q ?_
  intro x
  rfl

theorem fiberQuotToOn_rightInverse_fiberQuotFromOn
    {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S) (C0 : Set C.Obj)
    (obs : S → V) (target_obs : P → V) (h : P)
    (hCover : CoeffCovers (P := P) C fam C0 obs target_obs) :
    Function.RightInverse
      (fiberQuotFromOn (P := P) C fam C0 obs target_obs h hCover)
      (fiberQuotToOn (P := P) C fam C0 obs target_obs h hCover) := by
  intro q
  refine Quot.inductionOn q ?_
  intro x
  rfl

/--
Under coefficient cover, the full quotient and the restricted quotient are equivalent.
-/
def fiberQuotEquivFiberQuotOn {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S) (C0 : Set C.Obj)
    (obs : S → V) (target_obs : P → V) (h : P)
    (hCover : CoeffCovers (P := P) C fam C0 obs target_obs) :
    FiberQuot (P := P) C fam obs target_obs h ≃
      FiberQuotOn (P := P) C fam C0 obs target_obs h where
  toFun := fiberQuotToOn (P := P) C fam C0 obs target_obs h hCover
  invFun := fiberQuotFromOn (P := P) C fam C0 obs target_obs h hCover
  left_inv := fiberQuotFromOn_leftInverse_fiberQuotToOn
    (P := P) C fam C0 obs target_obs h hCover
  right_inv := fiberQuotToOn_rightInverse_fiberQuotFromOn
    (P := P) C fam C0 obs target_obs h hCover

/--
Structural quotient-equivalence from:
1) coefficient cofinality,
2) holonomy naturality,
3) push conservativity on holonomy.
-/
def fiberQuotEquivFiberQuotOn_of_coeffCofinal_of_holonomyNatural_of_pushConservativeOnHolonomy
    {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S) (C0 : Set C.Obj)
    (obs : S → V) (target_obs : P → V) (h : P)
    (push : FiberRelPush (P := P) (S := S) (V := V) C obs target_obs)
    (hCof : CoeffCofinal C C0)
    (hNat : HolonomyNatural (P := P) C fam obs target_obs push)
    (hCons : PushConservativeOnHolonomy (P := P) C fam obs target_obs push) :
    FiberQuot (P := P) C fam obs target_obs h ≃
      FiberQuotOn (P := P) C fam C0 obs target_obs h := by
  refine fiberQuotEquivFiberQuotOn (P := P) C fam C0 obs target_obs h ?_
  exact
    coeffCovers_of_coeffCofinal_of_holonomyNatural_of_pushConservativeOnHolonomy
      (P := P) C fam C0 obs target_obs push hCof hNat hCons

/-!
## Concrete instance: quotient equivalence

`Main.lean` already defines the “math” instance up to the setoid-level reduction theorem
`mathProbeReduction`. Here we add the corresponding quotient-level equivalence.
-/

section ConcreteMathInstance

/-- Structural quotient equivalence in the concrete mathematical instance. -/
def mathFiberQuotEquiv :
    FiberQuot
      (P := MathPrefix) MathCoeffCat mathSemFamily mathObs mathTargetObs MathPrefix.base
      ≃
    FiberQuotOn
      (P := MathPrefix) MathCoeffCat mathSemFamily mathC0
      mathObs mathTargetObs MathPrefix.base := by
  exact
    fiberQuotEquivFiberQuotOn_of_coeffCofinal_of_holonomyNatural_of_pushConservativeOnHolonomy
      (P := MathPrefix)
      MathCoeffCat mathSemFamily mathC0
      mathObs mathTargetObs MathPrefix.base
      mathPush mathCoeffCofinal mathHolonomyNatural mathPushConservative

end ConcreteMathInstance

/-!
## Descended holonomy relations on the realized quotients

This is the “representatives” presentation: a quotient-level relation holds if there exist
representatives related by the underlying fiber relation.
-/

section QuotientOperational

variable {P : Type u} [HistoryGraph P]
variable {S V : Type w}
variable (C : CoeffCat) (fam : SemFamily C P S)
variable (obs : S → V) (target_obs : P → V)

/-- Holonomy relation descended to the full quotient. -/
def HolonomyRelQuot
    {h k : P} (c : C.Obj) {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q) :
    Relation
      (FiberQuot (P := P) C fam obs target_obs h)
      (FiberQuot (P := P) C fam obs target_obs h) :=
  fun qx qy =>
    ∃ x y : FiberPt (P := P) obs target_obs h,
      Quot.mk (ProbeSetoid (P := P) C fam obs target_obs h) x = qx ∧
      Quot.mk (ProbeSetoid (P := P) C fam obs target_obs h) y = qy ∧
      HolonomyRel (P := P) (fam.sem c) obs target_obs α x y

/-- Holonomy relation descended to the restricted quotient (for coefficients in `C0`). -/
def HolonomyRelQuotOn
    {C0 : Set C.Obj} {h k : P} (c : C.Obj) (_hc : c ∈ C0)
    {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q) :
    Relation
      (FiberQuotOn (P := P) C fam C0 obs target_obs h)
      (FiberQuotOn (P := P) C fam C0 obs target_obs h) :=
  fun qx qy =>
    ∃ x y : FiberPt (P := P) obs target_obs h,
      Quot.mk (ProbeSetoidOn (P := P) C fam C0 obs target_obs h) x = qx ∧
      Quot.mk (ProbeSetoidOn (P := P) C fam C0 obs target_obs h) y = qy ∧
      HolonomyRel (P := P) (fam.sem c) obs target_obs α x y

/-- Representative-introduction rule for `HolonomyRelQuot`. -/
theorem holonomyRelQuot_mk
    {h k : P} (c : C.Obj) {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (x y : FiberPt (P := P) obs target_obs h) :
    HolonomyRel (P := P) (fam.sem c) obs target_obs α x y →
    HolonomyRelQuot (P := P) (C := C) fam obs target_obs c α
      (Quot.mk (ProbeSetoid (P := P) C fam obs target_obs h) x)
      (Quot.mk (ProbeSetoid (P := P) C fam obs target_obs h) y)
      := by
  intro hxy
  exact ⟨x, y, rfl, rfl, hxy⟩

/-- Representative-introduction form for `HolonomyRelQuot` (explicit arrow). -/
theorem holonomyRelQuot_mk_intro
    {h k : P} (c : C.Obj) {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (x y : FiberPt (P := P) obs target_obs h) :
    HolonomyRel (P := P) (fam.sem c) obs target_obs α x y →
    HolonomyRelQuot (P := P) (C := C) fam obs target_obs c α
      (Quot.mk (ProbeSetoid (P := P) C fam obs target_obs h) x)
      (Quot.mk (ProbeSetoid (P := P) C fam obs target_obs h) y) := by
  intro hxy
  exact ⟨x, y, rfl, rfl, hxy⟩

/-- Representative-introduction rule for `HolonomyRelQuotOn`. -/
theorem holonomyRelQuotOn_mk
    {C0 : Set C.Obj} {h k : P} (c : C.Obj) (hc : c ∈ C0)
    {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (x y : FiberPt (P := P) obs target_obs h) :
    HolonomyRel (P := P) (fam.sem c) obs target_obs α x y →
    HolonomyRelQuotOn (P := P) (C := C) (C0 := C0) fam obs target_obs c hc α
      (Quot.mk (ProbeSetoidOn (P := P) C fam C0 obs target_obs h) x)
      (Quot.mk (ProbeSetoidOn (P := P) C fam C0 obs target_obs h) y)
      := by
  intro hxy
  exact ⟨x, y, rfl, rfl, hxy⟩

/-- Representative-introduction form for `HolonomyRelQuotOn` (explicit arrow). -/
theorem holonomyRelQuotOn_mk_intro
    {C0 : Set C.Obj} {h k : P} (c : C.Obj) (hc : c ∈ C0)
    {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (x y : FiberPt (P := P) obs target_obs h) :
    HolonomyRel (P := P) (fam.sem c) obs target_obs α x y →
    HolonomyRelQuotOn (P := P) (C := C) (C0 := C0) fam obs target_obs c hc α
      (Quot.mk (ProbeSetoidOn (P := P) C fam C0 obs target_obs h) x)
      (Quot.mk (ProbeSetoidOn (P := P) C fam C0 obs target_obs h) y) := by
  intro hxy
  exact ⟨x, y, rfl, rfl, hxy⟩

/-- Representative-level introduction into the restricted quotient relation. -/
theorem holonomyRelQuotOn_toOn_iff
    {C0 : Set C.Obj} {h k : P} (c : C.Obj) (hc : c ∈ C0)
    {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (x y : FiberPt (P := P) obs target_obs h) :
    HolonomyRel (P := P) (fam.sem c) obs target_obs α x y →
    HolonomyRelQuotOn (P := P) (C := C) (C0 := C0) fam obs target_obs c hc α
      (Quot.mk (ProbeSetoidOn (P := P) C fam C0 obs target_obs h) x)
      (Quot.mk (ProbeSetoidOn (P := P) C fam C0 obs target_obs h) y) := by
  intro hxy
  exact holonomyRelQuotOn_mk (P := P) (C := C) (C0 := C0) fam obs target_obs c hc α x y hxy

/-- Representative-level introduction into the full quotient relation. -/
theorem holonomyRelQuot_fromOn_iff
    {C0 : Set C.Obj} {h k : P} (c : C.Obj) (_hc : c ∈ C0)
    {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (x y : FiberPt (P := P) obs target_obs h) :
    HolonomyRel (P := P) (fam.sem c) obs target_obs α x y →
    HolonomyRelQuot (P := P) (C := C) fam obs target_obs c α
      (Quot.mk (ProbeSetoid (P := P) C fam obs target_obs h) x)
      (Quot.mk (ProbeSetoid (P := P) C fam obs target_obs h) y) := by
  intro hxy
  exact holonomyRelQuot_mk (P := P) (C := C) fam obs target_obs c α x y hxy

end QuotientOperational

/-!
## Axiom audit

This file intentionally depends on `Quot.sound`.
-/

#print axioms PrimitiveHolonomy.FiberQuot
#print axioms PrimitiveHolonomy.FiberQuotOn
#print axioms PrimitiveHolonomy.fiberQuot_lift_existsUnique
#print axioms PrimitiveHolonomy.fiberQuotOn_lift_existsUnique
#print axioms PrimitiveHolonomy.fiberQuot_terminal_among_holonomyCompatible
#print axioms PrimitiveHolonomy.fiberQuotEquivFiberQuotOn
#print axioms PrimitiveHolonomy.mathFiberQuotEquiv
#print axioms PrimitiveHolonomy.HolonomyRelQuot
#print axioms PrimitiveHolonomy.HolonomyRelQuotOn
#print axioms PrimitiveHolonomy.holonomyRelQuot_mk
#print axioms PrimitiveHolonomy.holonomyRelQuotOn_mk
#print axioms PrimitiveHolonomy.holonomyRelQuotOn_toOn_iff
#print axioms PrimitiveHolonomy.holonomyRelQuot_fromOn_iff

end PrimitiveHolonomy

