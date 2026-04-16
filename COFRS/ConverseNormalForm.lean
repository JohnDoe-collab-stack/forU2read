import COFRS.Dynamics

/-!
# Primitive Holonomy: Converse / Normal-form fragments (constructive)

This file provides *partial converse* statements that are useful for Phase D
("converse / normal form") in the universalization plan.

Key idea: to extract explicit counterexamples (separating witnesses) from negative
statements like `¬ ObsPredictsStep`, we work under *explicit finitary enumerations*
of the relevant fiber. This avoids any classical choice and stays constructive.
-/

universe u w

namespace PrimitiveHolonomy

variable {P : Type u} [HistoryGraph P]

/-!
## Finitary fiber enumerations (no choice)

Rather than assuming `Fintype` and using non-constructive equivalences, we assume an
explicit finite enumeration `Fin N → FiberPt ...` which is surjective.
-/

structure FiberEnum {S V : Type w} (obs : S → V) (target_obs : P → V) (h : P) : Type w where
  N : Nat
  enum : Fin N → FiberPt (P := P) obs target_obs h
  surj : ∀ x : FiberPt (P := P) obs target_obs h, ∃ i : Fin N, enum i = x


section WithEnum

variable {S V : Type w}
variable (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
variable {h k : P} (step : HistoryGraph.Path h k)

/--
Either compatibility is `obs`-decidable (in the `ObsPredictsStep` sense), or the step separates the fiber.

This is the constructive split used to turn `¬ ObsPredictsStep` into an explicit
`StepSeparatesFiber` witness, *provided* we have a finitary fiber enumeration and a
decidable `Compatible` predicate on that fiber.
-/
theorem obsPredictsStep_or_stepSeparatesFiber_of_fiberEnum :
    (E : FiberEnum (P := P) obs target_obs h) →
    (decCompat : ∀ x : FiberPt (P := P) obs target_obs h,
      Decidable (Compatible (P := P) sem obs target_obs step x)) →
    ObsPredictsStep (P := P) sem obs target_obs step
      ∨ StepSeparatesFiber (P := P) sem obs target_obs step := by
  intro E decCompat
  let Pcompat : Fin E.N → Prop :=
    fun i => Compatible (P := P) sem obs target_obs step (E.enum i)
  have decPcompat : ∀ i : Fin E.N, Decidable (Pcompat i) :=
    fun i => decCompat (E.enum i)
  let Pncompat : Fin E.N → Prop := fun i => ¬ Pcompat i
  have decPncompat : ∀ i : Fin E.N, Decidable (Pncompat i) := by
    intro i
    letI : Decidable (Pcompat i) := decPcompat i
    dsimp [Pncompat]
    exact instDecidableNot
  -- Decide whether there exists an enumerated fiber point that is compatible.
  cases PrimitiveHolonomy.Combinatorics.decidableExistsFin
      (n := E.N)
      (P := Pcompat)
      (decP := decPcompat) with
  | isFalse hNoCompat =>
      -- No compatible points at all: choose the constant-false obs-predicate.
      refine Or.inl ?_
      refine ⟨(fun _v => False), ?_⟩
      intro x
      constructor
      · intro hx
        rcases E.surj x with ⟨i, hi⟩
        have : ∃ i : Fin E.N, Pcompat i := by
          refine ⟨i, ?_⟩
          -- rewrite `hx` along `hi : enum i = x`
          simpa [Pcompat, hi] using hx
        exact False.elim (hNoCompat this)
      · intro hFalse
        cases hFalse
  | isTrue hHasCompat =>
      rcases hHasCompat with ⟨i0, hi0⟩
      let x0 : FiberPt (P := P) obs target_obs h := E.enum i0
      have hx0 : Compatible (P := P) sem obs target_obs step x0 := by
        simpa [x0, Pcompat] using hi0
      -- Decide whether there exists an enumerated fiber point that is *not* compatible.
      cases PrimitiveHolonomy.Combinatorics.decidableExistsFin
          (n := E.N)
          (P := Pncompat)
          (decP := decPncompat) with
      | isTrue hHasNCompat =>
          rcases hHasNCompat with ⟨i1, hi1⟩
          let x1 : FiberPt (P := P) obs target_obs h := E.enum i1
          have hx1 : ¬ Compatible (P := P) sem obs target_obs step x1 := by
            simpa [x1, Pncompat, Pcompat] using hi1
          have hxne : x0 ≠ x1 := by
            intro hEq
            exact hx1 (by simpa [hEq] using hx0)
          exact Or.inr ⟨x0, x1, hxne, hx0, hx1⟩
      | isFalse hNoNCompat =>
          -- All enumerated points are compatible (by decidable search), hence all fiber points are compatible.
          have hall_enum : ∀ i : Fin E.N, Pcompat i := by
            intro i
            cases decPcompat i with
            | isTrue hi =>
                exact hi
            | isFalse hni =>
                exact False.elim (hNoNCompat ⟨i, hni⟩)
          have hall : ∀ x : FiberPt (P := P) obs target_obs h,
              Compatible (P := P) sem obs target_obs step x := by
            intro x
            rcases E.surj x with ⟨i, hi⟩
            have : Compatible (P := P) sem obs target_obs step (E.enum i) := by
              simpa [Pcompat] using hall_enum i
            simpa [hi] using this
          -- Use the constant-true obs-predicate.
          refine Or.inl ?_
          refine ⟨(fun _v => True), ?_⟩
          intro x
          constructor
          · intro _hx
            trivial
          · intro _hTrue
            exact hall x

/-- Under a finitary fiber enumeration, `¬ ObsPredictsStep` yields an explicit separating witness. -/
theorem stepSeparatesFiber_of_not_obsPredictsStep_of_fiberEnum
    (hNoObs : ¬ ObsPredictsStep (P := P) sem obs target_obs step) :
    (E : FiberEnum (P := P) obs target_obs h) →
    (decCompat : ∀ x : FiberPt (P := P) obs target_obs h,
      Decidable (Compatible (P := P) sem obs target_obs step x)) →
    StepSeparatesFiber (P := P) sem obs target_obs step := by
  intro E decCompat
  rcases obsPredictsStep_or_stepSeparatesFiber_of_fiberEnum
      (P := P) (sem := sem) (obs := obs) (target_obs := target_obs)
      (h := h) (k := k) (step := step) E decCompat with hObs | hSep
  · exact False.elim (hNoObs hObs)
  · exact hSep

end WithEnum


section NormalFormBinary

variable {S V : Type w}
variable (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
variable {h k : P} (step : HistoryGraph.Path h k)

variable (decCompat : ∀ x : FiberPt (P := P) obs target_obs h,
  Decidable (Compatible (P := P) sem obs target_obs step x))

private def fin2_0 : Fin 2 := PrimitiveHolonomy.Combinatorics.finFirst 1
private def fin2_1 : Fin 2 := PrimitiveHolonomy.Combinatorics.finLast 1

private theorem fin2_0_ne_fin2_1 : fin2_0 ≠ fin2_1 := by
  intro hEq
  have : (fin2_0).val = (fin2_1).val := congrArg Fin.val hEq
  -- `0 ≠ 1`
  exact Nat.zero_ne_one this

/-- If `Compatible` is decidable on the fiber, compatibility always has internal dimension ≤ 2. -/
theorem compatDimLe_two_of_decidableCompatible :
    (decCompat : ∀ x : FiberPt (P := P) obs target_obs h,
      Decidable (Compatible (P := P) sem obs target_obs step x)) →
    CompatDimLe (P := P) sem obs target_obs step 2 := by
  intro decCompat
  letI : DecidablePred (fun x : FiberPt (P := P) obs target_obs h =>
      Compatible (P := P) sem obs target_obs step x) :=
    decCompat
  let σ : FiberPt (P := P) obs target_obs h → Fin 2 :=
    fun x => if Compatible (P := P) sem obs target_obs step x then fin2_0 else fin2_1
  let pred : Fin 2 → Prop := fun i => i = fin2_0
  refine ⟨σ, pred, ?_⟩
  intro x
  -- Avoid `simp` here to keep the proof `propext`-free.
  cases decCompat x with
  | isTrue hx =>
      -- `Compatible x` holds, so `σ x = fin2_0`, hence the predicate holds.
      constructor
      · intro _hc
        dsimp [pred]
        dsimp [σ]
        rw [if_pos hx]
      · intro _hp
        exact hx
  | isFalse hx =>
      have hne : fin2_1 ≠ fin2_0 := by
        intro hEq
        exact fin2_0_ne_fin2_1 (by simpa using hEq.symm)
      constructor
      · intro hc
        exact False.elim (hx hc)
      · intro hp
        have hσ : σ x = fin2_1 := by
          dsimp [σ]
          rw [if_neg hx]
        have : fin2_0 = fin2_1 := hp.symm.trans hσ
        exact False.elim (hne this.symm)

/-- Normal form (binary): a separating step forces exact internal dimension 2, given decidable `Compatible`. -/
theorem compatDimEqTwo_of_stepSeparatesFiber_of_decidableCompatible
    (hSep : StepSeparatesFiber (P := P) sem obs target_obs step) :
    (decCompat : ∀ x : FiberPt (P := P) obs target_obs h,
      Decidable (Compatible (P := P) sem obs target_obs step x)) →
    CompatDimEqTwo (P := P) sem obs target_obs step := by
  intro decCompat
  refine ⟨compatDimLe_two_of_decidableCompatible (P := P) sem obs target_obs (h := h) (k := k) step decCompat, ?_⟩
  exact
    not_compatDimLe_one_of_stepSeparatesFiber (P := P) sem obs target_obs step hSep

end NormalFormBinary


section NormalFormN

variable {S V : Type w}
variable (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
variable {h k : P} (step : HistoryGraph.Path h k)
variable {n : Nat}

/-- Pairwise propositional separation (constructive): distinct indices do not carry equivalent props. -/
def PairwisePropSeparated (pred : Fin n → Prop) : Prop :=
  ∀ i j : Fin n, i ≠ j → ¬ (pred i ↔ pred j)

/--
Normal form (`n`-ary, conditional):

If compatibility factors through a finite summary `σ : fiber → Fin n` with predicate `pred`,
and there exists an explicit witness family realizing all `n` summary classes, and `pred` is
pairwise propositionally separated, then the compatibility dimension is **exactly** `n`.

This packages the usual “upper bound + constructive lower bound via pigeonhole” in a reusable form.
-/
theorem compatDimEq_of_factorization_of_pairwisePropSeparated
    (σ : FiberPt (P := P) obs target_obs h → Fin n)
    (pred : Fin n → Prop)
    (hcorr : ∀ x : FiberPt (P := P) obs target_obs h,
      Compatible (P := P) sem obs target_obs step x ↔ pred (σ x))
    (x : Fin n → FiberPt (P := P) obs target_obs h)
    (hx : ∀ i : Fin n, σ (x i) = i)
    (hsep : PairwisePropSeparated (n := n) pred) :
    CompatDimEq (P := P) sem obs target_obs step n := by
  refine ⟨⟨σ, pred, hcorr⟩, ?_⟩
  intro m hm
  -- Build the required pairwise compatibility separation from pairwise separation of `pred`.
  have hCompatSep :
      PairwiseCompatSeparated (P := P) sem obs target_obs step x := by
    intro i j hij
    intro hIff
    have hi : Compatible (P := P) sem obs target_obs step (x i) ↔ pred i := by
      have := hcorr (x i)
      simpa [hx i] using this
    have hj : Compatible (P := P) sem obs target_obs step (x j) ↔ pred j := by
      have := hcorr (x j)
      simpa [hx j] using this
    have : pred i ↔ pred j := (hi.symm.trans (hIff.trans hj))
    exact (hsep i j hij) this
  exact
    not_compatDimLe_of_finite_witness_family (P := P) sem obs target_obs step x hCompatSep hm

end NormalFormN

/-!
## Notes (Phase D / “getting rid of conditionals”)

In this development, `CompatDimEq … step n` is a *quantitative* statement about how many finite
classes are needed to decide the (binary) truth `Compatible … step x` on a fiber.

Because `Compatible … step x` is a single proposition (true/false), there is no general way to
force `n > 2` from “pure decidability” alone: decidability yields a canonical **binary**
classification (compatible vs not compatible), hence the unconditional normal form
`CompatDimLe … 2` in §`NormalFormBinary`.

To obtain **exact** dimension `n` without classical choice, one must provide (and in concrete
instances, *check*) extra structure that actually produces `n` non-collapsing classes. The
repository follows two professional routes:

1. **Witness families / barrier validity (finite, checkable).**
   Provide an explicit family of fiber points `x : Fin n → fiber` whose compatibility propositions
   are pairwise non-equivalent (or equivalently, provide a factorization through `Fin n` together
   with representatives of each summary class). This is the pattern used by
   `not_compatDimLe_of_finite_witness_family` in `COFRS/Dynamics.lean` and packaged here as the
   conditional normal form in §`NormalFormN`.

2. **Multi-step signatures (many bits, hence many classes).**
   Instead of fixing a single `step`, use the *signature* `Sig` over a finite family of future
   steps (or equivalently, a finite set of tests). This turns “one bit” into “many bits” and can
   yield `n`-ary exactness by construction. This corresponds to making the “barrier” richer
   (more separating tests) rather than asking a single proposition to carry `n` classes.

Empirically, this is exactly why Phase A1 in `Empirical/aslmt/UNIVERSALITY_PLAN.md` enforces
non-negotiable “barrier validity / anti-collisions” gates: they are the experimental analogue of
supplying the explicit witness structure required for `n`-ary exactness.
-/

end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.FiberEnum
#print axioms PrimitiveHolonomy.obsPredictsStep_or_stepSeparatesFiber_of_fiberEnum
#print axioms PrimitiveHolonomy.stepSeparatesFiber_of_not_obsPredictsStep_of_fiberEnum
#print axioms PrimitiveHolonomy.compatDimLe_two_of_decidableCompatible
#print axioms PrimitiveHolonomy.compatDimEqTwo_of_stepSeparatesFiber_of_decidableCompatible
#print axioms PrimitiveHolonomy.PairwisePropSeparated
#print axioms PrimitiveHolonomy.compatDimEq_of_factorization_of_pairwisePropSeparated
/- AXIOM_AUDIT_END -/
