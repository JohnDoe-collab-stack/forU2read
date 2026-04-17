import COFRS.RegulationAndReduction
import COFRS.Synthesis

namespace PrimitiveHolonomy
namespace HolonomicGodelByCode

/-
We now quantify over *codes* `e : Nat` for total boolean functions `U e : Nat → Bool`.
This is the right granularity for Church: only computable candidates are in scope.
-/

variable (Provable : Nat → Prop)

-- A universal evaluator for boolean total functions (code → input → output).
variable (U : Nat → Nat → Bool)

/-- A candidate code `e` decides provability if `U e` matches `Provable` on all inputs. -/
def DecidesProvableByCode (e : Nat) : Prop :=
  ∀ n, (U e n = true ↔ Provable n)

/--
Diagonal operator on *codes*: given `e`, returns `g` such that
`Provable g ↔ U e g = false`.
-/
structure DiagonalCode where
  diag : Nat → Nat
  diag_spec : ∀ e, Provable (diag e) ↔ (U e (diag e) = false)

variable {Provable U}
variable (D : DiagonalCode (Provable := Provable) (U := U))

/-! HistoryGraph: same as your file (minimal) -/

inductive PPath : Nat → Nat → Type
  | id   (n : Nat) : PPath n n
  | p    (n : Nat) : PPath n n
  | q    (n : Nat) : PPath n n
  | step (n : Nat) : PPath n n
  | comp {a b c : Nat} : PPath a b → PPath b c → PPath a c

inductive PDef : {h k : Nat} → PPath h k → PPath h k → Prop
  | pq (n : Nat) : PDef (PPath.p n) (PPath.q n)

instance : HistoryGraph Nat where
  Path := PPath
  Deformation := PDef
  idPath := PPath.id
  compPath := PPath.comp

/-! Microstates and semantics -/

abbrev State := LagState Nat Bool
abbrev obs : State → Nat := lagObs
def target_obs : Nat → Nat := fun n => n

def R_pq (n : Nat) : Relation State State :=
  fun a b => a.visible = n ∧ b.visible = n ∧ b.hidden = false

def R_step (n : Nat) : Relation State State :=
  fun a b =>
    a.visible = n ∧ b.visible = n ∧
    ( (Provable n ∧ a.hidden = false ∧ b.hidden = false)
      ∨ ((¬ Provable n) ∧ a.hidden = true ∧ b.hidden = true) )

def sem : {h k : Nat} → PPath h k → Relation State State
  | _, _, PPath.id _     => relId
  | _, _, PPath.p n      => R_pq n
  | _, _, PPath.q n      => R_pq n
  | _, _, PPath.step n   => R_step (Provable := Provable) n
  | _, _, PPath.comp u v => relComp (sem u) (sem v)

theorem sem_id (h : Nat) : RelEq (sem (Provable := Provable) (HistoryGraph.idPath h)) relId := by
  intro x y; dsimp [sem]; rfl

theorem sem_comp {h k l : Nat} (u : HistoryGraph.Path h k) (v : HistoryGraph.Path k l) :
    RelEq (sem (Provable := Provable) (HistoryGraph.compPath u v))
          (relComp (sem (Provable := Provable) u) (sem (Provable := Provable) v)) := by
  intro x y; dsimp [sem]; rfl

def semantics : Semantics Nat State where
  sem := sem (Provable := Provable)
  sem_id := sem_id (Provable := Provable)
  sem_comp := sem_comp (Provable := Provable)

/-! Build LagEvent at g = diag e -/

def g (e : Nat) : Nat := D.diag e

/-- The diagonal fiber (over the diagonal code `g e`). -/
abbrev DiagFiber (e : Nat) : Type :=
  FiberPt (P := Nat) obs target_obs (g (D := D) e)

def x (e : Nat) : FiberPt (P := Nat) obs target_obs (g (D := D) e) :=
  ⟨⟨g (D := D) e, false⟩, rfl⟩

def x' (e : Nat) : FiberPt (P := Nat) obs target_obs (g (D := D) e) :=
  ⟨⟨g (D := D) e, true⟩, rfl⟩

theorem x_ne_x' (e : Nat) : x (D := D) e ≠ x' (D := D) e := by
  intro h
  have : (x (D := D) e).1 = (x' (D := D) e).1 := congrArg Subtype.val h
  have : false = true := congrArg LagState.hidden this
  exact Bool.noConfusion this

/-- The diagonal fiber at `g e` has exactly the two points `x e` and `x' e`. -/
theorem diag_fiber_cases (e : Nat)
    (z : FiberPt (P := Nat) obs target_obs (g (D := D) e)) :
    z = x (D := D) e ∨ z = x' (D := D) e := by
  rcases z with ⟨⟨vis, hid⟩, hz⟩
  have hvis : vis = g (D := D) e := by
    simpa [obs, target_obs] using hz
  cases hid with
  | false =>
      left
      apply Subtype.ext
      cases hvis
      rfl
  | true =>
      right
      apply Subtype.ext
      cases hvis
      rfl

/-- Reduce a `∀ z z'` statement on the diagonal fiber to the four Boolean cases. -/
theorem forall_diag_fiber_iff (e : Nat)
    (P :
      FiberPt (P := Nat) obs target_obs (g (D := D) e) →
        FiberPt (P := Nat) obs target_obs (g (D := D) e) → Prop) :
    (∀ z z', P z z') ↔
      P (x (D := D) e) (x (D := D) e)
      ∧ P (x (D := D) e) (x' (D := D) e)
      ∧ P (x' (D := D) e) (x (D := D) e)
      ∧ P (x' (D := D) e) (x' (D := D) e) := by
  constructor
  · intro h
    refine ⟨h (x (D := D) e) (x (D := D) e), ?_⟩
    refine ⟨h (x (D := D) e) (x' (D := D) e), ?_⟩
    refine ⟨h (x' (D := D) e) (x (D := D) e), h (x' (D := D) e) (x' (D := D) e)⟩
  · rintro ⟨hxx, hxx', hx'x, hx'x'⟩
    intro z z'
    rcases diag_fiber_cases (D := D) e z with rfl | rfl <;>
      rcases diag_fiber_cases (D := D) e z' with rfl | rfl
    · exact hxx
    · exact hxx'
    · exact hx'x
    · exact hx'x'

/- Convenience alias: the same reduction lemma, typed using `DiagFiber`. -/
theorem forall2_diag_fiber_iff (e : Nat)
    (P : DiagFiber (D := D) e → DiagFiber (D := D) e → Prop) :
    (∀ z z', P z z') ↔
      P (x (D := D) e) (x (D := D) e)
      ∧ P (x (D := D) e) (x' (D := D) e)
      ∧ P (x' (D := D) e) (x (D := D) e)
      ∧ P (x' (D := D) e) (x' (D := D) e) := by
  constructor
  · intro h
    refine ⟨h (x (D := D) e) (x (D := D) e), ?_⟩
    refine ⟨h (x (D := D) e) (x' (D := D) e), ?_⟩
    refine ⟨h (x' (D := D) e) (x (D := D) e), h (x' (D := D) e) (x' (D := D) e)⟩
  · rintro ⟨hxx, hxx', hx'x, hx'x'⟩
    intro z z'
    rcases diag_fiber_cases (D := D) e z with rfl | rfl <;>
      rcases diag_fiber_cases (D := D) e z' with rfl | rfl
    · exact hxx
    · exact hxx'
    · exact hx'x
    · exact hx'x'

def α (e : Nat) : PDef (PPath.p (g (D := D) e)) (PPath.q (g (D := D) e)) :=
  PDef.pq _

def y (e : Nat) : FiberPt (P := Nat) obs target_obs (g (D := D) e) :=
  ⟨⟨g (D := D) e, false⟩, rfl⟩

theorem transport_p_x_y (e : Nat) :
    Transport (P := Nat) (@semantics Provable) obs target_obs (PPath.p (g (D := D) e))
      (x (D := D) e) (y (D := D) e) := by
  dsimp [Transport, semantics, sem, R_pq]
  exact ⟨rfl, rfl, rfl⟩

theorem transport_p_x'_y (e : Nat) :
    Transport (P := Nat) (@semantics Provable) obs target_obs (PPath.p (g (D := D) e))
      (x' (D := D) e) (y (D := D) e) := by
  dsimp [Transport, semantics, sem, R_pq]
  exact ⟨rfl, rfl, rfl⟩

theorem transport_q_x_y (e : Nat) :
    Transport (P := Nat) (@semantics Provable) obs target_obs (PPath.q (g (D := D) e))
      (x (D := D) e) (y (D := D) e) := by
  dsimp [Transport, semantics, sem, R_pq]
  exact ⟨rfl, rfl, rfl⟩

theorem transport_q_x'_y (e : Nat) :
    Transport (P := Nat) (@semantics Provable) obs target_obs (PPath.q (g (D := D) e))
      (x' (D := D) e) (y (D := D) e) := by
  dsimp [Transport, semantics, sem, R_pq]
  exact ⟨rfl, rfl, rfl⟩

theorem holonomy_x_x' (e : Nat) :
    HolonomyRel (P := Nat) (@semantics Provable) obs target_obs (α (D := D) e)
      (x (D := D) e) (x' (D := D) e) := by
  refine ⟨y (D := D) e, ?_, ?_⟩
  · exact transport_p_x_y (D := D) e
  · exact transport_q_x'_y (D := D) e

theorem compatible_step_x_of_provable (e : Nat)
    (hP : Provable (g (D := D) e)) :
    Compatible (P := Nat) (@semantics Provable) obs target_obs (PPath.step (g (D := D) e))
      (x (D := D) e) := by
  refine ⟨x (D := D) e, ?_⟩
  dsimp [Transport, semantics, sem, R_step]
  refine ⟨rfl, rfl, ?_⟩
  left; exact ⟨hP, rfl, rfl⟩

theorem not_compatible_step_x'_of_provable (e : Nat)
    (hP : Provable (g (D := D) e)) :
    ¬ Compatible (P := Nat) (@semantics Provable) obs target_obs (PPath.step (g (D := D) e))
        (x' (D := D) e) := by
  intro hC
  rcases hC with ⟨z, hz⟩
  dsimp [Transport, semantics, sem, R_step] at hz
  rcases hz with ⟨_hxvis, _hzvis, hcases⟩
  cases hcases with
  | inl h =>
      rcases h with ⟨_hP', hxhiddenFalse, _hzhiddenFalse⟩
      have hxhidden : (x' (D := D) e).1.hidden = true := rfl
      have : (true : Bool) = false := hxhidden.symm.trans hxhiddenFalse
      exact Bool.noConfusion this
  | inr h =>
      rcases h with ⟨hNP', _hxhiddenTrue, _hzhiddenTrue⟩
      exact hNP' hP

theorem compatible_step_x'_of_not_provable (e : Nat)
    (hNP : ¬ Provable (g (D := D) e)) :
    Compatible (P := Nat) (@semantics Provable) obs target_obs (PPath.step (g (D := D) e))
      (x' (D := D) e) := by
  refine ⟨x' (D := D) e, ?_⟩
  dsimp [Transport, semantics, sem, R_step]
  refine ⟨rfl, rfl, ?_⟩
  right; exact ⟨hNP, rfl, rfl⟩

theorem not_compatible_step_x_of_not_provable (e : Nat)
    (hNP : ¬ Provable (g (D := D) e)) :
    ¬ Compatible (P := Nat) (@semantics Provable) obs target_obs (PPath.step (g (D := D) e))
        (x (D := D) e) := by
  intro hC
  rcases hC with ⟨z, hz⟩
  dsimp [Transport, semantics, sem, R_step] at hz
  rcases hz with ⟨_hxvis, _hzvis, hcases⟩
  cases hcases with
  | inl h =>
      rcases h with ⟨hP', _hxhiddenFalse, _hzhiddenFalse⟩
      exact hNP hP'
  | inr h =>
      rcases h with ⟨_hNP', hxhiddenTrue, _hzhiddenTrue⟩
      have hxhidden : (x (D := D) e).1.hidden = false := rfl
      have : (false : Bool) = true := hxhidden.symm.trans hxhiddenTrue
      exact Bool.noConfusion this

/-- Strong constructive form: ∀e, ∃ LagEvent(e). -/
theorem lagEvent_at_diag (e : Nat) :
    LagEvent (P := Nat) (@semantics Provable) obs target_obs (α (D := D) e)
      (PPath.step (g (D := D) e)) := by
  have hspec := (D.diag_spec e)
  by_cases hU : U e (g (D := D) e) = false
  · have hP : Provable (g (D := D) e) := (hspec).2 hU
    refine lag_of_witness (P := Nat) (@semantics Provable) obs target_obs
      (α (D := D) e) (PPath.step (g (D := D) e))
      (x (D := D) e) (x' (D := D) e) (x_ne_x' (D := D) e)
      (holonomy_x_x' (D := D) e) ?_
    exact ⟨compatible_step_x_of_provable (D := D) e hP,
           not_compatible_step_x'_of_provable (D := D) e hP⟩
  · have hNP : ¬ Provable (g (D := D) e) := by
      intro hP
      have : U e (g (D := D) e) = false := (hspec).1 hP
      exact hU this
    refine lag_of_witness (P := Nat) (@semantics Provable) obs target_obs
      (α (D := D) e) (PPath.step (g (D := D) e))
      (x' (D := D) e) (x (D := D) e) (by
        intro h; exact (x_ne_x' (D := D) e) h.symm)
      (by
        refine ⟨y (D := D) e, ?_, ?_⟩
        · dsimp [Transport, semantics, sem, R_pq]; exact ⟨rfl, rfl, rfl⟩
        · dsimp [Transport, semantics, sem, R_pq]; exact ⟨rfl, rfl, rfl⟩)
      ?_
    exact ⟨compatible_step_x'_of_not_provable (D := D) e hNP,
           not_compatible_step_x_of_not_provable (D := D) e hNP⟩


/-- The diagonal 2-cell attached to code `e`. -/
def diagCell (e : Nat) : Cell (P := Nat) :=
  ⟨g (D := D) e, g (D := D) e,
    PPath.p (g (D := D) e), PPath.q (g (D := D) e),
    ⟨α (D := D) e⟩⟩

/-- At the diagonal point, the primitive holonomy is genuinely twisted. -/
theorem twistedHolonomy_at_diag (e : Nat) :
    TwistedHolonomy (P := Nat) (@semantics Provable) obs target_obs (α (D := D) e) := by
  refine ⟨x (D := D) e, x' (D := D) e, x_ne_x' (D := D) e, ?_⟩
  exact holonomy_x_x' (D := D) e

/--
Any summary depending only on the visible component identifies two states that
the diagonal future step separates.
-/
theorem diag_lag_breaks_visible_summaries
    (e : Nat) {Q : Type _}
    (σ : FiberPt (P := Nat) obs target_obs (g (D := D) e) → Q)
    (hσ : ∃ f : Nat → Q, ∀ z, σ z = f (obs z.1)) :
    ∃ z z' : FiberPt (P := Nat) obs target_obs (g (D := D) e),
      σ z = σ z' ∧
      Compatible (P := Nat) (@semantics Provable) obs target_obs
        (PPath.step (g (D := D) e)) z ∧
      ¬ Compatible (P := Nat) (@semantics Provable) obs target_obs
        (PPath.step (g (D := D) e)) z' := by
  exact
    lagEvent_gives_summary_witness
      (P := Nat) (@semantics Provable) obs target_obs
      (α := α (D := D) e)
      (step := PPath.step (g (D := D) e))
      σ hσ
      (lagEvent_at_diag (Provable := Provable) (U := U) (D := D) e)

/--
The diagonal cell cannot be flattened by any gauge that contains the fiber diagonal.
-/
theorem diag_not_autoRegulatedWrt_singleton_gaugeRefl (e : Nat) :
    ¬ AutoRegulatedWrt (P := Nat) (@semantics Provable) obs target_obs
      (fun φ => GaugeRefl (P := Nat) obs target_obs φ)
      (Set.singleton (diagCell (D := D) e)) := by
  dsimp [diagCell]
  exact
    not_autoRegulatedWrt_singleton_of_twistedHolonomy_of_gaugeRefl
      (P := Nat) (@semantics Provable) obs target_obs
      (α := α (D := D) e)
      (twistedHolonomy_at_diag (Provable := Provable) (U := U) (D := D) e)

/--
The diagonal cell is obstructed against every gauge containing the fiber diagonal.
-/
theorem diag_obstructionWrt_singleton_gaugeRefl (e : Nat) :
    ObstructionWrt (P := Nat) (@semantics Provable) obs target_obs
      (fun φ => GaugeRefl (P := Nat) obs target_obs φ)
      (Set.singleton (diagCell (D := D) e)) := by
  dsimp [diagCell]
  exact
    obstructionWrt_singleton_of_twistedHolonomy_of_gaugeRefl
      (P := Nat) (@semantics Provable) obs target_obs
      (α := α (D := D) e)
      (twistedHolonomy_at_diag (Provable := Provable) (U := U) (D := D) e)
/--
Compact package of the four main diagonal consequences:
twist, lag, obstruction, and failure of admissible global repair.
-/
theorem diag_rich_witness (e : Nat) :
    TwistedHolonomy (P := Nat) (@semantics Provable) obs target_obs (α (D := D) e)
    ∧ LagEvent (P := Nat) (@semantics Provable) obs target_obs
        (α (D := D) e) (PPath.step (g (D := D) e))
    ∧ ObstructionWrt (P := Nat) (@semantics Provable) obs target_obs
        (fun φ => GaugeRefl (P := Nat) obs target_obs φ)
        (Set.singleton (diagCell (D := D) e))
    ∧ ¬ AutoRegulatedWrt (P := Nat) (@semantics Provable) obs target_obs
        (fun φ => GaugeRefl (P := Nat) obs target_obs φ)
        (Set.singleton (diagCell (D := D) e)) := by
  refine ⟨twistedHolonomy_at_diag (Provable := Provable) (U := U) (D := D) e,
          lagEvent_at_diag (Provable := Provable) (U := U) (D := D) e,
          diag_obstructionWrt_singleton_gaugeRefl (Provable := Provable) (U := U) (D := D) e,
          diag_not_autoRegulatedWrt_singleton_gaugeRefl (Provable := Provable) (U := U) (D := D) e⟩




/--
Canonical classification instance: the diagonal cell fits the internal dynamic no-go package.
-/
theorem diag_diagonalDynamicClass (e : Nat) :
    DiagonalDynamicClass (P := Nat) (@semantics Provable) obs target_obs
      (h := g (D := D) e) (k := g (D := D) e) (k' := g (D := D) e)
      (p := PPath.p (g (D := D) e)) (q := PPath.q (g (D := D) e))
      (α := α (D := D) e)
      (PPath.step (g (D := D) e)) := by
  refine ⟨
    twistedHolonomy_at_diag (Provable := Provable) (U := U) (D := D) e,
    lagEvent_at_diag (Provable := Provable) (U := U) (D := D) e,
    ?_,
    ?_,
    ?_⟩
  · -- lag implies no visible predictor for the diagonal step
    exact
      not_visiblePredictsStep_of_lagEvent (P := Nat) (@semantics Provable) obs target_obs
        (h := g (D := D) e) (k := g (D := D) e) (k' := g (D := D) e)
        (p := PPath.p (g (D := D) e)) (q := PPath.q (g (D := D) e))
        (α := α (D := D) e)
        (step := PPath.step (g (D := D) e))
        (lagEvent_at_diag (Provable := Provable) (U := U) (D := D) e)
  · -- obstruction under admissible (reflexive) gauges
    simpa [diagCell] using
      diag_obstructionWrt_singleton_gaugeRefl (Provable := Provable) (U := U) (D := D) e
  · -- not auto-regulated under admissible (reflexive) gauges
    simpa [diagCell] using
      diag_not_autoRegulatedWrt_singleton_gaugeRefl (Provable := Provable) (U := U) (D := D) e



/-- Compatibility of the diagonal step depends only on the hidden boolean. -/
theorem diag_compatible_step_iff_hidden
    (e : Nat)
    (z : FiberPt (P := Nat) obs target_obs (g (D := D) e)) :
    Compatible (P := Nat) (@semantics Provable) obs target_obs
      (h := g (D := D) e) (k := g (D := D) e) (PPath.step (g (D := D) e)) z ↔
      ((Provable (g (D := D) e) ∧ z.1.hidden = false) ∨
        ((¬ Provable (g (D := D) e)) ∧ z.1.hidden = true)) := by
  constructor
  · intro hC
    rcases hC with ⟨y, hy⟩
    dsimp [Transport, semantics, sem, R_step] at hy
    rcases hy with ⟨_hzVis, _hyVis, hBranch⟩
    rcases hBranch with hP | hNP
    · rcases hP with ⟨hP, hzH, _hyH⟩
      exact Or.inl ⟨hP, hzH⟩
    · rcases hNP with ⟨hNP, hzH, _hyH⟩
      exact Or.inr ⟨hNP, hzH⟩
  · intro h
    refine ⟨z, ?_⟩
    have hzVis : z.1.visible = g (D := D) e := by
      have : obs z.1 = target_obs (g (D := D) e) := z.2
      simpa [obs, target_obs] using this
    dsimp [Transport, semantics, sem, R_step]
    refine ⟨hzVis, hzVis, ?_⟩
    rcases h with ⟨hP, hzH⟩ | ⟨hNP, hzH⟩
    · left
      exact ⟨hP, hzH, hzH⟩
    · right
      exact ⟨hNP, hzH, hzH⟩

/-- The diagonal compatibility predicate is classified by at most 2 hidden classes (one hidden bit). -/
theorem diag_hiddenCompatClassifiedByFin_two_step (e : Nat) :
    HiddenCompatClassifiedByFin (@semantics Provable) target_obs
      (h := g (D := D) e) (k := g (D := D) e)
      (PPath.step (g (D := D) e)) 2 := by
  let n : Nat := g (D := D) e
  let fin0 : Fin 2 := ⟨0, by decide⟩
  let fin1 : Fin 2 := ⟨1, by decide⟩
  let τ : FiberPt (P := Nat) obs target_obs n → Fin 2 :=
    fun z =>
      match z.1.hidden with
      | false => fin0
      | true => fin1
  let pred : Fin 2 → Prop :=
    fun i => if i.val = 0 then Provable n else ¬ Provable n
  refine ⟨τ, pred, ?_, ?_⟩
  · intro z z' hhid
    -- `τ` depends only on the hidden bit.
    dsimp [τ]
    exact congrArg (fun b => match b with | false => fin0 | true => fin1) hhid
  · intro z
    have hCompat :=
      diag_compatible_step_iff_hidden (Provable := Provable) (U := U) (D := D) e z

    have hPred0 : pred fin0 ↔ Provable n := by
      dsimp [pred, fin0]
      rfl

    have hPred1 : pred fin1 ↔ ¬ Provable n := by
      dsimp [pred, fin1]
      rfl

    cases hz : z.1.hidden
    · -- hidden = false
      have hCompat' : Compatible (P := Nat) (@semantics Provable) obs target_obs
          (h := n) (k := n) (PPath.step n) z ↔ Provable n := by
        constructor
        · intro hC
          rcases hCompat.mp hC with hP | hNP
          · exact hP.1
          · exfalso
            exact Bool.false_ne_true (hz.symm.trans hNP.2)
        · intro hP
          exact hCompat.mpr (Or.inl ⟨hP, hz⟩)

      have hτ : τ z = fin0 := by
        dsimp [τ]
        rw [hz]
      have hPredτ : pred (τ z) ↔ pred fin0 :=
        PrimitiveHolonomy.iff_of_eq (congrArg pred hτ)
      exact hCompat'.trans ((hPredτ.trans hPred0).symm)

    · -- hidden = true
      have hCompat' : Compatible (P := Nat) (@semantics Provable) obs target_obs
          (h := n) (k := n) (PPath.step n) z ↔ ¬ Provable n := by
        constructor
        · intro hC
          rcases hCompat.mp hC with hP | hNP
          · exfalso
            have : false = true := (hz.symm.trans hP.2).symm
            exact Bool.false_ne_true this
          · exact hNP.1
        · intro hNP
          exact hCompat.mpr (Or.inr ⟨hNP, hz⟩)

      have hτ : τ z = fin1 := by
        dsimp [τ]
        rw [hz]
      have hPredτ : pred (τ z) ↔ pred fin1 :=
        PrimitiveHolonomy.iff_of_eq (congrArg pred hτ)
      exact hCompat'.trans ((hPredτ.trans hPred1).symm)

/-- The diagonal compatibility predicate has dimension ≤ 2 (one hidden bit). -/
theorem diag_compatDimLe_two_step (e : Nat) :
    CompatDimLe (P := Nat) (@semantics Provable) obs target_obs
      (h := g (D := D) e) (k := g (D := D) e)
      (PPath.step (g (D := D) e)) 2 := by
  exact
    compatDimLe_of_hiddenCompatClassifiedByFin (@semantics Provable) target_obs
      (h := g (D := D) e) (k := g (D := D) e)
      (step := PPath.step (g (D := D) e)) 2
      (diag_hiddenCompatClassifiedByFin_two_step (Provable := Provable) (U := U) (D := D) e)

/-!
### Global compression of the canonical mediator on the diagonal fiber

`CompatDimLe … step n` is step-local. On the diagonal fiber, we can also compress the full
future-compatibility signature `Sig : Future h → Prop` into one hidden bit (i.e. `Fin 2`).

This is the instance-level bridge to the canonical-mediator layer in `COFRS/Dynamics.lean`.
-/

/-- On the diagonal fiber, the full signature `Sig` admits a global `Fin 2` compression. -/
theorem diag_compatSigDimLe_two (e : Nat) :
    CompatSigDimLe (P := Nat) (@semantics Provable) obs target_obs
      (h := g (D := D) e) 2 := by
  let fin0 : Fin 2 := ⟨0, by decide⟩
  let fin1 : Fin 2 := ⟨1, by decide⟩
  let σ : FiberPt (P := Nat) obs target_obs (g (D := D) e) → Fin 2 :=
    fun z => match z.1.hidden with | false => fin0 | true => fin1
  let pred : Fin 2 → Future (P := Nat) (g (D := D) e) → Prop :=
    fun i step =>
      if i.val = 0 then
        CompatibleFuture (P := Nat) (@semantics Provable) obs target_obs step (x (D := D) e)
      else
        CompatibleFuture (P := Nat) (@semantics Provable) obs target_obs step (x' (D := D) e)
  refine ⟨σ, pred, ?_⟩
  intro z step
  rcases diag_fiber_cases (D := D) e z with rfl | rfl
  · -- z = x
    have hσ : σ (x (D := D) e) = fin0 := by rfl
    have hPred : pred (σ (x (D := D) e)) step ↔ pred fin0 step := by
      exact PrimitiveHolonomy.iff_of_eq (congrArg (fun i => pred i step) hσ)
    have hPred0 : pred fin0 step ↔
        CompatibleFuture (P := Nat) (@semantics Provable) obs target_obs step (x (D := D) e) := by
      dsimp [pred, fin0]
      rfl
    exact (hPred.trans hPred0)
  · -- z = x'
    have hσ : σ (x' (D := D) e) = fin1 := by rfl
    have hPred : pred (σ (x' (D := D) e)) step ↔ pred fin1 step := by
      exact PrimitiveHolonomy.iff_of_eq (congrArg (fun i => pred i step) hσ)
    have hPred1 : pred fin1 step ↔
        CompatibleFuture (P := Nat) (@semantics Provable) obs target_obs step (x' (D := D) e) := by
      dsimp [pred, fin1]
      rfl
    exact (hPred.trans hPred1)

/-- On the diagonal fiber, the full signature `Sig` cannot be compressed into `Fin 1`. -/
theorem diag_not_compatSigDimLe_one (e : Nat) :
    ¬ CompatSigDimLe (P := Nat) (@semantics Provable) obs target_obs
        (h := g (D := D) e) 1 := by
  intro hSig1
  have hDim1 :
      CompatDimLe (P := Nat) (@semantics Provable) obs target_obs
        (h := g (D := D) e) (k := g (D := D) e)
        (PPath.step (g (D := D) e)) 1 :=
    (compatDimLe_of_compatSigDimLe (P := Nat) (@semantics Provable) obs target_obs
      (step := PPath.step (g (D := D) e)) (h := g (D := D) e)) hSig1
  have hNoDim1 :
      ¬ CompatDimLe (P := Nat) (@semantics Provable) obs target_obs
        (h := g (D := D) e) (k := g (D := D) e)
        (PPath.step (g (D := D) e)) 1 :=
    not_compatDimLe_one_of_lagEvent (P := Nat) (@semantics Provable) obs target_obs
      (h := g (D := D) e) (k := g (D := D) e) (k' := g (D := D) e)
      (p := PPath.p (g (D := D) e)) (q := PPath.q (g (D := D) e))
      (α := α (D := D) e)
      (step := PPath.step (g (D := D) e))
      (lagEvent_at_diag (Provable := Provable) (U := U) (D := D) e)
  exact hNoDim1 hDim1

/-- On the diagonal fiber, global `Fin 0` compression of `Sig` is impossible. -/
theorem diag_not_compatSigDimLe_zero (e : Nat) :
    ¬ CompatSigDimLe (P := Nat) (@semantics Provable) obs target_obs
        (h := g (D := D) e) 0 := by
  rintro ⟨σ, _pred, _Hcorr⟩
  have h0 : Fin 0 := σ (x (D := D) e)
  exact Fin.elim0 h0

/-- Corollary: on the diagonal fiber, the canonical mediator `Sig` factors through `Fin 2`. -/
theorem diag_sigFactorsThrough_two (e : Nat) :
    ∃ σ : FiberPt (P := Nat) obs target_obs (g (D := D) e) → Fin 2,
      SigFactorsThrough (P := Nat) (@semantics Provable) obs target_obs σ := by
  exact
    sigFactorsThrough_of_compatSigDimLe (P := Nat) (@semantics Provable) obs target_obs
      (h := g (D := D) e) (n := 2)
      (diag_compatSigDimLe_two (Provable := Provable) (U := U) (D := D) e)

/--
On the diagonal fiber, the hidden bit classifies *exactly* the canonical future signature:
two states have the same hidden bit iff they have the same `Sig` on all future steps.
-/
theorem diag_hidden_eq_iff_sameSig (e : Nat)
    (z z' : FiberPt (P := Nat) obs target_obs (g (D := D) e)) :
    z.1.hidden = z'.1.hidden ↔
      (∀ step : Future (P := Nat) (g (D := D) e),
        Sig (P := Nat) (@semantics Provable) obs target_obs z step ↔
          Sig (P := Nat) (@semantics Provable) obs target_obs z' step) := by
  rcases diag_fiber_cases (D := D) e z with rfl | rfl <;>
    rcases diag_fiber_cases (D := D) e z' with rfl | rfl
  · -- (x, x)
    constructor
    · intro _h; intro step; rfl
    · intro _hAll; rfl
  · -- (x, x')
    constructor
    · intro h
      cases h
    · intro hAll
      have hspec := (D.diag_spec e)
      let step0 : Future (P := Nat) (g (D := D) e) := ⟨g (D := D) e, PPath.step (g (D := D) e)⟩
      have hIff := hAll step0
      have hContra : False := by
        by_cases hU : U e (g (D := D) e) = false
        · have hP : Provable (g (D := D) e) := (hspec).2 hU
          have hxC :
              Compatible (P := Nat) (@semantics Provable) obs target_obs (PPath.step (g (D := D) e))
                (x (D := D) e) :=
            compatible_step_x_of_provable (Provable := Provable) (U := U) (D := D) e hP
          have hx'C :
              ¬ Compatible (P := Nat) (@semantics Provable) obs target_obs (PPath.step (g (D := D) e))
                  (x' (D := D) e) :=
            not_compatible_step_x'_of_provable (Provable := Provable) (U := U) (D := D) e hP
          have hxSig :
              Sig (P := Nat) (@semantics Provable) obs target_obs (x (D := D) e) step0 := by
            simpa [Sig, CompatibleFuture, step0] using hxC
          have hx'Sig :
              ¬ Sig (P := Nat) (@semantics Provable) obs target_obs (x' (D := D) e) step0 := by
            simpa [Sig, CompatibleFuture, step0] using hx'C
          exact hx'Sig (hIff.mp hxSig)
        · have hNP : ¬ Provable (g (D := D) e) := by
            intro hP
            have : U e (g (D := D) e) = false := (hspec).1 hP
            exact hU this
          have hxC :
              ¬ Compatible (P := Nat) (@semantics Provable) obs target_obs (PPath.step (g (D := D) e))
                  (x (D := D) e) :=
            not_compatible_step_x_of_not_provable (Provable := Provable) (U := U) (D := D) e hNP
          have hx'C :
              Compatible (P := Nat) (@semantics Provable) obs target_obs (PPath.step (g (D := D) e))
                (x' (D := D) e) :=
            compatible_step_x'_of_not_provable (Provable := Provable) (U := U) (D := D) e hNP
          have hxSig :
              ¬ Sig (P := Nat) (@semantics Provable) obs target_obs (x (D := D) e) step0 := by
            simpa [Sig, CompatibleFuture, step0] using hxC
          have hx'Sig :
              Sig (P := Nat) (@semantics Provable) obs target_obs (x' (D := D) e) step0 := by
            simpa [Sig, CompatibleFuture, step0] using hx'C
          exact hxSig (hIff.mpr hx'Sig)
      exact False.elim hContra
  · -- (x', x)
    constructor
    · intro h
      cases h
    · intro hAll
      have hspec := (D.diag_spec e)
      let step0 : Future (P := Nat) (g (D := D) e) := ⟨g (D := D) e, PPath.step (g (D := D) e)⟩
      have hIff := hAll step0
      have hContra : False := by
        by_cases hU : U e (g (D := D) e) = false
        · have hP : Provable (g (D := D) e) := (hspec).2 hU
          have hxC :
              Compatible (P := Nat) (@semantics Provable) obs target_obs (PPath.step (g (D := D) e))
                (x (D := D) e) :=
            compatible_step_x_of_provable (Provable := Provable) (U := U) (D := D) e hP
          have hx'C :
              ¬ Compatible (P := Nat) (@semantics Provable) obs target_obs (PPath.step (g (D := D) e))
                  (x' (D := D) e) :=
            not_compatible_step_x'_of_provable (Provable := Provable) (U := U) (D := D) e hP
          have hxSig :
              Sig (P := Nat) (@semantics Provable) obs target_obs (x (D := D) e) step0 := by
            simpa [Sig, CompatibleFuture, step0] using hxC
          have hx'Sig :
              ¬ Sig (P := Nat) (@semantics Provable) obs target_obs (x' (D := D) e) step0 := by
            simpa [Sig, CompatibleFuture, step0] using hx'C
          exact hx'Sig (hIff.mpr hxSig)
        · have hNP : ¬ Provable (g (D := D) e) := by
            intro hP
            have : U e (g (D := D) e) = false := (hspec).1 hP
            exact hU this
          have hxC :
              ¬ Compatible (P := Nat) (@semantics Provable) obs target_obs (PPath.step (g (D := D) e))
                  (x (D := D) e) :=
            not_compatible_step_x_of_not_provable (Provable := Provable) (U := U) (D := D) e hNP
          have hx'C :
              Compatible (P := Nat) (@semantics Provable) obs target_obs (PPath.step (g (D := D) e))
                (x' (D := D) e) :=
            compatible_step_x'_of_not_provable (Provable := Provable) (U := U) (D := D) e hNP
          have hxSig :
              ¬ Sig (P := Nat) (@semantics Provable) obs target_obs (x (D := D) e) step0 := by
            simpa [Sig, CompatibleFuture, step0] using hxC
          have hx'Sig :
              Sig (P := Nat) (@semantics Provable) obs target_obs (x' (D := D) e) step0 := by
            simpa [Sig, CompatibleFuture, step0] using hx'C
          exact hxSig (hIff.mp hx'Sig)
      exact False.elim hContra
  · -- (x', x')
    constructor
    · intro _h; intro step; rfl
    · intro _hAll; rfl

/-- On the diagonal fiber, the canonical mediator has global exact dimension `2`. -/
theorem diag_compatSigDimEqTwo (e : Nat) :
    CompatSigDimEqTwo (P := Nat) (@semantics Provable) obs target_obs
      (h := g (D := D) e) := by
  refine ⟨diag_compatSigDimLe_two (Provable := Provable) (U := U) (D := D) e, ?_⟩
  intro m hm
  cases m with
  | zero =>
      exact diag_not_compatSigDimLe_zero (Provable := Provable) (U := U) (D := D) e
  | succ m =>
      cases m with
      | zero =>
          -- m = 1
          exact diag_not_compatSigDimLe_one (Provable := Provable) (U := U) (D := D) e
      | succ m =>
          -- m ≥ 2 contradicts `m < 2`
          intro _h
          have hge : 2 ≤ Nat.succ (Nat.succ m) :=
            Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le m))
          exact False.elim ((Nat.not_lt_of_ge hge) hm)

/--
Packaging of global exactness on the diagonal fiber:
there exists a binary summary that respects the canonical mediator `Sig`,
and no strictly smaller finite summary can respect `Sig`.
-/
theorem diag_exists_sigFactorsThrough_two_and_no_smaller (e : Nat) :
    ∃ σ : FiberPt (P := Nat) obs target_obs (g (D := D) e) → Fin 2,
      SigFactorsThrough (P := Nat) (@semantics Provable) obs target_obs σ
      ∧ ∀ m : Nat, m < 2 →
          ¬ (∃ σm : FiberPt (P := Nat) obs target_obs (g (D := D) e) → Fin m,
              SigFactorsThrough (P := Nat) (@semantics Provable) obs target_obs σm) := by
  have hEq :
      CompatSigDimEq (P := Nat) (@semantics Provable) obs target_obs
        (h := g (D := D) e) 2 := by
    simpa [CompatSigDimEqTwo] using
      (diag_compatSigDimEqTwo (Provable := Provable) (U := U) (D := D) e)
  rcases
      exists_sigFactorsThrough_of_compatSigDimEq
        (P := Nat) (@semantics Provable) obs target_obs (h := g (D := D) e) (n := 2) hEq with
    ⟨σ, hσ, hMin⟩
  exact ⟨σ, hσ, hMin⟩

/-- The diagonal compatibility predicate has dimension exactly 2. -/
theorem diag_compatDimEqTwo_step (e : Nat) :
    CompatDimEqTwo (P := Nat) (@semantics Provable) obs target_obs
      (h := g (D := D) e) (k := g (D := D) e)
      (PPath.step (g (D := D) e)) := by
  exact
    compatDimEqTwo_of_lagEvent_and_hiddenCompatClassifiedByFin_two
      (@semantics Provable) target_obs
      (h := g (D := D) e) (k := g (D := D) e) (k' := g (D := D) e)
      (p := PPath.p (g (D := D) e)) (q := PPath.q (g (D := D) e))
      (α := α (D := D) e)
      (step := PPath.step (g (D := D) e))
      (lagEvent_at_diag (Provable := Provable) (U := U) (D := D) e)
      (diag_hiddenCompatClassifiedByFin_two_step (Provable := Provable) (U := U) (D := D) e)
/--
A code `e` repairs its diagonal cell if there exists a gauge containing the fiber diagonal
that makes the corrected holonomy on the diagonal cell flat.
-/
def CodeRepairsDiagonalCell (e : Nat) : Prop :=
  ∃ φ : Gauge (P := Nat) obs target_obs,
    GaugeRefl (P := Nat) obs target_obs φ ∧
    ∀ z z' : FiberPt (P := Nat) obs target_obs (g (D := D) e),
      CorrectedHolonomy (P := Nat) (@semantics Provable) obs target_obs φ
        (α (D := D) e) z z' ↔ z = z'

/--
Repairing the diagonal cell is equivalent to auto-regulating the singleton set
containing that cell, with admissible gauges required to contain the fiber diagonal.
-/
theorem codeRepairsDiagonalCell_iff_autoRegulatedSingleton (e : Nat) :
    CodeRepairsDiagonalCell (Provable := Provable) (U := U) (D := D) e ↔
    AutoRegulatedWrt (P := Nat) (@semantics Provable) obs target_obs
      (fun φ => GaugeRefl (P := Nat) obs target_obs φ)
      (Set.singleton (diagCell (D := D) e)) := by
  constructor
  · rintro ⟨φ, hRefl, hFlat⟩
    refine ⟨φ, hRefl, ?_⟩
    intro c hc
    -- No rewriting lemmas: membership in a singleton is definitional here.
    have hc' : c = diagCell (D := D) e := by
      have hc' := hc
      change c = diagCell (D := D) e at hc'
      exact hc'
    subst hc'
    intro z z'
    exact hFlat z z'
  · rintro ⟨φ, hRefl, hFlatAll⟩
    refine ⟨φ, hRefl, ?_⟩
    have hFlat :=
      hFlatAll (diagCell (D := D) e)
        (by
          -- membership in a singleton is definitional
          change diagCell (D := D) e = diagCell (D := D) e
          rfl)
    intro z z'
    exact hFlat z z'

/--
No code can repair its own diagonal cell by an admissible gauge containing the fiber diagonal.
-/
theorem not_codeRepairsDiagonalCell (e : Nat) :
    ¬ CodeRepairsDiagonalCell (Provable := Provable) (U := U) (D := D) e := by
  intro hRepair
  have hAuto :
      AutoRegulatedWrt (P := Nat) (@semantics Provable) obs target_obs
        (fun φ => GaugeRefl (P := Nat) obs target_obs φ)
        (Set.singleton (diagCell (D := D) e)) :=
    (codeRepairsDiagonalCell_iff_autoRegulatedSingleton
      (Provable := Provable) (U := U) (D := D) e).1 hRepair
  exact
    diag_not_autoRegulatedWrt_singleton_gaugeRefl
      (Provable := Provable) (U := U) (D := D) e hAuto

/--
Bridge schema: if every code-level decider induced an admissible repair of its diagonal cell,
then no such decider could exist.
-/
theorem no_decider_of_decider_to_diagonalRepair
    (bridge :
      ∀ e,
        DecidesProvableByCode (Provable := Provable) (U := U) e →
        CodeRepairsDiagonalCell (Provable := Provable) (U := U) (D := D) e) :
    ∀ e, ¬ DecidesProvableByCode (Provable := Provable) (U := U) e := by
  intro e hdec
  have hRepair :
      CodeRepairsDiagonalCell (Provable := Provable) (U := U) (D := D) e :=
    bridge e hdec
  exact
    not_codeRepairsDiagonalCell
      (Provable := Provable) (U := U) (D := D) e hRepair

/-- Code for a procedure queried via `U` to decide gauge membership. -/
structure DiagonalRepairProcedureCode where
  code : Nat

/-
We use a tiny, fully-constructive pairing codec on `Nat` with a custom injectivity lemma.

Important: we intentionally avoid `Mathlib.Data.Nat.Pairing` here, because common lemmas like
`Nat.pair_eq_pair` (and related `unpair` facts) may carry non-constructive dependencies in Mathlib.
-/
 namespace NatCodec

def times2 : Nat → Nat
  | 0 => 0
  | Nat.succ n => Nat.succ (Nat.succ (times2 n))

def evenb : Nat → Bool
  | 0 => true
  | 1 => false
  | Nat.succ (Nat.succ n) => evenb n

theorem evenb_times2 (n : Nat) : evenb (times2 n) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      dsimp [times2, evenb]
      exact ih

theorem evenb_succ_times2 (n : Nat) : evenb (Nat.succ (times2 n)) = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
      -- `succ (times2 (succ n)) = succ (succ (succ (times2 n)))`,
      -- and `evenb (succ (succ x)) = evenb x`.
      dsimp [times2]
      dsimp [evenb]
      exact ih

theorem times2_injective : Function.Injective times2 := by
  intro a b hab
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => rfl
      | succ b =>
          -- `times2 (succ b)` is at least `2`, contradiction with `times2 0 = 0`.
          cases hab
  | succ a ih =>
      cases b with
      | zero =>
          cases hab
      | succ b =>
          -- Peel two `succ` constructors.
          have h1 : Nat.succ (times2 a) = Nat.succ (times2 b) := Nat.succ.inj hab
          have h2 : times2 a = times2 b := Nat.succ.inj h1
          have : a = b := ih h2
          cases this
          rfl

def pair : Nat → Nat → Nat
  | 0, b => times2 b
  | Nat.succ a, b => Nat.succ (times2 (pair a b))

theorem pair_eq_pair {a b c d : Nat} : pair a b = pair c d ↔ a = c ∧ b = d := by
  constructor
  · intro hEq
    induction a generalizing c d with
    | zero =>
        cases c with
        | zero =>
            dsimp [pair] at hEq
            have : b = d := times2_injective hEq
            exact ⟨rfl, this⟩
        | succ c =>
            -- even vs odd via `evenb`
            have hEven : evenb (pair 0 b) = evenb (pair (Nat.succ c) d) := congrArg evenb hEq
            have hL : evenb (pair 0 b) = true := by
              dsimp [pair]
              exact evenb_times2 b
            have hR : evenb (pair (Nat.succ c) d) = false := by
              dsimp [pair]
              exact evenb_succ_times2 (pair c d)
            have : (true : Bool) = false := hL.symm.trans (hEven.trans hR)
            cases this
    | succ a iha =>
        cases c with
        | zero =>
            have hEven : evenb (pair (Nat.succ a) b) = evenb (pair 0 d) := congrArg evenb hEq
            have hL : evenb (pair (Nat.succ a) b) = false := by
              dsimp [pair]
              exact evenb_succ_times2 (pair a b)
            have hR : evenb (pair 0 d) = true := by
              dsimp [pair]
              exact evenb_times2 d
            have : (false : Bool) = true := hL.symm.trans (hEven.trans hR)
            cases this
        | succ c =>
            dsimp [pair] at hEq
            have h1 : times2 (pair a b) = times2 (pair c d) := Nat.succ.inj hEq
            have h2 : pair a b = pair c d := times2_injective h1
            have hrec : a = c ∧ b = d := iha h2
            cases hrec.1
            exact ⟨rfl, hrec.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end NatCodec

/-- A small natural code for `PPath`, used to package gauge queries into a `Nat`. -/
def pPathCode : {h k : Nat} → PPath h k → Nat
  | _, _, PPath.id n => NatCodec.pair 0 n
  | _, _, PPath.p n => NatCodec.pair 1 n
  | _, _, PPath.q n => NatCodec.pair 2 n
  | _, _, PPath.step n => NatCodec.pair 3 n
  | _, _, PPath.comp u v => NatCodec.pair 4 (NatCodec.pair (pPathCode u) (pPathCode v))

theorem pPath_endpoints : ∀ {h k : Nat}, PPath h k → h = k
  | _, _, PPath.id _ => rfl
  | _, _, PPath.p _ => rfl
  | _, _, PPath.q _ => rfl
  | _, _, PPath.step _ => rfl
  | _, _, PPath.comp u v => (pPath_endpoints u).trans (pPath_endpoints v)

/-- Encode a gauge query `(e, p, y, y')` into a single `Nat` input for `U`. -/
def encodeGaugeQuery {h k : Nat} (e : Nat) (p : PPath h k)
    (y y' : FiberPt (P := Nat) obs target_obs k) : Nat :=
  NatCodec.pair e <|
    NatCodec.pair (pPathCode p) <|
      NatCodec.pair (Bool.toNat y.1.hidden) (Bool.toNat y'.1.hidden)

/--
A (coded) gauge-producing procedure: it is reflexive by construction and otherwise delegates
membership queries to `U proc.code`.
-/
def procGauge (proc : DiagonalRepairProcedureCode) : Nat → Gauge (P := Nat) obs target_obs :=
  fun e =>
    fun {_h _k} (p : PPath _h _k) =>
      fun y y' =>
        y = y' ∨ U proc.code (encodeGaugeQuery e p y y') = true

/-- Diagonal corrected holonomy for the coded procedure-gauge. -/
abbrev DiagCH (proc : DiagonalRepairProcedureCode) (e : Nat)
    (z z' : DiagFiber (D := D) e) : Prop :=
  CorrectedHolonomy (P := Nat) (@semantics Provable) obs target_obs (procGauge (U := U) proc e)
    (α (D := D) e) z z'

/--
Unfold `CorrectedHolonomy` for the diagonal cell into a single explicit `∃`-statement.

This is the minimal “unfolding lemma” needed before doing any case analysis on the diagonal fiber.
-/
theorem CorrectedHolonomy_on_diag_unfold (proc : DiagonalRepairProcedureCode) (e : Nat)
    (z z' : DiagFiber (D := D) e) :
    DiagCH (Provable := Provable) (U := U) (D := D) proc e z z' ↔
      ∃ t : DiagFiber (D := D) e,
        (∃ w : DiagFiber (D := D) e,
            Transport (P := Nat) (@semantics Provable) obs target_obs (PPath.p (g (D := D) e)) z w ∧
              procGauge (U := U) proc e (PPath.p (g (D := D) e)) w t)
          ∧
        (∃ w' : DiagFiber (D := D) e,
            Transport (P := Nat) (@semantics Provable) obs target_obs (PPath.q (g (D := D) e)) z' w' ∧
              procGauge (U := U) proc e (PPath.q (g (D := D) e)) w' t) := by
  rfl

theorem DiagCH_x_x_iff (proc : DiagonalRepairProcedureCode) (e : Nat) :
    DiagCH (Provable := Provable) (U := U) (D := D) proc e (x (D := D) e) (x (D := D) e) ↔ True := by
  constructor
  · intro _h
    exact True.intro
  · intro _hTrue
    refine (CorrectedHolonomy_on_diag_unfold (Provable := Provable) (U := U) (D := D) proc e
      (z := x (D := D) e) (z' := x (D := D) e)).2 ?_
    refine ⟨y (D := D) e, ?_, ?_⟩
    · refine ⟨y (D := D) e, transport_p_x_y (Provable := Provable) (U := U) (D := D) e, ?_⟩
      dsimp [procGauge]
      exact Or.inl rfl
    · refine ⟨y (D := D) e, transport_q_x_y (Provable := Provable) (U := U) (D := D) e, ?_⟩
      dsimp [procGauge]
      exact Or.inl rfl

theorem DiagCH_x_x'_iff (proc : DiagonalRepairProcedureCode) (e : Nat) :
    DiagCH (Provable := Provable) (U := U) (D := D) proc e (x (D := D) e) (x' (D := D) e) ↔ True := by
  constructor
  · intro _h
    exact True.intro
  · intro _hTrue
    refine (CorrectedHolonomy_on_diag_unfold (Provable := Provable) (U := U) (D := D) proc e
      (z := x (D := D) e) (z' := x' (D := D) e)).2 ?_
    refine ⟨y (D := D) e, ?_, ?_⟩
    · refine ⟨y (D := D) e, transport_p_x_y (Provable := Provable) (U := U) (D := D) e, ?_⟩
      dsimp [procGauge]
      exact Or.inl rfl
    · refine ⟨y (D := D) e, transport_q_x'_y (Provable := Provable) (U := U) (D := D) e, ?_⟩
      dsimp [procGauge]
      exact Or.inl rfl

theorem DiagCH_x'_x_iff (proc : DiagonalRepairProcedureCode) (e : Nat) :
    DiagCH (Provable := Provable) (U := U) (D := D) proc e (x' (D := D) e) (x (D := D) e) ↔ True := by
  constructor
  · intro _h
    exact True.intro
  · intro _hTrue
    refine (CorrectedHolonomy_on_diag_unfold (Provable := Provable) (U := U) (D := D) proc e
      (z := x' (D := D) e) (z' := x (D := D) e)).2 ?_
    refine ⟨y (D := D) e, ?_, ?_⟩
    · refine ⟨y (D := D) e, transport_p_x'_y (Provable := Provable) (U := U) (D := D) e, ?_⟩
      dsimp [procGauge]
      exact Or.inl rfl
    · refine ⟨y (D := D) e, transport_q_x_y (Provable := Provable) (U := U) (D := D) e, ?_⟩
      dsimp [procGauge]
      exact Or.inl rfl

theorem DiagCH_x'_x'_iff (proc : DiagonalRepairProcedureCode) (e : Nat) :
    DiagCH (Provable := Provable) (U := U) (D := D) proc e (x' (D := D) e) (x' (D := D) e) ↔ True := by
  constructor
  · intro _h
    exact True.intro
  · intro _hTrue
    refine (CorrectedHolonomy_on_diag_unfold (Provable := Provable) (U := U) (D := D) proc e
      (z := x' (D := D) e) (z' := x' (D := D) e)).2 ?_
    refine ⟨y (D := D) e, ?_, ?_⟩
    · refine ⟨y (D := D) e, transport_p_x'_y (Provable := Provable) (U := U) (D := D) e, ?_⟩
      dsimp [procGauge]
      exact Or.inl rfl
    · refine ⟨y (D := D) e, transport_q_x'_y (Provable := Provable) (U := U) (D := D) e, ?_⟩
      dsimp [procGauge]
      exact Or.inl rfl

theorem not_procSound_pointwise (proc : DiagonalRepairProcedureCode) (e : Nat) :
    ¬ (∀ z z' : DiagFiber (D := D) e,
        DiagCH (Provable := Provable) (U := U) (D := D) proc e z z' ↔ z = z') := by
  intro hSound
  have hmix :
      DiagCH (Provable := Provable) (U := U) (D := D) proc e
        (x (D := D) e) (x' (D := D) e) :=
    (DiagCH_x_x'_iff (Provable := Provable) (U := U) (D := D) proc e).2 True.intro
  have heq : x (D := D) e = x' (D := D) e :=
    (hSound (x (D := D) e) (x' (D := D) e)).1 hmix
  exact x_ne_x' (D := D) e heq

theorem procGauge_never_procSound_pointwise (proc : DiagonalRepairProcedureCode) :
    ∀ e, ¬ (∀ z z' : DiagFiber (D := D) e,
        DiagCH (Provable := Provable) (U := U) (D := D) proc e z z' ↔ z = z') := by
  intro e
  exact not_procSound_pointwise (Provable := Provable) (U := U) (D := D) proc e

theorem no_procSound_for_procGauge (proc : DiagonalRepairProcedureCode) :
    ¬ (∀ e, ∀ z z' : DiagFiber (D := D) e,
        DiagCH (Provable := Provable) (U := U) (D := D) proc e z z' ↔ z = z') := by
  intro hAll
  exact (procGauge_never_procSound_pointwise (Provable := Provable) (U := U) (D := D) proc 0) (hAll 0)

/--
`procGauge` is structurally too permissive: its built-in reflexivity makes mixed diagonal pairs
realizable via the pivot `y`, so the pointwise repair soundness specification is impossible.
-/
theorem procGauge_is_structurally_too_weak (proc : DiagonalRepairProcedureCode) :
    ¬ (∀ e, ∀ z z' : DiagFiber (D := D) e,
        DiagCH (Provable := Provable) (U := U) (D := D) proc e z z' ↔ z = z') :=
  no_procSound_for_procGauge (Provable := Provable) (U := U) (D := D) proc

/--
Reduce the diagonal soundness obligation
`∀ z z', DiagCH proc e z z' ↔ z = z'`
to the four explicit cases `(x,x)`, `(x,x')`, `(x',x)`, `(x',x')`.
-/
theorem procSound_on_diag_iff_four (proc : DiagonalRepairProcedureCode) (e : Nat) :
    (∀ z z' : DiagFiber (D := D) e,
        DiagCH (Provable := Provable) (U := U) (D := D) proc e z z' ↔ z = z') ↔
      ((DiagCH (Provable := Provable) (U := U) (D := D) proc e (x (D := D) e) (x (D := D) e) ↔ True) ∧
       (DiagCH (Provable := Provable) (U := U) (D := D) proc e (x (D := D) e) (x' (D := D) e) ↔ False) ∧
       (DiagCH (Provable := Provable) (U := U) (D := D) proc e (x' (D := D) e) (x (D := D) e) ↔ False) ∧
       (DiagCH (Provable := Provable) (U := U) (D := D) proc e (x' (D := D) e) (x' (D := D) e) ↔ True)) := by
  have hForall :=
    (forall2_diag_fiber_iff (Provable := Provable) (U := U) (D := D) (e := e)
      (P := fun z z' : DiagFiber (D := D) e =>
        DiagCH (Provable := Provable) (U := U) (D := D) proc e z z' ↔ z = z'))

  have hEq_xx : (x (D := D) e = x (D := D) e) ↔ True := by
    refine ⟨(fun _ => True.intro), (fun _ => rfl)⟩
  have hEq_xx' : (x (D := D) e = x' (D := D) e) ↔ False := by
    refine ⟨(fun h => x_ne_x' (D := D) e h), (fun h => False.elim h)⟩
  have hEq_x'x : (x' (D := D) e = x (D := D) e) ↔ False := by
    refine ⟨(fun h => x_ne_x' (D := D) e h.symm), (fun h => False.elim h)⟩
  have hEq_x'x' : (x' (D := D) e = x' (D := D) e) ↔ True := by
    refine ⟨(fun _ => True.intro), (fun _ => rfl)⟩

  constructor
  · intro hSound
    rcases (hForall.mp hSound) with ⟨hxx, hxx', hx'x, hx'x'⟩
    refine ⟨Iff.trans hxx hEq_xx, ?_⟩
    refine ⟨Iff.trans hxx' hEq_xx', ?_⟩
    refine ⟨Iff.trans hx'x hEq_x'x, Iff.trans hx'x' hEq_x'x'⟩
  · rintro ⟨hxx, hxx', hx'x, hx'x'⟩
    refine hForall.mpr ?_
    refine ⟨Iff.trans hxx (Iff.symm hEq_xx), ?_⟩
    refine ⟨Iff.trans hxx' (Iff.symm hEq_xx'), ?_⟩
    refine ⟨Iff.trans hx'x (Iff.symm hEq_x'x), Iff.trans hx'x' (Iff.symm hEq_x'x')⟩

/-- The coded procedure-gauge is reflexive by construction. -/
theorem procRefl_of_procGauge (proc : DiagonalRepairProcedureCode) :
    ∀ e, GaugeRefl (P := Nat) obs target_obs (procGauge (U := U) proc e) := by
  intro e h k p y
  dsimp [GaugeRefl, procGauge]
  exact Or.inl rfl

/--
Local bridge: a diagonal-repair “procedure” immediately yields an admissible repair of the diagonal
cell, for any code `e` that decides.
-/
theorem codeRepairsDiagonalCell_of_diagonalRepairProcedure
    (procGauge : Nat → Gauge (P := Nat) obs target_obs)
    (procRefl : ∀ e, GaugeRefl (P := Nat) obs target_obs (procGauge e))
    (procSound :
      ∀ e,
        DecidesProvableByCode (Provable := Provable) (U := U) e →
        ∀ z z' : FiberPt (P := Nat) obs target_obs (g (D := D) e),
          CorrectedHolonomy (P := Nat) (@semantics Provable) obs target_obs (procGauge e)
            (α (D := D) e) z z' ↔ z = z') :
    ∀ e,
      DecidesProvableByCode (Provable := Provable) (U := U) e →
      CodeRepairsDiagonalCell (Provable := Provable) (U := U) (D := D) e := by
  intro e hdec
  exact ⟨procGauge e, procRefl e, procSound e hdec⟩

 /--
 **Procedure-form bridge**: if a “procedure” assigns to each code `e` an admissible gauge and is
 sound in the sense that, assuming `e` decides, that gauge repairs the diagonal cell, then no code
 can decide.

 This is just a thin wrapper around `no_decider_of_decider_to_diagonalRepair` with a local bridge.
 -/
theorem no_decider_of_decider_via_diagonalRepairProcedure
    (procGauge : Nat → Gauge (P := Nat) obs target_obs)
    (procRefl : ∀ e, GaugeRefl (P := Nat) obs target_obs (procGauge e))
    (procSound :
      ∀ e,
        DecidesProvableByCode (Provable := Provable) (U := U) e →
        ∀ z z' : FiberPt (P := Nat) obs target_obs (g (D := D) e),
          CorrectedHolonomy (P := Nat) (@semantics Provable) obs target_obs (procGauge e)
            (α (D := D) e) z z' ↔ z = z') :
    ∀ e, ¬ DecidesProvableByCode (Provable := Provable) (U := U) e := by
  refine
    no_decider_of_decider_to_diagonalRepair (Provable := Provable) (U := U) (D := D)
      (codeRepairsDiagonalCell_of_diagonalRepairProcedure
        (Provable := Provable) (U := U) (D := D) procGauge procRefl procSound)




universe u

/--
A visible-only summary of the diagonal fiber that predicts compatibility
with the diagonal future step.
-/
def VisiblePredictsDiagonalStep (e : Nat) : Prop :=
  ∃ (Q : Type u)
    (σ : FiberPt (P := Nat) obs target_obs (g (D := D) e) → Q)
    (pred : Q → Prop),
      (∃ f : Nat → Q, ∀ z, σ z = f (obs z.1)) ∧
      ∀ z : FiberPt (P := Nat) obs target_obs (g (D := D) e),
        Compatible (P := Nat) (@semantics Provable) obs target_obs
          (PPath.step (g (D := D) e)) z ↔ pred (σ z)

/--
The diagonal lag forbids any predictor that depends only on the visible component.
-/
theorem not_visiblePredictsDiagonalStep (e : Nat) :
    ¬ VisiblePredictsDiagonalStep (Provable := Provable) (U := U) (D := D) e := by
  intro hVis
  rcases hVis with ⟨Q, σ, pred, hσ, hcorr⟩
  rcases
    diag_lag_breaks_visible_summaries
      (Provable := Provable) (U := U) (D := D)
      (e := e) (Q := Q) σ hσ
    with ⟨z, z', hσσ', hCz, hNCz'⟩
  have hp : pred (σ z) := (hcorr z).1 hCz
  have hp' : pred (σ z') := by
    exact Eq.mp (congrArg pred hσσ') hp
  have hCz' :
      Compatible (P := Nat) (@semantics Provable) obs target_obs
        (PPath.step (g (D := D) e)) z' :=
    (hcorr z').2 hp'
  exact hNCz' hCz'

/--
Bridge schema, information form:
if a code-level decider induced a visible predictor for the diagonal step,
then no such decider could exist.
-/
theorem no_decider_of_decider_to_visiblePredictor
    (bridge :
      ∀ e,
        DecidesProvableByCode (Provable := Provable) (U := U) e →
        VisiblePredictsDiagonalStep (Provable := Provable) (U := U) (D := D) e) :
    ∀ e, ¬ DecidesProvableByCode (Provable := Provable) (U := U) e := by
  intro e hdec
  have hVis :
      VisiblePredictsDiagonalStep (Provable := Provable) (U := U) (D := D) e :=
    bridge e hdec
  exact not_visiblePredictsDiagonalStep (Provable := Provable) (U := U) (D := D) e hVis

/--
Unified synthesis theorem:
any bridge from code-level decision to either
(1) a visible predictor of the diagonal step, or
(2) an admissible repair of the diagonal cell,
is impossible.
-/
theorem no_decider_of_decider_to_visiblePredictor_or_diagonalRepair
    (bridge :
      ∀ e,
        DecidesProvableByCode (Provable := Provable) (U := U) e →
        VisiblePredictsDiagonalStep (Provable := Provable) (U := U) (D := D) e
        ∨ CodeRepairsDiagonalCell (Provable := Provable) (U := U) (D := D) e) :
    ∀ e, ¬ DecidesProvableByCode (Provable := Provable) (U := U) e := by
  intro e hdec
  rcases bridge e hdec with hVis | hRepair
  · exact not_visiblePredictsDiagonalStep (Provable := Provable) (U := U) (D := D) e hVis
  · exact not_codeRepairsDiagonalCell (Provable := Provable) (U := U) (D := D) e hRepair
/-- Hence: no code e can decide provability. -/
theorem no_decider_by_code (D : DiagonalCode (Provable := Provable) (U := U)) : ∀ e, ¬ DecidesProvableByCode (Provable := Provable) (U := U) e := by
  intro e hdec
  -- diagonal contradiction at n := diag e
  let n := g (D := D) e
  have hspec := D.diag_spec e
  have hdec' : (U e n = true ↔ Provable n) := hdec n
  have hcontra : (U e n = true ↔ U e n = false) := by
    calc
      (U e n = true) ↔ Provable n := hdec'
      _ ↔ (U e n = false) := hspec
  cases hUn : U e n with
  | true =>
      have hf : U e n = false := (hcontra.mp hUn)
      have : true = false := hUn.symm.trans hf
      exact Bool.noConfusion this
  | false =>
      have ht : U e n = true := (hcontra.mpr hUn)
      have : false = true := hUn.symm.trans ht
      exact Bool.noConfusion this

/-- Paper-friendly qualitative profile for the Gödel-by-code diagonal cell. -/
theorem diag_profile (e : Nat) :
    DynamicNoGoProfile (P := Nat) (@semantics Provable) obs target_obs
      (k' := g (D := D) e)
      (c := diagCell (D := D) e)
      (step := (PPath.step (g (D := D) e) :
        HistoryGraph.Path (P := Nat) (g (D := D) e) (g (D := D) e))) := by
  -- Unfold the profile wrapper (it is just a conjunction for this concrete cell).
  simp [DynamicNoGoProfile, diagCell]
  refine ⟨twistedHolonomy_at_diag (Provable := Provable) (U := U) (D := D) e,
    lagEvent_at_diag (Provable := Provable) (U := U) (D := D) e, ?_,
    diag_not_autoRegulatedWrt_singleton_gaugeRefl (Provable := Provable) (U := U) (D := D) e⟩
  exact
    not_visiblePredictsStep_of_lagEvent
      (P := Nat) (@semantics Provable) obs target_obs
      (h := g (D := D) e) (k := g (D := D) e) (k' := g (D := D) e)
      (p := PPath.p (g (D := D) e)) (q := PPath.q (g (D := D) e))
      (α := α (D := D) e)
      (PPath.step (g (D := D) e))
      (lagEvent_at_diag (Provable := Provable) (U := U) (D := D) e)

/-- The diagonal cell profile plus the quantitative invariant `CompatDimEqTwo` for the diagonal step. -/
theorem diag_profile_dim2 (e : Nat) :
    DynamicNoGoProfile (P := Nat) (@semantics Provable) obs target_obs
      (k' := g (D := D) e)
      (c := diagCell (D := D) e)
      (step := (PPath.step (g (D := D) e) :
        HistoryGraph.Path (P := Nat) (g (D := D) e) (g (D := D) e)))
    ∧ CompatDimEqTwo (P := Nat) (@semantics Provable) obs target_obs
      (h := g (D := D) e) (k := g (D := D) e)
      (PPath.step (g (D := D) e)) := by
  refine ⟨diag_profile (Provable := Provable) (U := U) (D := D) e,
    diag_compatDimEqTwo_step (Provable := Provable) (U := U) (D := D) e⟩

end HolonomicGodelByCode
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
Auto-generated: `#print axioms` for each non-private `theorem`/`lemma` in this file.
-/
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.sem_id
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.sem_comp
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.x_ne_x'
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.diag_fiber_cases
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.forall_diag_fiber_iff
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.DiagFiber
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.forall2_diag_fiber_iff
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.transport_p_x_y
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.transport_p_x'_y
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.transport_q_x_y
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.transport_q_x'_y
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.holonomy_x_x'
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.compatible_step_x_of_provable
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.not_compatible_step_x'_of_provable
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.compatible_step_x'_of_not_provable
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.not_compatible_step_x_of_not_provable
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.lagEvent_at_diag
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.twistedHolonomy_at_diag
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.diag_lag_breaks_visible_summaries
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.diag_not_autoRegulatedWrt_singleton_gaugeRefl
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.diag_obstructionWrt_singleton_gaugeRefl
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.diag_rich_witness
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.diag_diagonalDynamicClass
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.diag_compatible_step_iff_hidden
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.diag_hiddenCompatClassifiedByFin_two_step
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.diag_compatDimLe_two_step
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.diag_compatSigDimLe_two
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.diag_not_compatSigDimLe_zero
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.diag_not_compatSigDimLe_one
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.diag_sigFactorsThrough_two
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.diag_hidden_eq_iff_sameSig
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.diag_compatSigDimEqTwo
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.diag_exists_sigFactorsThrough_two_and_no_smaller
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.diag_compatDimEqTwo_step
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.codeRepairsDiagonalCell_iff_autoRegulatedSingleton
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.not_codeRepairsDiagonalCell
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.no_decider_of_decider_to_diagonalRepair
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.DiagonalRepairProcedureCode
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.NatCodec.pair_eq_pair
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.NatCodec.times2_injective
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.pPathCode
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.encodeGaugeQuery
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.procGauge
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.DiagCH
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.CorrectedHolonomy_on_diag_unfold
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.DiagCH_x_x_iff
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.DiagCH_x_x'_iff
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.DiagCH_x'_x_iff
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.DiagCH_x'_x'_iff
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.not_procSound_pointwise
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.procGauge_never_procSound_pointwise
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.no_procSound_for_procGauge
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.procGauge_is_structurally_too_weak
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.procSound_on_diag_iff_four
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.procRefl_of_procGauge
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.codeRepairsDiagonalCell_of_diagonalRepairProcedure
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.no_decider_of_decider_via_diagonalRepairProcedure
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.not_visiblePredictsDiagonalStep
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.no_decider_of_decider_to_visiblePredictor
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.no_decider_of_decider_to_visiblePredictor_or_diagonalRepair
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.no_decider_by_code
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.diag_profile
#print axioms PrimitiveHolonomy.HolonomicGodelByCode.diag_profile_dim2
/- AXIOM_AUDIT_END -/
