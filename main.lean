import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Relation

/-!
# Primitive Holonomy: The 2-Geometry before Quotient

Formalization of `docs/PRIMITIVE_HOLONOMY.md`.
Strictly constructive (no `noncomputable`, no `classical`).
-/

universe u v w uQ

/--
## 1. The Primitive: 2-Category of Histories (H₂)

We define a minimal 2-structure for histories given by:
- Objects `P`: Prefixes of histories.
- 1-Morphisms `Path`: Totals/Schedulings.
- 2-Morphisms `Deformation`: Admissible commutations/moves.

Note: We do not enforce category laws unless necessary.
-/
class HistoryGraph (P : Type u) where
  Path : P → P → Type v
  Deformation : {h k : P} → Path h k → Path h k → Prop
  idPath (h : P) : Path h h
  compPath {h k l : P} : Path h k → Path k l → Path h l

namespace PrimitiveHolonomy

variable {P : Type u}

/--
## 2. Non-Inversible Semantics: Relational Domain

Target domain: Rel(S).
-/
def Relation (A : Type u) (B : Type v) := A → B → Prop

/-- Pointwise equivalence of relations (axiom-free stand-in for relation equality). -/
def RelEq {A : Type u} {B : Type v} (R S : Relation A B) : Prop :=
  ∀ x y, R x y ↔ S x y

def relComp {A : Type u} {B : Type v} {C : Type w} (R : Relation A B) (S : Relation B C) : Relation A C :=
  fun a c ↦ ∃ b, R a b ∧ S b c

def relId {A : Type u} : Relation A A :=
  fun x y ↦ x = y

def relConverse {A : Type u} {B : Type v} (R : Relation A B) : Relation B A :=
  fun b a ↦ R a b

structure Semantics (P : Type u) [HistoryGraph P] (S : Type w) where
  /-- Transition relation for each scheduling. -/
  sem : {h k : P} → HistoryGraph.Path h k → Relation S S
  sem_id : ∀ h, RelEq (sem (HistoryGraph.idPath h)) relId
  sem_comp : ∀ {h k l} (p : HistoryGraph.Path h k) (q : HistoryGraph.Path k l),
    RelEq (sem (HistoryGraph.compPath p q)) (relComp (sem p) (sem q))



/-- Fiber of ambiguity above `h` (relative to the observable). -/
def Fiber {S V : Type w} (obs : S → V) (target_obs : P → V) (h : P) : Set S :=
  { x | obs x = target_obs h }

/-- The type of points in the fiber above `h`. -/
abbrev FiberPt {S V : Type w} (obs : S → V) (target_obs : P → V) (h : P) : Type w :=
  { x : S // x ∈ Fiber (P := P) obs target_obs h }

/-- Fiber diagonal Δ_{F(h)}. -/
def FiberIdentity {S V : Type w} (obs : S → V) (target_obs : P → V) (h : P) :
    Relation (FiberPt (P := P) obs target_obs h) (FiberPt (P := P) obs target_obs h) :=
  relId

structure LagState (Y B : Type w) where
  visible : Y
  hidden : B

def lagObs {Y B : Type w} : LagState Y B → Y := LagState.visible

theorem hidden_ne_of_ne {Y B : Type w} {target_obs : P → Y} {h : P}
    {x x' : FiberPt (P := P) (obs := (lagObs (Y := Y) (B := B))) target_obs h} (hx : x ≠ x') :
    x.1.hidden ≠ x'.1.hidden :=
by
  intro hhidden
  apply hx
  apply Subtype.ext
  cases x with
  | mk xs hxmem =>
    cases x' with
    | mk xs' hxmem' =>
      cases xs with
      | mk vis hid =>
        cases xs' with
        | mk vis' hid' =>
          have hvis : vis = vis' := hxmem.trans hxmem'.symm
          cases hvis
          cases hhidden
          rfl

section WithHistoryGraph

variable [HistoryGraph P]

/-- Transport restricted to fibers. -/
def Transport {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (p : HistoryGraph.Path h k) :
    Relation (FiberPt (P := P) obs target_obs h) (FiberPt (P := P) obs target_obs k) :=
  fun x y ↦ sem.sem p x.1 y.1

/-- Transport written in the "document style": a relation on the ambient `S`, explicitly restricted to fibers. -/
def TransportDoc {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (p : HistoryGraph.Path h k) : Relation S S :=
  fun x y ↦ sem.sem p x y ∧ obs x = target_obs h ∧ obs y = target_obs k

theorem transport_eq_transportDoc {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (p : HistoryGraph.Path h k)
    (x : FiberPt (P := P) obs target_obs h) (y : FiberPt (P := P) obs target_obs k) :
  Transport sem obs target_obs p x y ↔ TransportDoc sem obs target_obs p x.1 y.1 :=
by
  -- `x.2` and `y.2` are exactly the fiber equalities.
  simpa [Transport, TransportDoc, Fiber, FiberPt] using
    (show sem.sem p x.1 y.1 ↔ sem.sem p x.1 y.1 ∧ obs x.1 = target_obs h ∧ obs y.1 = target_obs k from
      ⟨fun hp ↦ ⟨hp, x.2, y.2⟩, fun hdoc ↦ hdoc.1⟩)

/-- Defines holonomy relative to a 2-cell. -/
def HolonomyRel {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (_α : HistoryGraph.Deformation p q) :
    Relation (FiberPt (P := P) obs target_obs h) (FiberPt (P := P) obs target_obs h) :=
  relComp (Transport sem obs target_obs p) (relConverse (Transport sem obs target_obs q))

theorem holonomy_congr {S : Type w} {V : Type w}
    (sem₁ sem₂ : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (Hp : Transport sem₁ obs target_obs p = Transport sem₂ obs target_obs p)
    (Hq : Transport sem₁ obs target_obs q = Transport sem₂ obs target_obs q) :
    HolonomyRel sem₁ obs target_obs α = HolonomyRel sem₂ obs target_obs α := by
  unfold HolonomyRel
  rw [← Hp, ← Hq]

theorem holonomy_def {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (x x' : FiberPt (P := P) obs target_obs h) :
  HolonomyRel sem obs target_obs α x x' ↔
  ∃ y : FiberPt (P := P) obs target_obs k,
    Transport sem obs target_obs p x y ∧ Transport sem obs target_obs q x' y :=
by rfl

/-!
## 5. "Lag" (Delayed Repercussion)
-/
/-- `x` is compatible with the observed value at `k` along `p` iff `p` can reach the fiber at `k` from `x`. -/
def Compatible {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (p : HistoryGraph.Path h k)
    (x : FiberPt (P := P) obs target_obs h) : Prop :=
  ∃ y : FiberPt (P := P) obs target_obs k, Transport sem obs target_obs p x y

/-- Lag event: two distinct states are related by holonomy now, but only one stays compatible later. -/
def LagEvent {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k') : Prop :=
  ∃ x x' : FiberPt (P := P) obs target_obs h,
    x ≠ x' ∧ HolonomyRel sem obs target_obs α x x' ∧
    Compatible sem obs target_obs step x ∧ ¬ Compatible sem obs target_obs step x'

theorem lag_of_witness {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k')
    (x x' : FiberPt (P := P) obs target_obs h)
    (hx : x ≠ x')
    (hHol : HolonomyRel sem obs target_obs α x x')
    (hstep : Compatible sem obs target_obs step x ∧ ¬ Compatible sem obs target_obs step x') :
    LagEvent sem obs target_obs α step :=
by
  refine ⟨x, x', hx, hHol, hstep.1, hstep.2⟩

/-!
### 5.1 Positive use: compatibility signatures (universal property)

`Compatible` already captures “what stays possible in the future from a micro-state”. The most
direct *positive* invariant for predicting future compatibility is the signature that maps each
future step to its compatibility truth value.

This section packages two facts:

1. `Sig` is a complete invariant for “compatibility prediction” along a chosen family of steps.
2. Any predictor that factors through a 1D summary `σ` forces `σ` to separate any pair that has
   different compatibility along some step (so you can *prove what extra information is required*).
-/

/-- The type of “future steps” starting at a fixed prefix `h` (endpoint varies). -/
def Future (h : P) := Σ k : P, HistoryGraph.Path h k

/-- Compatibility along a dependent future step. -/
def CompatibleFuture {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h : P} (step : Future (P := P) h) (x : FiberPt (P := P) obs target_obs h) : Prop :=
  Compatible sem obs target_obs step.2 x

/-- Full compatibility signature: for each future step, whether `x` remains compatible. -/
def Sig {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h : P} (x : FiberPt (P := P) obs target_obs h) : Future (P := P) h → Prop :=
  fun step => CompatibleFuture (P := P) sem obs target_obs step x

theorem sig_iff_of_summary_correct
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h : P}
    {Q : Type uQ} (σ : FiberPt (P := P) obs target_obs h → Q)
    (pred : Q → Future (P := P) h → Prop)
    (Hcorr : ∀ x step, pred (σ x) step ↔ CompatibleFuture (P := P) sem obs target_obs step x)
    {x x' : FiberPt (P := P) obs target_obs h}
    (hσ : σ x = σ x') :
    ∀ step, Sig (P := P) sem obs target_obs x step ↔ Sig (P := P) sem obs target_obs x' step :=
by
  intro step
  have hx : pred (σ x) step ↔ pred (σ x') step := by simp [hσ]
  exact (Hcorr x step).symm.trans (hx.trans (Hcorr x' step))

theorem summary_separates_compatible_witness
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h : P}
    {Q : Type uQ} (σ : FiberPt (P := P) obs target_obs h → Q)
    (pred : Q → Future (P := P) h → Prop)
    (Hcorr : ∀ x step, pred (σ x) step ↔ CompatibleFuture (P := P) sem obs target_obs step x)
    {x x' : FiberPt (P := P) obs target_obs h}
    (step : Future (P := P) h)
    (hx : CompatibleFuture (P := P) sem obs target_obs step x)
    (hx' : ¬ CompatibleFuture (P := P) sem obs target_obs step x') :
    σ x ≠ σ x' :=
by
  intro hσ
  have hsig :
      ∀ s, Sig (P := P) sem obs target_obs x s ↔ Sig (P := P) sem obs target_obs x' s :=
    sig_iff_of_summary_correct (P := P) sem obs target_obs σ pred Hcorr hσ
  have hEq : CompatibleFuture (P := P) sem obs target_obs step x ↔
      CompatibleFuture (P := P) sem obs target_obs step x' := by
    simpa [Sig, CompatibleFuture] using hsig step
  exact hx' (hEq.mp hx)

theorem lagEvent_gives_summary_witness
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k')
    {Q : Type uQ} (σ : FiberPt (P := P) obs target_obs h → Q)
    (hσ : ∃ f : V → Q, ∀ x, σ x = f (obs x.1))
    (Hlag : LagEvent (P := P) sem obs target_obs α step) :
    ∃ x x' : FiberPt (P := P) obs target_obs h,
      σ x = σ x' ∧ Compatible (P := P) sem obs target_obs step x ∧ ¬ Compatible (P := P) sem obs target_obs step x' :=
by
  rcases Hlag with ⟨x, x', hxne, hHol, hx, hx'⟩
  rcases hσ with ⟨f, hf⟩
  have hobs : obs x.1 = obs x'.1 := by
    -- both lie in the same fiber over `h`
    have hx0 : obs x.1 = target_obs h := x.2
    have hx'0 : obs x'.1 = target_obs h := x'.2
    exact hx0.trans hx'0.symm
  have hσxx' : σ x = σ x' := by
    calc
      σ x = f (obs x.1) := hf x
      _ = f (obs x'.1) := by rw [hobs]
      _ = σ x' := (hf x').symm
  exact ⟨x, x', hσxx', hx, hx'⟩

/--
Step-dependence on the hidden component (product scenario `X = Y×B`, `O(y,b)=y`):
two states in the same fiber with different `hidden` values cannot both remain compatible
with the same observed next step.
-/
def StepDependsOnHidden {Y B : Type w} (sem : Semantics P (LagState Y B))
    (target_obs : P → Y) {h k : P} (step : HistoryGraph.Path h k) : Prop :=
  ∀ x x' : FiberPt (P := P) (obs := (lagObs (Y := Y) (B := B))) target_obs h,
    x.1.hidden ≠ x'.1.hidden →
      ¬ (Compatible sem lagObs target_obs step x ∧ Compatible sem lagObs target_obs step x')

theorem lag_of_twist_and_hidden_step
    {Y B : Type w} (sem : Semantics P (LagState Y B)) (target_obs : P → Y)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k')
    (hDep : StepDependsOnHidden (P := P) sem target_obs step)
    (x x' : FiberPt (P := P) (obs := (lagObs (Y := Y) (B := B))) target_obs h)
    (hx : x ≠ x')
    (hHol : HolonomyRel sem lagObs target_obs α x x')
    (hCompat : Compatible sem lagObs target_obs step x) :
    LagEvent sem lagObs target_obs α step :=
by
  have hHidden : x.1.hidden ≠ x'.1.hidden := hidden_ne_of_ne (P := P) (x := x) (x' := x') hx
  have hNotCompat : ¬ Compatible sem lagObs target_obs step x' := by
    intro hx'
    exact (hDep x x' hHidden) ⟨hCompat, hx'⟩
  exact lag_of_witness (P := P) sem lagObs target_obs α step x x' hx hHol ⟨hCompat, hNotCompat⟩

/--
## 6. Auto-Regulation "Cofinal"

Formalization of the repair condition on a set of 2-cells J.

Audit Reform: Gauge is a "Fiber Preserving Repair".
Ideally it maps Fiber(k) to Fiber(k).
We define a predicate `IsFiberPreserving`.
-/
def Gauge {S V : Type w} (obs : S → V) (target_obs : P → V) :=
  {h k : P} → HistoryGraph.Path h k →
    Relation (FiberPt (P := P) obs target_obs k) (FiberPt (P := P) obs target_obs k)

/-- The empty gauge: it never relates any two fiber points (useful to audit vacuity). -/
def emptyGauge {S V : Type w} (obs : S → V) (target_obs : P → V) : Gauge (P := P) obs target_obs :=
  fun {_h _k} _p => fun _ _ => False

/-- Gauge admissibility: reflexive on each target fiber (contains the diagonal). -/
def GaugeRefl {S V : Type w} (obs : S → V) (target_obs : P → V)
    (φ : Gauge (P := P) obs target_obs) : Prop :=
  ∀ {h k : P} (p : HistoryGraph.Path h k) (y : FiberPt (P := P) obs target_obs k), φ p y y

/-- Gauge admissibility: total/serial on each target fiber (cannot annihilate everything). -/
def GaugeTotal {S V : Type w} (obs : S → V) (target_obs : P → V)
    (φ : Gauge (P := P) obs target_obs) : Prop :=
  ∀ {h k : P} (p : HistoryGraph.Path h k) (y : FiberPt (P := P) obs target_obs k),
    ∃ y' : FiberPt (P := P) obs target_obs k, φ p y y'

/-- Corrected transport along a total p: first do Transport, then apply the gauge at the target. -/
def CorrectedTransport {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (gauge : Gauge (P := P) obs target_obs) (p : HistoryGraph.Path h k) :
    Relation (FiberPt (P := P) obs target_obs h) (FiberPt (P := P) obs target_obs k) :=
  relComp (Transport sem obs target_obs p) (gauge p)

/-- Corrected holonomy: Hol♯(p,q) = T♯_p ∘ (T♯_q)†  -/
def CorrectedHolonomy {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (gauge : Gauge (P := P) obs target_obs) {p q : HistoryGraph.Path h k} (_α : HistoryGraph.Deformation p q) :
    Relation (FiberPt (P := P) obs target_obs h) (FiberPt (P := P) obs target_obs h) :=
  relComp (CorrectedTransport sem obs target_obs gauge p)
          (relConverse (CorrectedTransport sem obs target_obs gauge q))

/-!
### A small but important monotonicity fact

If a gauge contains the diagonal (`GaugeRefl`), then corrected transport/holonomy can only add
possibilities: any existing witness for `Transport`/`HolonomyRel` remains a witness after correction.

This is the key to making `OK` meaningful: once `OK` enforces at least `GaugeRefl`, some obstructions
cannot be “repaired away” by choosing a degenerate gauge like `emptyGauge`.
-/

theorem correctedTransport_of_transport_of_gaugeRefl
    {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (gauge : Gauge (P := P) obs target_obs)
    (hg : GaugeRefl (P := P) obs target_obs gauge)
    (p : HistoryGraph.Path h k)
    (x : FiberPt (P := P) obs target_obs h) (y : FiberPt (P := P) obs target_obs k) :
    Transport (P := P) sem obs target_obs p x y →
      CorrectedTransport (P := P) sem obs target_obs gauge p x y := by
  intro hT
  unfold CorrectedTransport
  exact ⟨y, hT, hg p y⟩

theorem correctedHolonomy_of_holonomy_of_gaugeRefl
    {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (gauge : Gauge (P := P) obs target_obs)
    (hg : GaugeRefl (P := P) obs target_obs gauge)
    {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (x x' : FiberPt (P := P) obs target_obs h) :
    HolonomyRel (P := P) sem obs target_obs α x x' →
      CorrectedHolonomy (P := P) sem obs target_obs gauge α x x' := by
  intro hHol
  -- unfold both sides and reuse the same intermediate witness `y`
  unfold HolonomyRel at hHol
  rcases hHol with ⟨y, hTp, hTq⟩
  unfold CorrectedHolonomy CorrectedTransport
  refine ⟨y, ?_, ?_⟩
  · exact ⟨y, hTp, hg p y⟩
  · exact ⟨y, hTq, hg q y⟩

/-- `emptyGauge` makes every corrected transport false. -/
theorem not_correctedTransport_emptyGauge {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (p : HistoryGraph.Path h k)
    (x : FiberPt (P := P) obs target_obs h) (y : FiberPt (P := P) obs target_obs k) :
    ¬ CorrectedTransport sem obs target_obs (emptyGauge (P := P) obs target_obs) p x y := by
  intro hCT
  unfold CorrectedTransport emptyGauge at hCT
  rcases hCT with ⟨z, _hzT, hzG⟩
  exact hzG

/-- `emptyGauge` makes every corrected holonomy false. -/
theorem not_correctedHolonomy_emptyGauge {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (x x' : FiberPt (P := P) obs target_obs h) :
    ¬ CorrectedHolonomy sem obs target_obs (emptyGauge (P := P) obs target_obs) α x x' := by
  intro hHol
  unfold CorrectedHolonomy at hHol
  rcases hHol with ⟨y, hy, _⟩
  exact (not_correctedTransport_emptyGauge (P := P) sem obs target_obs p x y) hy

/-- A primitive 2-cell: (h,k,p,q) together with α : p ⇒ q. We use PLift to put Prop in Type. -/
abbrev Cell {P : Type u} [HistoryGraph P] :=
  Σ h k : P, Σ p q : HistoryGraph.Path h k, PLift (HistoryGraph.Deformation p q)

/-- Source prefix of a 2-cell. -/
def CellSrc {P : Type u} [HistoryGraph P] : Cell (P := P) → P
| ⟨h, _, _, _, _⟩ => h

/-- Target prefix of a 2-cell. -/
def CellTgt {P : Type u} [HistoryGraph P] : Cell (P := P) → P
| ⟨_, k, _, _, _⟩ => k

/-- “c lives in J” means its endpoints are in `J`. -/
def CellLivesIn {P : Type u} [HistoryGraph P] (J : Set P) (c : Cell (P := P)) : Prop :=
  CellSrc c ∈ J ∧ CellTgt c ∈ J

/-- Set of 2-cells whose endpoints lie in `J`. -/
def CellsOver (C : Set P) : Set (Cell (P := P)) :=
  { c | CellSrc c ∈ C ∧ CellTgt c ∈ C }

/-- Holonomy is weak iff Δ ⊆ Hol. -/
def WeakHolonomy {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q) : Prop :=
  ∀ x : FiberPt (P := P) obs target_obs h, HolonomyRel sem obs target_obs α x x

/-- Holonomy is flat (strong) iff Hol = Δ. -/
def FlatHolonomy {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q) : Prop :=
  ∀ x x' : FiberPt (P := P) obs target_obs h, HolonomyRel sem obs target_obs α x x' ↔ x = x'

/-- Holonomy is twisted iff ∃ x ≠ x' with (x,x') ∈ Hol. -/
def TwistedHolonomy {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q) : Prop :=
  ∃ x x' : FiberPt (P := P) obs target_obs h, x ≠ x' ∧ HolonomyRel sem obs target_obs α x x'

/--
Definition of Auto-Regulation on a set J of deformations.
"There exists a fiber-preserving gauge φ such that for all α ∈ J, the corrected holonomy is the diagonal."
-/
def AutoRegulated {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (J : Set (Cell (P := P))) : Prop :=
  ∃ φ : Gauge (P := P) obs target_obs,
    ∀ c, c ∈ J →
      let ⟨_h, _, _, _, ⟨α⟩⟩ := c
      ∀ x x',
        CorrectedHolonomy sem obs target_obs φ α x x' ↔ x = x'

/-- Auto-regulation relative to a predicate selecting *admissible* gauges. -/
def AutoRegulatedWrt {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop) (J : Set (Cell (P := P))) : Prop :=
  ∃ φ : Gauge (P := P) obs target_obs, OK φ ∧
    ∀ c, c ∈ J →
      let ⟨_h, _, _, _, ⟨α⟩⟩ := c
      ∀ x x',
        CorrectedHolonomy sem obs target_obs φ α x x' ↔ x = x'

/--
## 7. Constructive Verification
-/
theorem is_constructive : True := trivial

/- 1) Préordre interne des préfixes : h ≤ k ssi Reach h k (∃ total). -/
def Reach (h k : P) : Prop :=
  Nonempty (HistoryGraph.Path h k)

theorem reach_refl (h : P) : Reach h h :=
  ⟨HistoryGraph.idPath h⟩

theorem reach_trans {h k l : P} : Reach h k → Reach k l → Reach h l :=
by
  intro hk kl
  rcases hk with ⟨p⟩
  rcases kl with ⟨q⟩
  exact ⟨HistoryGraph.compPath p q⟩

/- 2) Cofinalité (futur ouvert interne) sur (P, Reach). -/
def Cofinal (C : Set P) : Prop :=
  ∀ h : P, ∃ k : P, k ∈ C ∧ Reach h k

/- 3) Dirigé + inférieur-clos : idéal (exécution prolongée comme futur dirigé). -/
def LowerClosed (I : Set P) : Prop :=
  ∀ {h k : P}, Reach h k → k ∈ I → h ∈ I

def Directed (I : Set P) : Prop :=
  ∀ ⦃a b : P⦄, a ∈ I → b ∈ I → ∃ c : P, c ∈ I ∧ Reach a c ∧ Reach b c

structure Ideal (I : Set P) : Prop where
  (lower : LowerClosed I)
  (dir   : Directed I)

/- 4) Temps/ordinal = shadow : un scheduling est une chaîne cofinale. -/
structure Scheduling (A : Type uQ) [Preorder A] where
  c : A → P
  mono : ∀ {i j : A}, i ≤ j → Reach (c i) (c j)
  cofinal : ∀ h : P, ∃ i : A, Reach h (c i)

/-- A scheduling presents a cofinal set of prefixes: its range. -/
theorem cofinal_range_of_scheduling {A : Type uQ} [Preorder A] (s : Scheduling (P := P) A) :
    Cofinal (P := P) (Set.range s.c) := by
  intro h
  rcases s.cofinal h with ⟨i, hi⟩
  refine ⟨s.c i, ⟨i, rfl⟩, hi⟩

/- 5) Auto-régulation cofinale : on restreint les 2-cellules à un futur cofinal. -/

-- Rappel : AutoRegulated est déjà défini chez toi.
-- On ajoute la version “cofinalement” :
def AutoRegulatedCofinal
  {S V : Type w}
  (sem : Semantics P S) (obs : S → V) (target_obs : P → V) : Prop :=
  ∃ C : Set P, Cofinal C ∧ AutoRegulated sem obs target_obs (CellsOver C)

/-- Cofinal auto-regulation relative to a predicate selecting admissible gauges. -/
def AutoRegulatedCofinalWrt
  {S V : Type w}
  (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
  (OK : Gauge (P := P) obs target_obs → Prop) : Prop :=
  ∃ C : Set P, Cofinal C ∧ AutoRegulatedWrt (P := P) sem obs target_obs OK (CellsOver C)

/-- A positive (witnessed) notion of obstruction: every gauge fails by producing a twisted corrected holonomy. -/
def Obstruction {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (J : Set (Cell (P := P))) : Prop :=
  ∀ φ : Gauge (P := P) obs target_obs,
    ∃ c, c ∈ J ∧
      let ⟨h, _, _, _, ⟨α⟩⟩ := c
      ∃ x x' : FiberPt (P := P) obs target_obs h,
        x ≠ x' ∧ CorrectedHolonomy sem obs target_obs φ α x x'

/-- Obstruction relative to a predicate selecting *admissible* gauges. -/
def ObstructionWrt {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop) (J : Set (Cell (P := P))) : Prop :=
  ∀ φ : Gauge (P := P) obs target_obs, OK φ →
    ∃ c, c ∈ J ∧
      let ⟨h, _, _, _, ⟨α⟩⟩ := c
      ∃ x x' : FiberPt (P := P) obs target_obs h,
        x ≠ x' ∧ CorrectedHolonomy sem obs target_obs φ α x x'

/-!
### Decisive structural laws (monotonicity)

These are sharp, witness-preserving consequences of the *positive* definitions:

- `Obstruction` is **upward closed** in the tested cell set `J`.
- `AutoRegulated` is **downward closed** in `J`.
- Same for the `Wrt OK` variants.
-/

theorem obstruction_mono_J {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {J J' : Set (Cell (P := P))} (hJJ' : J ⊆ J') :
    Obstruction (P := P) sem obs target_obs J → Obstruction (P := P) sem obs target_obs J' := by
  intro hObs φ
  rcases hObs φ with ⟨c, hcJ, hw⟩
  exact ⟨c, hJJ' hcJ, hw⟩

theorem obstructionWrt_mono_J {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop)
    {J J' : Set (Cell (P := P))} (hJJ' : J ⊆ J') :
    ObstructionWrt (P := P) sem obs target_obs OK J →
      ObstructionWrt (P := P) sem obs target_obs OK J' := by
  intro hObs φ hOK
  rcases hObs φ hOK with ⟨c, hcJ, hw⟩
  exact ⟨c, hJJ' hcJ, hw⟩

theorem autoRegulated_anti_J {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {J J' : Set (Cell (P := P))} (hJJ' : J ⊆ J') :
    AutoRegulated (P := P) sem obs target_obs J' → AutoRegulated (P := P) sem obs target_obs J := by
  rintro ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  intro c hcJ
  exact hφ c (hJJ' hcJ)

theorem autoRegulatedWrt_anti_J {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop)
    {J J' : Set (Cell (P := P))} (hJJ' : J ⊆ J') :
    AutoRegulatedWrt (P := P) sem obs target_obs OK J' →
      AutoRegulatedWrt (P := P) sem obs target_obs OK J := by
  rintro ⟨φ, hOK, hφ⟩
  refine ⟨φ, hOK, ?_⟩
  intro c hcJ
  exact hφ c (hJJ' hcJ)

theorem autoRegulatedWrt_mono_OK {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {OK OK' : Gauge (P := P) obs target_obs → Prop}
    (hOK : ∀ φ, OK φ → OK' φ)
    (J : Set (Cell (P := P))) :
    AutoRegulatedWrt (P := P) sem obs target_obs OK J →
      AutoRegulatedWrt (P := P) sem obs target_obs OK' J := by
  rintro ⟨φ, hφOK, hφ⟩
  exact ⟨φ, hOK φ hφOK, hφ⟩

theorem obstructionWrt_anti_OK {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {OK OK' : Gauge (P := P) obs target_obs → Prop}
    (hOK : ∀ φ, OK φ → OK' φ)
    (J : Set (Cell (P := P))) :
    ObstructionWrt (P := P) sem obs target_obs OK' J →
      ObstructionWrt (P := P) sem obs target_obs OK J := by
  intro hObs φ hφOK
  exact hObs φ (hOK φ hφOK)

/-- With the current (unrestricted) `Gauge`, `Obstruction` is refutable via `emptyGauge`. -/
theorem not_Obstruction_of_emptyGauge {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (J : Set (Cell (P := P))) :
    ¬ Obstruction (P := P) sem obs target_obs J := by
  intro hObs
  rcases hObs (emptyGauge (P := P) obs target_obs) with ⟨c, _hcJ, hw⟩
  rcases c with ⟨h, k, p, q, ⟨α⟩⟩
  rcases hw with ⟨x, x', _hxne, hxHol⟩
  exact (not_correctedHolonomy_emptyGauge (P := P) sem obs target_obs α x x') hxHol

/-- `ObstructionWrt` implies `¬ AutoRegulatedWrt` (constructive, no quantifier swaps). -/
theorem not_AutoRegulatedWrt_of_ObstructionWrt {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop) (J : Set (Cell (P := P))) :
    ObstructionWrt (P := P) sem obs target_obs OK J →
      ¬ AutoRegulatedWrt (P := P) sem obs target_obs OK J := by
  intro hObs hAuto
  rcases hAuto with ⟨φ, hOK, hφ⟩
  rcases hObs φ hOK with ⟨c, hcJ, hw⟩
  rcases c with ⟨h, k, p, q, ⟨α⟩⟩
  have hDiag : ∀ x x', CorrectedHolonomy sem obs target_obs φ α x x' ↔ x = x' :=
    hφ ⟨h, k, p, q, ⟨α⟩⟩ hcJ
  rcases hw with ⟨x, x', hxne, hxHol⟩
  have : x = x' := (hDiag x x').1 hxHol
  exact hxne this

/-- `AutoRegulatedWrt` implies `¬ ObstructionWrt` (constructive, no quantifier swaps). -/
theorem not_ObstructionWrt_of_AutoRegulatedWrt {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop) (J : Set (Cell (P := P))) :
    AutoRegulatedWrt (P := P) sem obs target_obs OK J →
      ¬ ObstructionWrt (P := P) sem obs target_obs OK J := by
  intro hAuto hObs
  exact (not_AutoRegulatedWrt_of_ObstructionWrt (P := P) sem obs target_obs OK J hObs) hAuto

/-!
### How `OK` restrictions stop vacuity

If `OK` forces gauges to contain the diagonal (`GaugeRefl`), then correction is monotone:
any twisted holonomy witness for `HolonomyRel` remains a twisted witness for `CorrectedHolonomy`.
So the only way a gauge can “repair away” such a witness is by **dropping** reflexivity.
-/

theorem obstructionWrt_singleton_of_twistedHolonomy_of_gaugeRefl
    {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q) :
    TwistedHolonomy (P := P) sem obs target_obs α →
      ObstructionWrt (P := P) sem obs target_obs
        (fun φ => GaugeRefl (P := P) obs target_obs φ)
        (Set.singleton (⟨h, k, p, q, ⟨α⟩⟩ : Cell (P := P))) := by
  intro hTw φ hφ
  refine ⟨⟨h, k, p, q, ⟨α⟩⟩, by simp [Set.singleton], ?_⟩
  change
    ∃ x x' : FiberPt (P := P) obs target_obs h,
      x ≠ x' ∧ CorrectedHolonomy (P := P) sem obs target_obs φ α x x'
  rcases hTw with ⟨x, x', hxne, hHol⟩
  refine ⟨x, x', hxne, ?_⟩
  exact correctedHolonomy_of_holonomy_of_gaugeRefl (P := P) sem obs target_obs φ hφ α x x' hHol

theorem not_autoRegulatedWrt_singleton_of_twistedHolonomy_of_gaugeRefl
    {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q) :
    TwistedHolonomy (P := P) sem obs target_obs α →
      ¬ AutoRegulatedWrt (P := P) sem obs target_obs
        (fun φ => GaugeRefl (P := P) obs target_obs φ)
        (Set.singleton (⟨h, k, p, q, ⟨α⟩⟩ : Cell (P := P))) := by
  intro hTw
  exact
    not_AutoRegulatedWrt_of_ObstructionWrt (P := P) sem obs target_obs
      (OK := fun φ => GaugeRefl (P := P) obs target_obs φ)
      (J := Set.singleton (⟨h, k, p, q, ⟨α⟩⟩ : Cell (P := P)))
      (obstructionWrt_singleton_of_twistedHolonomy_of_gaugeRefl (P := P) sem obs target_obs α hTw)

/-- Cofinal obstruction: there exists a cofinal future where every gauge fails (with a witness). -/
def ObstructionCofinal {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V) : Prop :=
  ∃ C : Set P, Cofinal C ∧ Obstruction sem obs target_obs (CellsOver C)

/-- Cofinal obstruction relative to a predicate selecting admissible gauges. -/
def ObstructionCofinalWrt {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop) : Prop :=
  ∃ C : Set P, Cofinal C ∧ ObstructionWrt (P := P) sem obs target_obs OK (CellsOver C)

/-- Cells whose endpoints lie on the range of a given scheduling `s`. -/
abbrev CellsAlong {A : Type uQ} [Preorder A] (s : Scheduling (P := P) A) : Set (Cell (P := P)) :=
  CellsOver (Set.range s.c)

/-- Auto-regulation restricted to the cofinal future presented by `s`. -/
def AutoRegulatedAlong
    {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {A : Type uQ} [Preorder A] (s : Scheduling (P := P) A) : Prop :=
  AutoRegulated sem obs target_obs (CellsAlong (P := P) s)

/-- Auto-regulation along a specific scheduling, relative to admissible gauges. -/
def AutoRegulatedAlongWrt
    {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop)
    {A : Type uQ} [Preorder A] (s : Scheduling (P := P) A) : Prop :=
  AutoRegulatedWrt (P := P) sem obs target_obs OK (CellsAlong (P := P) s)

/-- Obstruction restricted to the cofinal future presented by `s`. -/
def ObstructionAlong
    {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {A : Type uQ} [Preorder A] (s : Scheduling (P := P) A) : Prop :=
  Obstruction sem obs target_obs (CellsAlong (P := P) s)

/-- Obstruction along a specific scheduling, relative to admissible gauges. -/
def ObstructionAlongWrt
    {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop)
    {A : Type uQ} [Preorder A] (s : Scheduling (P := P) A) : Prop :=
  ObstructionWrt (P := P) sem obs target_obs OK (CellsAlong (P := P) s)

theorem autoRegulatedCofinal_of_autoRegulatedAlong
    {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {A : Type uQ} [Preorder A] (s : Scheduling (P := P) A) :
    AutoRegulatedAlong (P := P) sem obs target_obs s → AutoRegulatedCofinal (P := P) sem obs target_obs := by
  intro hAlong
  refine ⟨Set.range s.c, ?_, ?_⟩
  · exact cofinal_range_of_scheduling (P := P) s
  · simpa [AutoRegulatedAlong, CellsAlong] using hAlong

theorem obstructionCofinal_of_obstructionAlong
    {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {A : Type uQ} [Preorder A] (s : Scheduling (P := P) A) :
    ObstructionAlong (P := P) sem obs target_obs s → ObstructionCofinal (P := P) sem obs target_obs := by
  intro hAlong
  refine ⟨Set.range s.c, ?_, ?_⟩
  · exact cofinal_range_of_scheduling (P := P) s
  · simpa [ObstructionAlong, CellsAlong] using hAlong

theorem autoRegulatedCofinalWrt_of_autoRegulatedAlongWrt
    {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop)
    {A : Type uQ} [Preorder A] (s : Scheduling (P := P) A) :
    AutoRegulatedAlongWrt (P := P) sem obs target_obs OK s →
      AutoRegulatedCofinalWrt (P := P) sem obs target_obs OK := by
  intro hAlong
  refine ⟨Set.range s.c, ?_, ?_⟩
  · exact cofinal_range_of_scheduling (P := P) s
  · simpa [AutoRegulatedAlongWrt, CellsAlong] using hAlong

theorem obstructionCofinalWrt_of_obstructionAlongWrt
    {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop)
    {A : Type uQ} [Preorder A] (s : Scheduling (P := P) A) :
    ObstructionAlongWrt (P := P) sem obs target_obs OK s →
      ObstructionCofinalWrt (P := P) sem obs target_obs OK := by
  intro hAlong
  refine ⟨Set.range s.c, ?_, ?_⟩
  · exact cofinal_range_of_scheduling (P := P) s
  · simpa [ObstructionAlongWrt, CellsAlong] using hAlong

theorem not_AutoRegulated_of_Obstruction {S : Type w} {V : Type w}
    {sem : Semantics P S} {obs : S → V} {target_obs : P → V} {J : Set (Cell (P := P))} :
    Obstruction (P := P) sem obs target_obs J → ¬ AutoRegulated (P := P) sem obs target_obs J :=
by
  intro hObs hAuto
  rcases hAuto with ⟨φ, hφ⟩
  rcases hObs φ with ⟨c, hcJ, hw⟩
  -- unpack the cell and use the diagonal property to contradict the twist witness
  rcases c with ⟨h, k, p, q, ⟨α⟩⟩
  have hDiag : ∀ x x', CorrectedHolonomy sem obs target_obs φ α x x' ↔ x = x' :=
    hφ ⟨h, k, p, q, ⟨α⟩⟩ hcJ
  rcases hw with ⟨x, x', hxne, hxHol⟩
  have : x = x' := (hDiag x x').1 hxHol
  exact hxne this

/-- The converse direction is constructive: a global gauge implies no obstruction witness. -/
theorem not_Obstruction_of_AutoRegulated {S : Type w} {V : Type w}
    {sem : Semantics P S} {obs : S → V} {target_obs : P → V} {J : Set (Cell (P := P))} :
    AutoRegulated (P := P) sem obs target_obs J → ¬ Obstruction (P := P) sem obs target_obs J :=
by
  intro hAuto hObs
  exact (not_AutoRegulated_of_Obstruction (P := P) (sem := sem) (obs := obs) (target_obs := target_obs)
    (J := J) hObs) hAuto

theorem not_AutoRegulatedAlong_of_ObstructionAlong
    {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {A : Type uQ} [Preorder A] (s : Scheduling (P := P) A) :
    ObstructionAlong (P := P) sem obs target_obs s → ¬ AutoRegulatedAlong (P := P) sem obs target_obs s :=
by
  intro hObs hAuto
  have hObs' : Obstruction (P := P) sem obs target_obs (CellsAlong (P := P) s) := by
    simpa [ObstructionAlong] using hObs
  have hAuto' : AutoRegulated (P := P) sem obs target_obs (CellsAlong (P := P) s) := by
    simpa [AutoRegulatedAlong] using hAuto
  exact (not_AutoRegulated_of_Obstruction (P := P) (sem := sem) (obs := obs) (target_obs := target_obs)
    (J := CellsAlong (P := P) s) hObs') hAuto'

theorem not_ObstructionAlong_of_AutoRegulatedAlong
    {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {A : Type uQ} [Preorder A] (s : Scheduling (P := P) A) :
    AutoRegulatedAlong (P := P) sem obs target_obs s → ¬ ObstructionAlong (P := P) sem obs target_obs s :=
by
  intro hAuto hObs
  have hAuto' : AutoRegulated (P := P) sem obs target_obs (CellsAlong (P := P) s) := by
    simpa [AutoRegulatedAlong] using hAuto
  have hObs' : Obstruction (P := P) sem obs target_obs (CellsAlong (P := P) s) := by
    simpa [ObstructionAlong] using hObs
  exact (not_Obstruction_of_AutoRegulated (P := P) (sem := sem) (obs := obs) (target_obs := target_obs)
    (J := CellsAlong (P := P) s) hAuto') hObs'

/-- Local (per-2-cell) repair: each cell has some gauge that makes its corrected holonomy diagonal. -/
def LocallyAutoRegulated {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (J : Set (Cell (P := P))) : Prop :=
  ∀ c, c ∈ J →
    ∃ φ : Gauge (P := P) obs target_obs,
      let ⟨_h, _, _, _, ⟨α⟩⟩ := c
      ∀ x x', CorrectedHolonomy sem obs target_obs φ α x x' ↔ x = x'

theorem locallyAutoRegulated_of_AutoRegulated {S : Type w} {V : Type w}
    {sem : Semantics P S} {obs : S → V} {target_obs : P → V} {J : Set (Cell (P := P))} :
    AutoRegulated (P := P) sem obs target_obs J → LocallyAutoRegulated (P := P) sem obs target_obs J :=
by
  rintro ⟨φ, hφ⟩
  intro c hcJ
  refine ⟨φ, ?_⟩
  -- exactly the same diagonal witness, but per-cell
  exact hφ c hcJ

/-- Local (per-2-cell) repair, relative to admissible gauges selected by `OK`. -/
def LocallyAutoRegulatedWrt {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop)
    (J : Set (Cell (P := P))) : Prop :=
  ∀ c, c ∈ J →
    ∃ φ : Gauge (P := P) obs target_obs, OK φ ∧
      let ⟨_h, _, _, _, ⟨α⟩⟩ := c
      ∀ x x', CorrectedHolonomy sem obs target_obs φ α x x' ↔ x = x'

/-- Global auto-regulation implies local auto-regulation (version `Wrt`). -/
theorem locallyAutoRegulatedWrt_of_autoRegulatedWrt
    {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop)
    (J : Set (Cell (P := P))) :
  AutoRegulatedWrt (P := P) sem obs target_obs OK J →
  LocallyAutoRegulatedWrt (P := P) sem obs target_obs OK J := by
  rintro ⟨φ, hOK, hφ⟩
  intro c hcJ
  refine ⟨φ, hOK, ?_⟩
  exact hφ c hcJ

/-- Corrected holonomy is flat on a single 2-cell `c` under gauge `φ`. -/
def FlatOnCell {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (φ : Gauge (P := P) obs target_obs) (c : Cell (P := P)) : Prop :=
  let ⟨h, _, _, _, ⟨α⟩⟩ := c
  ∀ x x' : FiberPt (P := P) obs target_obs h,
    CorrectedHolonomy sem obs target_obs φ α x x' ↔ x = x'

/-- Twisted witness on a single 2-cell `c` under gauge `φ`. -/
def TwistedOnCell {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (φ : Gauge (P := P) obs target_obs) (c : Cell (P := P)) : Prop :=
  let ⟨h, _, _, _, ⟨α⟩⟩ := c
  ∃ x x' : FiberPt (P := P) obs target_obs h,
    x ≠ x' ∧ CorrectedHolonomy sem obs target_obs φ α x x'

/-- Set of admissible gauges that flatten a fixed cell `c`. -/
def GoodGaugeForCellWrt {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop)
    (c : Cell (P := P)) (φ : Gauge (P := P) obs target_obs) : Prop :=
  OK φ ∧ FlatOnCell (P := P) sem obs target_obs φ c

/-- Global intersection of good gauges over all cells in `J`. -/
def GoodGaugeIntersectionWrt {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop)
    (J : Set (Cell (P := P))) : Prop :=
  ∃ φ : Gauge (P := P) obs target_obs, OK φ ∧
    ∀ c, c ∈ J → FlatOnCell (P := P) sem obs target_obs φ c

theorem locallyAutoRegulatedWrt_iff_goodGaugeForCell_nonempty
    {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop)
    (J : Set (Cell (P := P))) :
    LocallyAutoRegulatedWrt (P := P) sem obs target_obs OK J ↔
      ∀ c, c ∈ J → ∃ φ : Gauge (P := P) obs target_obs,
        GoodGaugeForCellWrt (P := P) sem obs target_obs OK c φ := by
  constructor
  · intro hLocal c hcJ
    rcases hLocal c hcJ with ⟨φ, hOK, hFlat⟩
    refine ⟨φ, hOK, ?_⟩
    simpa [GoodGaugeForCellWrt, FlatOnCell] using hFlat
  · intro hGood c hcJ
    rcases hGood c hcJ with ⟨φ, hOK, hFlat⟩
    refine ⟨φ, hOK, ?_⟩
    simpa [GoodGaugeForCellWrt, FlatOnCell] using hFlat

theorem autoRegulatedWrt_iff_exists_goodGaugeForAllCells
    {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop)
    (J : Set (Cell (P := P))) :
    AutoRegulatedWrt (P := P) sem obs target_obs OK J ↔
      ∃ φ : Gauge (P := P) obs target_obs, OK φ ∧
        ∀ c, c ∈ J → GoodGaugeForCellWrt (P := P) sem obs target_obs OK c φ := by
  constructor
  · intro hAuto
    rcases hAuto with ⟨φ, hOK, hFlatAll⟩
    refine ⟨φ, hOK, ?_⟩
    intro c hcJ
    refine ⟨hOK, ?_⟩
    simpa [GoodGaugeForCellWrt, FlatOnCell] using hFlatAll c hcJ
  · intro h
    rcases h with ⟨φ, hOK, hGood⟩
    refine ⟨φ, hOK, ?_⟩
    intro c hcJ
    have hFlat : FlatOnCell (P := P) sem obs target_obs φ c := (hGood c hcJ).2
    simpa [FlatOnCell] using hFlat

theorem autoRegulatedWrt_iff_goodGaugeIntersection_nonempty
    {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop)
    (J : Set (Cell (P := P))) :
    AutoRegulatedWrt (P := P) sem obs target_obs OK J ↔
      GoodGaugeIntersectionWrt (P := P) sem obs target_obs OK J := by
  constructor
  · intro hAuto
    rcases hAuto with ⟨φ, hOK, hFlatAll⟩
    refine ⟨φ, hOK, ?_⟩
    intro c hcJ
    simpa [FlatOnCell] using hFlatAll c hcJ
  · intro hI
    rcases hI with ⟨φ, hOK, hAll⟩
    refine ⟨φ, hOK, ?_⟩
    intro c hcJ
    simpa [FlatOnCell] using (hAll c hcJ)

theorem obstructionWrt_iff_twistedOnCell
    {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop)
    (J : Set (Cell (P := P))) :
    ObstructionWrt (P := P) sem obs target_obs OK J ↔
      ∀ φ : Gauge (P := P) obs target_obs, OK φ →
        ∃ c, c ∈ J ∧ TwistedOnCell (P := P) sem obs target_obs φ c := by
  constructor
  · intro hObs φ hOK
    rcases hObs φ hOK with ⟨c, hcJ, hw⟩
    refine ⟨c, hcJ, ?_⟩
    simpa [TwistedOnCell] using hw
  · intro hObs φ hOK
    rcases hObs φ hOK with ⟨c, hcJ, hTw⟩
    refine ⟨c, hcJ, ?_⟩
    simpa [TwistedOnCell] using hTw

theorem twistedOnCell_not_goodGaugeForCellWrt
    {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop)
    {φ : Gauge (P := P) obs target_obs} {c : Cell (P := P)} :
    TwistedOnCell (P := P) sem obs target_obs φ c →
      ¬ GoodGaugeForCellWrt (P := P) sem obs target_obs OK c φ := by
  intro hTw hGood
  rcases hGood with ⟨_hOK, hFlat⟩
  rcases c with ⟨h, k, p, q, ⟨α⟩⟩
  dsimp [TwistedOnCell, FlatOnCell] at hTw hFlat
  rcases hTw with ⟨x, x', hxne, hHol⟩
  have : x = x' := (hFlat x x').1 hHol
  exact hxne this

theorem obstructionWrt_implies_exists_cell_not_goodGauge
    {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop)
    (J : Set (Cell (P := P))) :
    ObstructionWrt (P := P) sem obs target_obs OK J →
      ∀ φ : Gauge (P := P) obs target_obs, OK φ →
        ∃ c, c ∈ J ∧ ¬ GoodGaugeForCellWrt (P := P) sem obs target_obs OK c φ := by
  intro hObs φ hOK
  rcases hObs φ hOK with ⟨c, hcJ, hw⟩
  have hTw : TwistedOnCell (P := P) sem obs target_obs φ c := by
    simpa [TwistedOnCell] using hw
  exact ⟨c, hcJ, twistedOnCell_not_goodGaugeForCellWrt (P := P) sem obs target_obs OK hTw⟩

/-- Paradigm statement: locally flat but globally obstructed on the same cofinal future. -/
def LocalFlatButObstructedCofinalWrt {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop) : Prop :=
  ∃ C : Set P, Cofinal (P := P) C ∧
    LocallyAutoRegulatedWrt (P := P) sem obs target_obs OK (CellsOver (P := P) C) ∧
    ObstructionWrt (P := P) sem obs target_obs OK (CellsOver (P := P) C)

/-- On that cofinal future, local flatness together with obstruction forces non-auto-regulation. -/
theorem localAndNotAutoRegulatedWrt_of_localFlatButObstructedCofinalWrt
    {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop) :
  LocalFlatButObstructedCofinalWrt (P := P) sem obs target_obs OK →
  ∃ C : Set P, Cofinal (P := P) C ∧
    LocallyAutoRegulatedWrt (P := P) sem obs target_obs OK (CellsOver (P := P) C) ∧
    ¬ AutoRegulatedWrt (P := P) sem obs target_obs OK (CellsOver (P := P) C) := by
  rintro ⟨C, hCof, hLocal, hObs⟩
  refine ⟨C, hCof, hLocal, ?_⟩
  exact not_AutoRegulatedWrt_of_ObstructionWrt (P := P) sem obs target_obs OK
    (J := CellsOver (P := P) C) hObs

/-- Obstructed cofinal paradigm implies non-auto-regulation on the same cofinal future. -/
theorem not_autoRegulatedWrt_of_localFlatButObstructedCofinalWrt
    {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : Gauge (P := P) obs target_obs → Prop) :
  LocalFlatButObstructedCofinalWrt (P := P) sem obs target_obs OK →
  ∃ C : Set P, Cofinal (P := P) C ∧
    ¬ AutoRegulatedWrt (P := P) sem obs target_obs OK (CellsOver (P := P) C) := by
  rintro ⟨C, hCof, _hLocal, hObs⟩
  refine ⟨C, hCof, ?_⟩
  exact not_AutoRegulatedWrt_of_ObstructionWrt (P := P) sem obs target_obs OK
    (J := CellsOver (P := P) C) hObs

end WithHistoryGraph

end PrimitiveHolonomy



#print axioms PrimitiveHolonomy.holonomy_congr
#print axioms PrimitiveHolonomy.holonomy_def
#print axioms PrimitiveHolonomy.lag_of_witness
#print axioms PrimitiveHolonomy.Compatible
#print axioms PrimitiveHolonomy.hidden_ne_of_ne
#print axioms PrimitiveHolonomy.StepDependsOnHidden
#print axioms PrimitiveHolonomy.lag_of_twist_and_hidden_step
#print axioms PrimitiveHolonomy.Transport
#print axioms PrimitiveHolonomy.LagEvent
#print axioms PrimitiveHolonomy.AutoRegulated
#print axioms PrimitiveHolonomy.Reach
#print axioms PrimitiveHolonomy.Cofinal
#print axioms PrimitiveHolonomy.Scheduling
#print axioms PrimitiveHolonomy.AutoRegulatedCofinal
#print axioms PrimitiveHolonomy.Obstruction
#print axioms PrimitiveHolonomy.ObstructionCofinal
#print axioms PrimitiveHolonomy.not_AutoRegulated_of_Obstruction
#print axioms PrimitiveHolonomy.LocallyAutoRegulated
#print axioms PrimitiveHolonomy.locallyAutoRegulated_of_AutoRegulated

namespace PrimitiveHolonomy

/-- 1D shot: compress each total/scheduling `p : Path h k` into a code in `Q`. -/
abbrev Summary {P : Type u} [HistoryGraph P] (Q : Type uQ) :=
  ∀ {h k : P}, HistoryGraph.Path h k → Q

/-
Refinements for "1D shots":

`Summary` is intentionally permissive: it can encode the path itself, so global
statements like `NonReducibleHolonomy` are only meaningful when we restrict what
counts as "1D".

We provide two constructive restrictions:

* `TimeShot`: a monotone "time coordinate" on objects (prefixes), inducing a summary.
* `shadowSummary` from a `Scheduling`: a set-valued shadow that does not use choice.
-/

/-- A time-like shot: a preorder-valued coordinate on prefixes, monotone along `Reach`. -/
structure TimeShot {P : Type u} [HistoryGraph P] (A : Type uQ) [Preorder A] where
  time : P → A
  mono : ∀ {h k : P}, Reach (P := P) h k → time h ≤ time k

/-- A `TimeShot` induces a `Summary` by forgetting the actual path and keeping the target time. -/
def TimeShot.toSummary {P : Type u} [HistoryGraph P] {A : Type uQ} [Preorder A]
    (t : TimeShot (P := P) A) : Summary (P := P) A :=
  fun {_h k} _p => t.time k

/-- Shadow-future set of indices at a prefix: indices whose stage is reachable from `h`. -/
def shadowFuture {P : Type u} [HistoryGraph P] {A : Type uQ} [Preorder A]
    (s : Scheduling (P := P) A) (h : P) : Set A :=
  { i | Reach (P := P) h (s.c i) }

/-- Constructively, `Scheduling` induces a canonical set-valued summary (no choice needed). -/
def shadowSummary {P : Type u} [HistoryGraph P] {A : Type uQ} [Preorder A]
    (s : Scheduling (P := P) A) : Summary (P := P) (Set A) :=
  fun {_h k} _p => shadowFuture (P := P) s k

/-- Holonomy factors through a 1D summary `q` iff there exists a map `H`
    such that Hol(α) depends only on the two 1D codes of the paths involved in α. -/
def FactorsHolonomy {P : Type u} [HistoryGraph P] {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {Q : Type uQ} (q : Summary (P := P) Q) : Prop :=
  ∃ H : ∀ h : P, Q → Q →
        Relation (FiberPt (P := P) obs target_obs h) (FiberPt (P := P) obs target_obs h),
    ∀ (c : Cell (P := P)),
      let ⟨h, _, p, q', ⟨α⟩⟩ := c
      RelEq (HolonomyRel sem obs target_obs α) (H h (q p) (q q'))

/-- "Factors through time": `FactorsHolonomy` for the summary induced by a `TimeShot`. -/
def FactorsHolonomyTime {P : Type u} [HistoryGraph P] {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {A : Type uQ} [Preorder A] (t : TimeShot (P := P) A) : Prop :=
  FactorsHolonomy (P := P) sem obs target_obs (t.toSummary)

/-- Non-reducible relative to *time-like* shots. -/
def NonReducibleHolonomyTime {P : Type u} [HistoryGraph P] {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V) : Prop :=
  ∀ (A : Type uQ) [Preorder A] (t : TimeShot (P := P) A),
    ¬ FactorsHolonomy (P := P) sem obs target_obs (t.toSummary)

/-- Forward direction: if holonomy factors through a 1D summary,
    then equal codes force equal holonomy. -/
theorem factors_eq_of_codes
  {P : Type u} [HistoryGraph P] {S V : Type w}
  (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
  {Q : Type uQ} (q : Summary (P := P) Q)
  (fact : FactorsHolonomy (P := P) sem obs target_obs q)
  {h k : P}
  {p₁ q₁ : HistoryGraph.Path h k} (α₁ : HistoryGraph.Deformation p₁ q₁)
  {p₂ q₂ : HistoryGraph.Path h k} (α₂ : HistoryGraph.Deformation p₂ q₂)
  (hp : q p₁ = q p₂) (hq : q q₁ = q q₂) :
  RelEq (HolonomyRel (P := P) sem obs target_obs α₁)
        (HolonomyRel (P := P) sem obs target_obs α₂) :=
by
  rcases fact with ⟨H, Hfact⟩
  let c1 : Cell (P := P) := ⟨h, k, p₁, q₁, ⟨α₁⟩⟩
  let c2 : Cell (P := P) := ⟨h, k, p₂, q₂, ⟨α₂⟩⟩
  have e1 : RelEq (HolonomyRel (P := P) sem obs target_obs α₁) (H h (q p₁) (q q₁)) := Hfact c1
  have e2 : RelEq (HolonomyRel (P := P) sem obs target_obs α₂) (H h (q p₂) (q q₂)) := Hfact c2
  intro x x'
  have h1 : HolonomyRel (P := P) sem obs target_obs α₁ x x' ↔ H h (q p₁) (q q₁) x x' := e1 x x'
  have h2 : HolonomyRel (P := P) sem obs target_obs α₂ x x' ↔ H h (q p₂) (q q₂) x x' := e2 x x'
  have hmid : H h (q p₁) (q q₁) x x' ↔ H h (q p₂) (q q₂) x x' := by
    rw [hp, hq]
  exact h1.trans (hmid.trans h2.symm)

/-- Witness-killer: if two 2-cells have the same limit codes but different holonomy,
    then NO factorization through that 1D shot exists. -/
theorem witness_no_factor {P : Type u} [HistoryGraph P] {S V : Type w}
  (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
  {Q : Type uQ} (q : Summary (P := P) Q)
  {h k : P}
  -- Two deformations
  {p₁ q₁ : HistoryGraph.Path h k} (α₁ : HistoryGraph.Deformation p₁ q₁)
  {p₂ q₂ : HistoryGraph.Path h k} (α₂ : HistoryGraph.Deformation p₂ q₂)
  -- Codes match strictly
  (hp : q p₁ = q p₂) (hq : q q₁ = q q₂)
  -- Holonomies differ
  (hne : ¬ RelEq (HolonomyRel sem obs target_obs α₁) (HolonomyRel sem obs target_obs α₂)) :
  ¬ FactorsHolonomy sem obs target_obs q :=
by
  intro fact
  exact hne (factors_eq_of_codes (P := P) sem obs target_obs q fact (α₁ := α₁) (α₂ := α₂) hp hq)

/-- Global non-reduction statement (for holonomy itself): no 1D shot can capture it. -/
def NonReducibleHolonomy {P : Type u} [HistoryGraph P] {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V) : Prop :=
  ∀ (Q : Type uQ) (q : Summary (P := P) Q),
    ¬ FactorsHolonomy sem obs target_obs q

/-!
## 8. Coefficients / Probes: coherent families of holonomies

This section packages the "all holonomies" viewpoint:
- a coefficient system (`CoeffCat`);
- a family of semantics indexed by coefficients (`SemFamily`);
- a notion of naturality for holonomy under coefficient change;
- an indistinguishability relation tested by all coefficients;
- a constructive cofinal-reduction theorem for a covering subfamily.
-/

universe uC uM

/-- Minimal category-like structure for probe/coefficients. -/
structure CoeffCat where
  Obj : Type uC
  Hom : Obj → Obj → Type uM
  id : ∀ c : Obj, Hom c c
  comp : ∀ {a b d : Obj}, Hom a b → Hom b d → Hom a d

/-- A family of semantics indexed by coefficients. -/
structure SemFamily (C : CoeffCat) (P : Type u) [HistoryGraph P] (S : Type w) where
  sem : C.Obj → Semantics P S

/-- Action of coefficient morphisms on fiber relations (at each source prefix). -/
structure FiberRelPush {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (obs : S → V) (target_obs : P → V) where
  push :
    {c d : C.Obj} → C.Hom c d → {h : P} →
      Relation (FiberPt (P := P) obs target_obs h) (FiberPt (P := P) obs target_obs h) →
      Relation (FiberPt (P := P) obs target_obs h) (FiberPt (P := P) obs target_obs h)
  push_id :
    ∀ {c : C.Obj} {h : P}
      (R : Relation (FiberPt (P := P) obs target_obs h) (FiberPt (P := P) obs target_obs h)),
      RelEq (push (C.id c) (h := h) R) R
  push_comp :
    ∀ {a b d : C.Obj} (f : C.Hom a b) (g : C.Hom b d) {h : P}
      (R : Relation (FiberPt (P := P) obs target_obs h) (FiberPt (P := P) obs target_obs h)),
      RelEq (push (C.comp f g) (h := h) R) (push g (h := h) (push f (h := h) R))

/-- Naturality: change coefficient then read holonomy = read holonomy then push. -/
def HolonomyNatural {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S) (obs : S → V) (target_obs : P → V)
    (push : FiberRelPush (P := P) (S := S) (V := V) C obs target_obs) : Prop :=
  ∀ {c d : C.Obj} (f : C.Hom c d) (cell : Cell (P := P)),
    let ⟨h, _, _p, _q, ⟨α⟩⟩ := cell
    RelEq
      (push.push f (h := h) (HolonomyRel (P := P) (fam.sem c) obs target_obs α))
      (HolonomyRel (P := P) (fam.sem d) obs target_obs α)

/-- One-sided (outgoing) indistinguishability seen by all coefficients/cells from `h`. -/
def ProbeIndistinguishableOut {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S)
    (obs : S → V) (target_obs : P → V) (h : P)
    (x y : FiberPt (P := P) obs target_obs h) : Prop :=
  ∀ (c : C.Obj) (k : P) (p q : HistoryGraph.Path h k) (α : HistoryGraph.Deformation p q)
    (z : FiberPt (P := P) obs target_obs h),
      HolonomyRel (P := P) (fam.sem c) obs target_obs α x z ↔
      HolonomyRel (P := P) (fam.sem c) obs target_obs α y z

/-- One-sided indistinguishability restricted to a selected subfamily of coefficients. -/
def ProbeIndistinguishableOutOn {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S) (C0 : Set C.Obj)
    (obs : S → V) (target_obs : P → V) (h : P)
    (x y : FiberPt (P := P) obs target_obs h) : Prop :=
  ∀ (c : C.Obj), c ∈ C0 →
    ∀ (k : P) (p q : HistoryGraph.Path h k) (α : HistoryGraph.Deformation p q)
      (z : FiberPt (P := P) obs target_obs h),
      HolonomyRel (P := P) (fam.sem c) obs target_obs α x z ↔
      HolonomyRel (P := P) (fam.sem c) obs target_obs α y z

/-- Two-sided indistinguishability (outgoing + incoming) over all coefficients/cells. -/
def ProbeIndistinguishable {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S)
    (obs : S → V) (target_obs : P → V) (h : P)
    (x y : FiberPt (P := P) obs target_obs h) : Prop :=
  ProbeIndistinguishableOut (P := P) C fam obs target_obs h x y ∧
  (∀ (c : C.Obj) (k : P) (p q : HistoryGraph.Path h k) (α : HistoryGraph.Deformation p q)
    (z : FiberPt (P := P) obs target_obs h),
      HolonomyRel (P := P) (fam.sem c) obs target_obs α z x ↔
      HolonomyRel (P := P) (fam.sem c) obs target_obs α z y)

/-- Two-sided indistinguishability restricted to a selected subfamily of coefficients. -/
def ProbeIndistinguishableOn {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S) (C0 : Set C.Obj)
    (obs : S → V) (target_obs : P → V) (h : P)
    (x y : FiberPt (P := P) obs target_obs h) : Prop :=
  ProbeIndistinguishableOutOn (P := P) C fam C0 obs target_obs h x y ∧
  (∀ (c : C.Obj), c ∈ C0 →
    ∀ (k : P) (p q : HistoryGraph.Path h k) (α : HistoryGraph.Deformation p q)
      (z : FiberPt (P := P) obs target_obs h),
      HolonomyRel (P := P) (fam.sem c) obs target_obs α z x ↔
      HolonomyRel (P := P) (fam.sem c) obs target_obs α z y)

/-- Setoid induced by all probes. -/
def ProbeSetoid {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S)
    (obs : S → V) (target_obs : P → V) (h : P) :
    Setoid (FiberPt (P := P) obs target_obs h) where
  r := ProbeIndistinguishable (P := P) C fam obs target_obs h
  iseqv := by
    constructor
    · intro x
      constructor
      · intro c k p q α z
        rfl
      · intro c k p q α z
        rfl
    · intro x y hxy
      constructor
      · intro c k p q α z
        exact (hxy.1 c k p q α z).symm
      · intro c k p q α z
        exact (hxy.2 c k p q α z).symm
    · intro x y z hxy hyz
      constructor
      · intro c k p q α t
        exact (hxy.1 c k p q α t).trans (hyz.1 c k p q α t)
      · intro c k p q α t
        exact (hxy.2 c k p q α t).trans (hyz.2 c k p q α t)

/-- Setoid induced by a restricted probe family `C0`. -/
def ProbeSetoidOn {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S) (C0 : Set C.Obj)
    (obs : S → V) (target_obs : P → V) (h : P) :
    Setoid (FiberPt (P := P) obs target_obs h) where
  r := ProbeIndistinguishableOn (P := P) C fam C0 obs target_obs h
  iseqv := by
    constructor
    · intro x
      constructor
      · intro c hc k p q α z
        rfl
      · intro c hc k p q α z
        rfl
    · intro x y hxy
      constructor
      · intro c hc k p q α z
        exact (hxy.1 c hc k p q α z).symm
      · intro c hc k p q α z
        exact (hxy.2 c hc k p q α z).symm
    · intro x y z hxy hyz
      constructor
      · intro c hc k p q α t
        exact (hxy.1 c hc k p q α t).trans (hyz.1 c hc k p q α t)
      · intro c hc k p q α t
        exact (hxy.2 c hc k p q α t).trans (hyz.2 c hc k p q α t)

/-!
## Probe budgets: finitary stability vs. global indistinguishability

This is the quotient-free “LLN core” for probe semantics: how information refines as the
available probe family grows. Everything here is constructive: no `Classical`, no `propext`,
no witness extraction from negations.
-/

section ProbeBudget

variable {P : Type u} [HistoryGraph P] {S V : Type w}
variable (C : CoeffCat) (fam : SemFamily C P S) (obs : S → V) (target_obs : P → V)
variable (h : P)

abbrev ProbeIndist (C0 : Set C.Obj) (x y : FiberPt (P := P) obs target_obs h) : Prop :=
  ProbeIndistinguishableOn (P := P) C fam C0 obs target_obs h x y

theorem probeIndist_anti_mono {C0 C1 : Set C.Obj}
    (hC : C0 ⊆ C1) {x y : FiberPt (P := P) obs target_obs h} :
    ProbeIndist (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h)
        C1 x y →
      ProbeIndist (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h)
        C0 x y := by
  intro h1
  constructor
  · intro c hc0 k p q α z
    exact h1.1 c (hC hc0) k p q α z
  · intro c hc0 k p q α z
    exact h1.2 c (hC hc0) k p q α z

/-- `StableAt C0 x y` means enlarging the probe budget past `C0` never changes whether `x,y`
are indistinguishable. -/
def StableAt (C0 : Set C.Obj) (x y : FiberPt (P := P) obs target_obs h) : Prop :=
  ∀ C1 : Set C.Obj, C0 ⊆ C1 →
    (ProbeIndist (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) C0 x y ↔
     ProbeIndist (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) C1 x y)

theorem not_stableAt_of_indist_and_not_univ {C0 : Set C.Obj}
    {x y : FiberPt (P := P) obs target_obs h}
    (hC0 : ProbeIndist (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) C0 x y)
    (hUniv : ¬ ProbeIndist (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h)
        Set.univ x y) :
    ¬ StableAt (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) C0 x y := by
  intro hStable
  have h' :
      ProbeIndist (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) Set.univ x y :=
    (hStable Set.univ (by intro c _; trivial)).1 hC0
  exact hUniv h'

/-- A *probe obstruction* is: every **finite** probe budget fails to distinguish `x,y`, but the
full family `univ` does distinguish them. -/
def ProbeObstruction : Prop :=
  ∃ x y : FiberPt (P := P) obs target_obs h,
    (∀ C0 : Set C.Obj, Set.Finite C0 →
        ProbeIndist (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) C0 x y) ∧
      ¬ ProbeIndist (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) Set.univ x y

/-- “Finitary compactness”: indistinguishable for all finite budgets ⇒ indistinguishable for `univ`. -/
def FinitaryCompactness : Prop :=
  ∀ x y : FiberPt (P := P) obs target_obs h,
    (∀ C0 : Set C.Obj, Set.Finite C0 →
        ProbeIndist (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) C0 x y) →
      ProbeIndist (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) Set.univ x y

theorem probeObstruction_not_finitaryCompactness :
    ProbeObstruction (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) →
      ¬ FinitaryCompactness (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) := by
  rintro ⟨x, y, hFin, hUniv⟩ hComp
  exact hUniv (hComp x y hFin)

theorem finitaryCompactness_not_probeObstruction :
    FinitaryCompactness (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) →
      ¬ ProbeObstruction (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) := by
  intro hComp hObs
  exact (probeObstruction_not_finitaryCompactness (P := P) (C := C) (fam := fam) (obs := obs)
    (target_obs := target_obs) (h := h) hObs) hComp


theorem probeObstruction_forces_no_finite_stabilization :
    ProbeObstruction (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) →
      ∃ x y : FiberPt (P := P) obs target_obs h,
        (∀ C0 : Set C.Obj, Set.Finite C0 →
            ProbeIndist (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) C0 x y) ∧
          ¬ ProbeIndist (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) Set.univ x y ∧
            (∀ C0 : Set C.Obj, Set.Finite C0 →
              ¬ StableAt (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) C0 x y) := by
  rintro ⟨x, y, hFin, hUniv⟩
  refine ⟨x, y, hFin, hUniv, ?_⟩
  intro C0 hC0
  have hC0xy :
      ProbeIndist (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) C0 x y :=
    hFin C0 hC0
  exact not_stableAt_of_indist_and_not_univ (P := P) (C := C) (fam := fam) (obs := obs)
    (target_obs := target_obs) (h := h) (C0 := C0) hC0xy hUniv

end ProbeBudget

/-!
## Probe quotient (two layers)

We separate two layers:

1. A **quotient-free, setoid-only** characterization: the probe “quotient” is the canonical
   setoid `ProbeSetoid ...` on the fiber, and it is **terminal / greatest** among all
   fiber setoids whose equivalence relation is holonomy-compatible.

2. A **`Quot` realization**: define `FiberQuot := Quot (ProbeSetoid ...)` and state the usual
   universal properties (existence/uniqueness of factorization) plus terminality among
   holonomy-compatible quotients. This layer explicitly depends on the kernel axiom
   `Quot.sound` and is moved to `RevHalt/Theory/PrimitiveHolonomy/QuotRealization.lean`.

Important: `Quot.sound` is **not** a classical axiom (no choice, no excluded middle); it is the
primitive soundness principle for quotient types in Lean.
-/

section ProbeQuotientSetoidOnly

variable {P : Type u} [HistoryGraph P]
variable {S V : Type w}
variable (C : CoeffCat) (fam : SemFamily C P S)
variable (obs : S → V) (target_obs : P → V)
variable {h : P}

/-- A fiber setoid is holonomy-compatible if every holonomy test is invariant under it in both arguments. -/
def HolonomyCompatibleSetoid
    (R : Setoid (FiberPt (P := P) obs target_obs h)) : Prop :=
  ∀ (c : C.Obj) (k : P) (p q : HistoryGraph.Path h k) (α : HistoryGraph.Deformation p q)
      {x x' y y' : FiberPt (P := P) obs target_obs h},
    R.r x x' → R.r y y' →
      (HolonomyRel (P := P) (fam.sem c) obs target_obs α x y ↔
        HolonomyRel (P := P) (fam.sem c) obs target_obs α x' y')

/-- The probe setoid is holonomy-compatible (setoid-only statement). -/
theorem holonomyCompatible_probeSetoid :
    HolonomyCompatibleSetoid (P := P) (C := C) fam obs target_obs (h := h)
      (ProbeSetoid (P := P) C fam obs target_obs h) := by
  intro c k p q α x x' y y' hx hy
  constructor
  · intro hxy
    have hx' : HolonomyRel (P := P) (fam.sem c) obs target_obs α x' y :=
      (hx.1 c k p q α y).mp hxy
    exact (hy.2 c k p q α x').mp hx'
  · intro hx'y'
    have hx'y : HolonomyRel (P := P) (fam.sem c) obs target_obs α x' y :=
      (hy.2 c k p q α x').mpr hx'y'
    exact (hx.1 c k p q α y).mpr hx'y

/-- Maximality of the probe setoid: any holonomy-compatible setoid is contained in `ProbeSetoid`. -/
theorem probeIndistinguishable_of_holonomyCompatibleSetoid
    (R : Setoid (FiberPt (P := P) obs target_obs h))
    (hR : HolonomyCompatibleSetoid (P := P) (C := C) fam obs target_obs (h := h) R)
    {x x' : FiberPt (P := P) obs target_obs h} (hxx' : R.r x x') :
    ProbeIndistinguishable (P := P) C fam obs target_obs h x x' := by
  constructor
  · intro c k p q α z
    have hz : R.r z z := R.iseqv.1 z
    exact hR c k p q α (x := x) (x' := x') (y := z) (y' := z) hxx' hz
  · intro c k p q α z
    have hz : R.r z z := R.iseqv.1 z
    exact hR c k p q α (x := z) (x' := z) (y := x) (y' := x') hz hxx'

/--
Setoid-only terminality: the probe setoid is the greatest holonomy-compatible fiber setoid.

Here “greatest” is with respect to inclusion of equivalence relations:
`R ≤ S` means `R.r x y → S.r x y`.
-/
theorem probeSetoid_terminal_holonomyCompatible
    (R : Setoid (FiberPt (P := P) obs target_obs h))
    (hR : HolonomyCompatibleSetoid (P := P) (C := C) fam obs target_obs (h := h) R) :
    ∀ {x y : FiberPt (P := P) obs target_obs h},
      R.r x y → (ProbeSetoid (P := P) C fam obs target_obs h).r x y := by
  intro x y hxy
  exact
    probeIndistinguishable_of_holonomyCompatibleSetoid
      (P := P) (C := C) fam obs target_obs (h := h) R hR hxy

end ProbeQuotientSetoidOnly

/-!
## Quotient realization (separate file)

This development is **setoid-first**: the probe “quotient” is presented as the canonical
setoid `ProbeSetoid ...` together with its maximality/terminality property among
holonomy-compatible setoids.

If one accepts Lean's primitive quotient type `Quot`, then one can *realize* this setoid as
an actual quotient type and recover the usual “maps of types” universal properties
(`Quot.lift`, terminality among holonomy-compatible quotients, …). That realization
layer depends on the kernel axiom `Quot.sound` and is moved to:

`RevHalt/Theory/PrimitiveHolonomy/QuotRealization.lean`.
-/

/-- Cofinality in coefficients: every coefficient maps to some coefficient in `C0`. -/
def CoeffCofinal (C : CoeffCat) (C0 : Set C.Obj) : Prop :=
  ∀ c : C.Obj, ∃ c0 : C.Obj, c0 ∈ C0 ∧ Nonempty (C.Hom c c0)

/--
Conservativity on holonomy tests along coefficient morphisms:
pushing a holonomy relation does not lose information (pointwise).
-/
def PushConservativeOnHolonomy {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S) (obs : S → V) (target_obs : P → V)
    (push : FiberRelPush (P := P) (S := S) (V := V) C obs target_obs) : Prop :=
  ∀ {c d : C.Obj} (f : C.Hom c d) (cell : Cell (P := P)),
    let ⟨h, _, _p, _q, ⟨α⟩⟩ := cell
    RelEq
      (push.push f (h := h) (HolonomyRel (P := P) (fam.sem c) obs target_obs α))
      (HolonomyRel (P := P) (fam.sem c) obs target_obs α)

/--
`C0` covers all coefficients if each coefficient has a representative in `C0`
with exactly the same holonomy tests (pointwise on fibers).
-/
def CoeffCovers {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S) (C0 : Set C.Obj)
    (obs : S → V) (target_obs : P → V) : Prop :=
  ∀ c : C.Obj, ∃ c0 : C.Obj, c0 ∈ C0 ∧
    ∀ (h k : P) (p q : HistoryGraph.Path h k) (α : HistoryGraph.Deformation p q)
      (x z : FiberPt (P := P) obs target_obs h),
      HolonomyRel (P := P) (fam.sem c) obs target_obs α x z ↔
      HolonomyRel (P := P) (fam.sem c0) obs target_obs α x z

/--
Structural derivation of `CoeffCovers` from:
1) coefficient cofinality (via morphisms),
2) holonomy naturality under coefficient change,
3) conservativity of push on holonomy tests.
-/
theorem coeffCovers_of_coeffCofinal_of_holonomyNatural_of_pushConservativeOnHolonomy
    {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S) (C0 : Set C.Obj)
    (obs : S → V) (target_obs : P → V)
    (push : FiberRelPush (P := P) (S := S) (V := V) C obs target_obs)
    (hCof : CoeffCofinal C C0)
    (hNat : HolonomyNatural (P := P) C fam obs target_obs push)
    (hCons : PushConservativeOnHolonomy (P := P) C fam obs target_obs push) :
    CoeffCovers (P := P) C fam C0 obs target_obs := by
  intro c
  rcases hCof c with ⟨c0, hc0, ⟨f⟩⟩
  refine ⟨c0, hc0, ?_⟩
  intro h k p q α x z
  have hNatCell :
      RelEq
        (push.push f (h := h) (HolonomyRel (P := P) (fam.sem c) obs target_obs α))
        (HolonomyRel (P := P) (fam.sem c0) obs target_obs α) := by
    simpa using hNat (c := c) (d := c0) f ⟨h, k, p, q, ⟨α⟩⟩
  have hConsCell :
      RelEq
        (push.push f (h := h) (HolonomyRel (P := P) (fam.sem c) obs target_obs α))
        (HolonomyRel (P := P) (fam.sem c) obs target_obs α) := by
    simpa using hCons (c := c) (d := c0) f ⟨h, k, p, q, ⟨α⟩⟩
  have hEq :
      RelEq
        (HolonomyRel (P := P) (fam.sem c) obs target_obs α)
        (HolonomyRel (P := P) (fam.sem c0) obs target_obs α) := by
    intro a b
    exact (hConsCell a b).symm.trans (hNatCell a b)
  exact hEq x z

theorem probeIndistinguishableOn_of_probeIndistinguishable
    {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S) (C0 : Set C.Obj)
    (obs : S → V) (target_obs : P → V) (h : P)
    {x y : FiberPt (P := P) obs target_obs h} :
    ProbeIndistinguishable (P := P) C fam obs target_obs h x y →
      ProbeIndistinguishableOn (P := P) C fam C0 obs target_obs h x y := by
  intro hAll
  constructor
  · intro c hc0 k p q α z
    exact hAll.1 c k p q α z
  · intro c hc0 k p q α z
    exact hAll.2 c k p q α z

theorem probeIndistinguishable_of_probeIndistinguishableOn_of_coeffCovers
    {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S) (C0 : Set C.Obj)
    (obs : S → V) (target_obs : P → V) (h : P)
    (hCover : CoeffCovers (P := P) C fam C0 obs target_obs)
    {x y : FiberPt (P := P) obs target_obs h} :
    ProbeIndistinguishableOn (P := P) C fam C0 obs target_obs h x y →
      ProbeIndistinguishable (P := P) C fam obs target_obs h x y := by
  intro hOn
  constructor
  · intro c k p q α z
    rcases hCover c with ⟨c0, hc0, hEq⟩
    have hx : HolonomyRel (P := P) (fam.sem c) obs target_obs α x z ↔
        HolonomyRel (P := P) (fam.sem c0) obs target_obs α x z := hEq h k p q α x z
    have hy : HolonomyRel (P := P) (fam.sem c) obs target_obs α y z ↔
        HolonomyRel (P := P) (fam.sem c0) obs target_obs α y z := hEq h k p q α y z
    exact hx.trans ((hOn.1 c0 hc0 k p q α z).trans hy.symm)
  · intro c k p q α z
    rcases hCover c with ⟨c0, hc0, hEq⟩
    have hx : HolonomyRel (P := P) (fam.sem c) obs target_obs α z x ↔
        HolonomyRel (P := P) (fam.sem c0) obs target_obs α z x := hEq h k p q α z x
    have hy : HolonomyRel (P := P) (fam.sem c) obs target_obs α z y ↔
        HolonomyRel (P := P) (fam.sem c0) obs target_obs α z y := hEq h k p q α z y
    exact hx.trans ((hOn.2 c0 hc0 k p q α z).trans hy.symm)

/-- Cofinal-reduction principle for two-sided probe indistinguishability. -/
theorem probeIndistinguishable_iff_probeIndistinguishableOn_of_coeffCovers
    {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S) (C0 : Set C.Obj)
    (obs : S → V) (target_obs : P → V) (h : P)
    (hCover : CoeffCovers (P := P) C fam C0 obs target_obs)
    (x y : FiberPt (P := P) obs target_obs h) :
    ProbeIndistinguishable (P := P) C fam obs target_obs h x y ↔
      ProbeIndistinguishableOn (P := P) C fam C0 obs target_obs h x y := by
  constructor
  · exact probeIndistinguishableOn_of_probeIndistinguishable (P := P) C fam C0 obs target_obs h
  · exact probeIndistinguishable_of_probeIndistinguishableOn_of_coeffCovers
      (P := P) C fam C0 obs target_obs h hCover

end PrimitiveHolonomy

#print axioms PrimitiveHolonomy.factors_eq_of_codes
#print axioms PrimitiveHolonomy.witness_no_factor
#print axioms PrimitiveHolonomy.NonReducibleHolonomy

namespace PrimitiveHolonomy

section ConcreteMathInstance

/-!
Concrete non-physical instance for the coefficient/probe layer:
- one-prefix history graph;
- boolean micro-states with constant observable;
- two coefficient objects with unique morphisms;
- identity push on probe relations.

This section instantiates and validates the full structural chain:
`CoeffCofinal + HolonomyNatural + PushConservativeOnHolonomy
  => CoeffCovers => probe reduction`.
-/

inductive MathPrefix where
  | base
  deriving DecidableEq

instance : HistoryGraph MathPrefix where
  Path _ _ := Unit
  Deformation {_ _} _ _ := True
  idPath _ := ()
  compPath _ _ := ()

def mathObs : Bool → Unit := fun _ => ()

def mathTargetObs : MathPrefix → Unit := fun _ => ()

def mathSemantics : Semantics MathPrefix Bool where
  sem := by
    intro _h _k _p
    exact relId
  sem_id := by
    intro h x y
    rfl
  sem_comp := by
    intro h k l p q x y
    constructor
    · intro hxy
      refine ⟨x, ?_, ?_⟩
      · rfl
      · exact hxy
    · rintro ⟨b, hb1, hb2⟩
      exact hb1.trans hb2

inductive MathCoeffObj where
  | c0
  | c1
  deriving DecidableEq

def MathCoeffCat : CoeffCat where
  Obj := MathCoeffObj
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()

def mathSemFamily : SemFamily MathCoeffCat MathPrefix Bool where
  sem _ := mathSemantics

def mathPush :
    FiberRelPush (P := MathPrefix) (S := Bool) (V := Unit)
      MathCoeffCat mathObs mathTargetObs where
  push := by
    intro _c _d _f _h R
    exact R
  push_id := by
    intro c h R x y
    rfl
  push_comp := by
    intro a b d f g h R x y
    rfl

/-- Chosen covering subfamily: one coefficient object only. -/
def mathC0 : Set MathCoeffObj := {MathCoeffObj.c0}

/-- The chosen subfamily is proper (`c1` is excluded). -/
theorem mathC0_proper : MathCoeffObj.c1 ∉ mathC0 := by
  intro hmem
  have hEq : MathCoeffObj.c1 = MathCoeffObj.c0 := by
    -- `mathC0` is a singleton set.
    dsimp [mathC0] at hmem
    exact hmem
  have hne : MathCoeffObj.c1 ≠ MathCoeffObj.c0 := by
    decide
  exact hne hEq

theorem mathCoeffCofinal : CoeffCofinal MathCoeffCat mathC0 := by
  intro c
  refine ⟨MathCoeffObj.c0, ?_, ⟨()⟩⟩
  -- Membership in the singleton set is definitional.
  dsimp [mathC0]
  rfl

theorem mathHolonomyNatural :
    HolonomyNatural (P := MathPrefix)
      MathCoeffCat mathSemFamily mathObs mathTargetObs mathPush := by
  intro c d f cell
  rcases cell with ⟨h, k, p, q, ⟨α⟩⟩
  intro x y
  rfl

theorem mathPushConservative :
    PushConservativeOnHolonomy (P := MathPrefix)
      MathCoeffCat mathSemFamily mathObs mathTargetObs mathPush := by
  intro c d f cell
  rcases cell with ⟨h, k, p, q, ⟨α⟩⟩
  intro x y
  rfl

theorem mathCoeffCovers :
    CoeffCovers (P := MathPrefix)
      MathCoeffCat mathSemFamily mathC0 mathObs mathTargetObs := by
  exact
    coeffCovers_of_coeffCofinal_of_holonomyNatural_of_pushConservativeOnHolonomy
      (P := MathPrefix)
      MathCoeffCat mathSemFamily mathC0 mathObs mathTargetObs mathPush
      mathCoeffCofinal mathHolonomyNatural mathPushConservative

theorem mathProbeReduction
    (x y : FiberPt (P := MathPrefix) mathObs mathTargetObs MathPrefix.base) :
    ProbeIndistinguishable
      (P := MathPrefix) MathCoeffCat mathSemFamily mathObs mathTargetObs MathPrefix.base x y
      ↔
    ProbeIndistinguishableOn
      (P := MathPrefix) MathCoeffCat mathSemFamily mathC0
      mathObs mathTargetObs MathPrefix.base x y := by
  exact
    probeIndistinguishable_iff_probeIndistinguishableOn_of_coeffCovers
      (P := MathPrefix)
      MathCoeffCat mathSemFamily mathC0 mathObs mathTargetObs MathPrefix.base
      mathCoeffCovers x y

end ConcreteMathInstance

section QuotientOperational

variable {P : Type u} [HistoryGraph P]
variable {S V : Type w}
variable (C : CoeffCat) (fam : SemFamily C P S)
variable (obs : S → V) (target_obs : P → V)

/-- Holonomy tests are compatible with the full probe setoid in both arguments. -/
theorem holonomyRel_respects_probeSetoid
    {h k : P} (c : C.Obj) {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    {x x' y y' : FiberPt (P := P) obs target_obs h}
    (hx : ProbeIndistinguishable (P := P) C fam obs target_obs h x x')
    (hy : ProbeIndistinguishable (P := P) C fam obs target_obs h y y') :
    HolonomyRel (P := P) (fam.sem c) obs target_obs α x y ↔
      HolonomyRel (P := P) (fam.sem c) obs target_obs α x' y' := by
  constructor
  · intro hxy
    have hx' : HolonomyRel (P := P) (fam.sem c) obs target_obs α x' y :=
      (hx.1 c k p q α y).mp hxy
    exact (hy.2 c k p q α x').mp hx'
  · intro hx'y'
    have hx'y : HolonomyRel (P := P) (fam.sem c) obs target_obs α x' y :=
      (hy.2 c k p q α x').mpr hx'y'
    exact (hx.1 c k p q α y).mpr hx'y

/-- Holonomy tests are compatible with the restricted probe setoid in both arguments. -/
theorem holonomyRel_respects_probeSetoidOn
    {C0 : Set C.Obj} {h k : P} (c : C.Obj) (hc : c ∈ C0)
    {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    {x x' y y' : FiberPt (P := P) obs target_obs h}
    (hx : ProbeIndistinguishableOn (P := P) C fam C0 obs target_obs h x x')
    (hy : ProbeIndistinguishableOn (P := P) C fam C0 obs target_obs h y y') :
    HolonomyRel (P := P) (fam.sem c) obs target_obs α x y ↔
      HolonomyRel (P := P) (fam.sem c) obs target_obs α x' y' := by
  constructor
  · intro hxy
    have hx' : HolonomyRel (P := P) (fam.sem c) obs target_obs α x' y :=
      (hx.1 c hc k p q α y).mp hxy
    exact (hy.2 c hc k p q α x').mp hx'
  · intro hx'y'
    have hx'y : HolonomyRel (P := P) (fam.sem c) obs target_obs α x' y :=
      (hy.2 c hc k p q α x').mpr hx'y'
    exact (hx.1 c hc k p q α y).mpr hx'y

end QuotientOperational

section NontrivialCombinatorialInstance

/-!
Concrete nontrivial mathematical instance:
- one-prefix history graph with five nontrivial path codes;
- relational semantics on `Bool`;
- explicit twisted holonomy witness;
- explicit lag witness.
-/

inductive ComboPrefix where
  | base
  deriving DecidableEq

inductive ComboPath where
  | id
  | all
  | step
  | fromFalse
  | toFalse
  deriving DecidableEq

def comboComp : ComboPath → ComboPath → ComboPath
  | ComboPath.id, r => r
  | r, ComboPath.id => r
  | ComboPath.all, ComboPath.all => ComboPath.all
  | ComboPath.all, ComboPath.step => ComboPath.toFalse
  | ComboPath.all, ComboPath.fromFalse => ComboPath.all
  | ComboPath.all, ComboPath.toFalse => ComboPath.toFalse
  | ComboPath.step, ComboPath.all => ComboPath.fromFalse
  | ComboPath.step, ComboPath.step => ComboPath.step
  | ComboPath.step, ComboPath.fromFalse => ComboPath.fromFalse
  | ComboPath.step, ComboPath.toFalse => ComboPath.step
  | ComboPath.fromFalse, ComboPath.all => ComboPath.fromFalse
  | ComboPath.fromFalse, ComboPath.step => ComboPath.step
  | ComboPath.fromFalse, ComboPath.fromFalse => ComboPath.fromFalse
  | ComboPath.fromFalse, ComboPath.toFalse => ComboPath.step
  | ComboPath.toFalse, ComboPath.all => ComboPath.all
  | ComboPath.toFalse, ComboPath.step => ComboPath.toFalse
  | ComboPath.toFalse, ComboPath.fromFalse => ComboPath.all
  | ComboPath.toFalse, ComboPath.toFalse => ComboPath.toFalse

instance : HistoryGraph ComboPrefix where
  Path _ _ := ComboPath
  Deformation {_ _} _ _ := True
  idPath _ := ComboPath.id
  compPath := comboComp

def comboObs : Bool → Unit := fun _ => ()

def comboTargetObs : ComboPrefix → Unit := fun _ => ()

def comboRel : ComboPath → Relation Bool Bool
  | ComboPath.id => relId
  | ComboPath.all => fun _ _ => True
  | ComboPath.step => fun a b => a = false ∧ b = false
  | ComboPath.fromFalse => fun a _ => a = false
  | ComboPath.toFalse => fun _ b => b = false

instance instDecidableComboRel (p : ComboPath) (a b : Bool) : Decidable (comboRel p a b) := by
  cases p
  · simpa [comboRel, relId] using (inferInstance : Decidable (a = b))
  · simpa [comboRel] using (inferInstance : Decidable True)
  · simpa [comboRel] using (inferInstance : Decidable (a = false ∧ b = false))
  · simpa [comboRel] using (inferInstance : Decidable (a = false))
  · simpa [comboRel] using (inferInstance : Decidable (b = false))

instance instDecidableRelCompCombo (p q : ComboPath) (x y : Bool) :
    Decidable (relComp (comboRel p) (comboRel q) x y) := by
  unfold relComp
  infer_instance

theorem combo_sem_comp_bool (p q : ComboPath) (x y : Bool) :
    comboRel (comboComp p q) x y ↔ relComp (comboRel p) (comboRel q) x y := by
  cases p <;> cases q <;> cases x <;> cases y <;> decide

def comboSemantics : Semantics ComboPrefix Bool where
  sem := by
    intro _h _k p
    exact comboRel p
  sem_id := by
    intro h x y
    rfl
  sem_comp := by
    intro h k l p q x y
    simpa using combo_sem_comp_bool p q x y

def comboX0 : FiberPt (P := ComboPrefix) comboObs comboTargetObs ComboPrefix.base := ⟨false, rfl⟩

def comboX1 : FiberPt (P := ComboPrefix) comboObs comboTargetObs ComboPrefix.base := ⟨true, rfl⟩

theorem comboX0_ne_comboX1 : comboX0 ≠ comboX1 := by
  intro h
  exact Bool.false_ne_true (congrArg Subtype.val h)

theorem combo_holonomy_all_id
    (x y : FiberPt (P := ComboPrefix) comboObs comboTargetObs ComboPrefix.base) :
    HolonomyRel (P := ComboPrefix) comboSemantics comboObs comboTargetObs
      (h := ComboPrefix.base) (k := ComboPrefix.base)
      (p := ComboPath.all) (q := ComboPath.id) (by trivial) x y := by
  unfold HolonomyRel relComp relConverse Transport
  refine ⟨y, ?_, ?_⟩
  · simp [comboSemantics, comboRel]
  · rfl

theorem combo_holonomy_all_id_iff_true
    (x y : FiberPt (P := ComboPrefix) comboObs comboTargetObs ComboPrefix.base) :
    HolonomyRel (P := ComboPrefix) comboSemantics comboObs comboTargetObs
      (h := ComboPrefix.base) (k := ComboPrefix.base)
      (p := ComboPath.all) (q := ComboPath.id) (by trivial) x y ↔ True := by
  constructor
  · intro _h
    trivial
  · intro _h
    exact combo_holonomy_all_id x y

theorem combo_holonomy_id_id_iff_eq
    (x y : FiberPt (P := ComboPrefix) comboObs comboTargetObs ComboPrefix.base) :
    HolonomyRel (P := ComboPrefix) comboSemantics comboObs comboTargetObs
      (h := ComboPrefix.base) (k := ComboPrefix.base)
      (p := ComboPath.id) (q := ComboPath.id) (by trivial) x y ↔ x = y := by
  constructor
  · intro hHol
    unfold HolonomyRel relComp relConverse Transport at hHol
    rcases hHol with ⟨z, hx, hy⟩
    cases x with
    | mk xv hxmem =>
      cases y with
      | mk yv hymem =>
        cases z with
        | mk zv hzmem =>
          change Subtype.mk xv hxmem = Subtype.mk yv hymem
          change comboRel ComboPath.id xv zv at hx
          change comboRel ComboPath.id yv zv at hy
          change xv = zv at hx
          change yv = zv at hy
          have hv : xv = yv := hx.trans hy.symm
          cases hv
          cases hxmem
          cases hymem
          rfl
  · intro hxy
    subst hxy
    unfold HolonomyRel relComp relConverse Transport
    refine ⟨x, ?_, ?_⟩
    · change comboRel ComboPath.id x.1 x.1
      change x.1 = x.1
      rfl
    · change comboRel ComboPath.id x.1 x.1
      change x.1 = x.1
      rfl

theorem combo_twistedHolonomy :
    TwistedHolonomy (P := ComboPrefix) comboSemantics comboObs comboTargetObs
      (h := ComboPrefix.base) (k := ComboPrefix.base)
      (p := ComboPath.all) (q := ComboPath.id)
      (show HistoryGraph.Deformation (P := ComboPrefix) ComboPath.all ComboPath.id from trivial) := by
  refine ⟨comboX0, comboX1, comboX0_ne_comboX1, ?_⟩
  exact combo_holonomy_all_id comboX0 comboX1

theorem combo_compatible_step_x0 :
    Compatible (P := ComboPrefix) comboSemantics comboObs comboTargetObs
      (h := ComboPrefix.base) (k := ComboPrefix.base) ComboPath.step comboX0 := by
  refine ⟨comboX0, ?_⟩
  change comboRel ComboPath.step comboX0.1 comboX0.1
  change comboX0.1 = false ∧ comboX0.1 = false
  exact ⟨rfl, rfl⟩

theorem combo_not_compatible_step_x1 :
    ¬ Compatible (P := ComboPrefix) comboSemantics comboObs comboTargetObs
      (h := ComboPrefix.base) (k := ComboPrefix.base) ComboPath.step comboX1 := by
  intro hC
  rcases hC with ⟨y, hy⟩
  change comboRel ComboPath.step comboX1.1 y.1 at hy
  change comboX1.1 = false ∧ y.1 = false at hy
  cases hy.1

theorem combo_lagEvent :
    LagEvent (P := ComboPrefix) comboSemantics comboObs comboTargetObs
      (h := ComboPrefix.base) (k := ComboPrefix.base) (k' := ComboPrefix.base)
      (p := ComboPath.all) (q := ComboPath.id)
      (show HistoryGraph.Deformation (P := ComboPrefix) ComboPath.all ComboPath.id from trivial)
      ComboPath.step := by
  refine lag_of_witness (P := ComboPrefix) comboSemantics comboObs comboTargetObs
    (h := ComboPrefix.base) (k := ComboPrefix.base) (k' := ComboPrefix.base)
    (p := ComboPath.all) (q := ComboPath.id)
    (α := (show HistoryGraph.Deformation (P := ComboPrefix) ComboPath.all ComboPath.id from trivial))
    (step := ComboPath.step)
    comboX0 comboX1 comboX0_ne_comboX1 ?_ ?_
  · exact combo_holonomy_all_id comboX0 comboX1
  · exact ⟨combo_compatible_step_x0, combo_not_compatible_step_x1⟩

/-- For `(id,id)`, `comboX0` and `comboX1` are not holonomy-related. -/
theorem combo_not_holonomy_id_id_x0_x1 :
    ¬ HolonomyRel (P := ComboPrefix) comboSemantics comboObs comboTargetObs
      (h := ComboPrefix.base) (k := ComboPrefix.base)
      (p := ComboPath.id) (q := ComboPath.id)
      (show HistoryGraph.Deformation (P := ComboPrefix) ComboPath.id ComboPath.id from trivial)
      comboX0 comboX1 := by
  intro hHol
  rcases hHol with ⟨y, hy0, hy1⟩
  have hy0' : comboX0.1 = y.1 := by
    simpa [Transport, comboSemantics, comboRel, relId] using hy0
  have hy1' : comboX1.1 = y.1 := by
    simpa [Transport, comboSemantics, comboRel, relId] using hy1
  have h01 : comboX0.1 = comboX1.1 := hy0'.trans hy1'.symm
  exact Bool.false_ne_true h01

/-- The two holonomies `(all,id)` and `(id,id)` are extensionally different. -/
theorem combo_holonomy_all_id_ne_holonomy_id_id :
    ¬ RelEq
      (HolonomyRel (P := ComboPrefix) comboSemantics comboObs comboTargetObs
        (h := ComboPrefix.base) (k := ComboPrefix.base)
        (p := ComboPath.all) (q := ComboPath.id)
        (show HistoryGraph.Deformation (P := ComboPrefix) ComboPath.all ComboPath.id from trivial))
      (HolonomyRel (P := ComboPrefix) comboSemantics comboObs comboTargetObs
        (h := ComboPrefix.base) (k := ComboPrefix.base)
        (p := ComboPath.id) (q := ComboPath.id)
        (show HistoryGraph.Deformation (P := ComboPrefix) ComboPath.id ComboPath.id from trivial)) := by
  intro hEq
  have hAll :
      HolonomyRel (P := ComboPrefix) comboSemantics comboObs comboTargetObs
        (h := ComboPrefix.base) (k := ComboPrefix.base)
        (p := ComboPath.all) (q := ComboPath.id)
        (show HistoryGraph.Deformation (P := ComboPrefix) ComboPath.all ComboPath.id from trivial)
        comboX0 comboX1 := combo_holonomy_all_id comboX0 comboX1
  have hId :
      HolonomyRel (P := ComboPrefix) comboSemantics comboObs comboTargetObs
        (h := ComboPrefix.base) (k := ComboPrefix.base)
        (p := ComboPath.id) (q := ComboPath.id)
        (show HistoryGraph.Deformation (P := ComboPrefix) ComboPath.id ComboPath.id from trivial)
        comboX0 comboX1 := (hEq comboX0 comboX1).1 hAll
  exact combo_not_holonomy_id_id_x0_x1 hId

/-- This instance cannot factor holonomy through any time-shot summary. -/
theorem combo_not_factorsHolonomyTime
    {A : Type uQ} [Preorder A] (t : TimeShot (P := ComboPrefix) A) :
    ¬ FactorsHolonomy (P := ComboPrefix) comboSemantics comboObs comboTargetObs (t.toSummary) := by
  have hp :
      t.toSummary (h := ComboPrefix.base) (k := ComboPrefix.base) ComboPath.all =
        t.toSummary (h := ComboPrefix.base) (k := ComboPrefix.base) ComboPath.id := rfl
  have hq :
      t.toSummary (h := ComboPrefix.base) (k := ComboPrefix.base) ComboPath.id =
        t.toSummary (h := ComboPrefix.base) (k := ComboPrefix.base) ComboPath.id := rfl
  exact witness_no_factor (P := ComboPrefix) comboSemantics comboObs comboTargetObs
    (q := t.toSummary)
    (h := ComboPrefix.base) (k := ComboPrefix.base)
    (α₁ := (show HistoryGraph.Deformation (P := ComboPrefix) ComboPath.all ComboPath.id from trivial))
    (α₂ := (show HistoryGraph.Deformation (P := ComboPrefix) ComboPath.id ComboPath.id from trivial))
    hp hq combo_holonomy_all_id_ne_holonomy_id_id

/-- Rich witness: the combo instance is non-reducible for every time-shot summary. -/
theorem combo_nonReducibleHolonomyTime :
    NonReducibleHolonomyTime (P := ComboPrefix) comboSemantics comboObs comboTargetObs := by
  intro A _ t
  exact combo_not_factorsHolonomyTime t

theorem combo_not_autoRegulatedWrt_singleton_gaugeRefl :
    ¬ AutoRegulatedWrt (P := ComboPrefix) comboSemantics comboObs comboTargetObs
      (fun φ => GaugeRefl (P := ComboPrefix) comboObs comboTargetObs φ)
      (Set.singleton
        (⟨ComboPrefix.base, ComboPrefix.base, ComboPath.all, ComboPath.id, ⟨by trivial⟩⟩ :
          Cell (P := ComboPrefix))) := by
  intro hAuto
  rcases hAuto with ⟨φ, hRefl, hFlatAll⟩
  let c0 : Cell (P := ComboPrefix) :=
    ⟨ComboPrefix.base, ComboPrefix.base, ComboPath.all, ComboPath.id, ⟨by trivial⟩⟩
  have hDiag :
      ∀ x x' : FiberPt (P := ComboPrefix) comboObs comboTargetObs ComboPrefix.base,
        CorrectedHolonomy (P := ComboPrefix) comboSemantics comboObs comboTargetObs φ
          (show HistoryGraph.Deformation (P := ComboPrefix) (h := ComboPrefix.base) (k := ComboPrefix.base)
            ComboPath.all ComboPath.id from trivial)
          x x' ↔ x = x' :=
    hFlatAll c0 (by exact Set.mem_singleton c0)
  have hHol :
      HolonomyRel (P := ComboPrefix) comboSemantics comboObs comboTargetObs
        (show HistoryGraph.Deformation (P := ComboPrefix) (h := ComboPrefix.base) (k := ComboPrefix.base)
          ComboPath.all ComboPath.id from trivial)
        comboX0 comboX1 :=
    combo_holonomy_all_id comboX0 comboX1
  have hCHol :
      CorrectedHolonomy (P := ComboPrefix) comboSemantics comboObs comboTargetObs φ
        (show HistoryGraph.Deformation (P := ComboPrefix) (h := ComboPrefix.base) (k := ComboPrefix.base)
          ComboPath.all ComboPath.id from trivial)
        comboX0 comboX1 :=
    correctedHolonomy_of_holonomy_of_gaugeRefl
      (P := ComboPrefix) comboSemantics comboObs comboTargetObs φ hRefl
      (show HistoryGraph.Deformation (P := ComboPrefix) (h := ComboPrefix.base) (k := ComboPrefix.base)
        ComboPath.all ComboPath.id from trivial)
      comboX0 comboX1 hHol
  exact comboX0_ne_comboX1 ((hDiag comboX0 comboX1).1 hCHol)

/-- Compact "no-discussion" package of the four core phenomena on the combo instance. -/
theorem combo_rich_witness :
    TwistedHolonomy (P := ComboPrefix) comboSemantics comboObs comboTargetObs
      (h := ComboPrefix.base) (k := ComboPrefix.base)
      (p := ComboPath.all) (q := ComboPath.id)
      (show HistoryGraph.Deformation (P := ComboPrefix) ComboPath.all ComboPath.id from trivial)
    ∧ LagEvent (P := ComboPrefix) comboSemantics comboObs comboTargetObs
        (h := ComboPrefix.base) (k := ComboPrefix.base) (k' := ComboPrefix.base)
        (p := ComboPath.all) (q := ComboPath.id)
        (show HistoryGraph.Deformation (P := ComboPrefix) ComboPath.all ComboPath.id from trivial)
        ComboPath.step
    ∧ ¬ AutoRegulatedWrt (P := ComboPrefix) comboSemantics comboObs comboTargetObs
        (fun φ => GaugeRefl (P := ComboPrefix) comboObs comboTargetObs φ)
        (Set.singleton
          (⟨ComboPrefix.base, ComboPrefix.base, ComboPath.all, ComboPath.id, ⟨by trivial⟩⟩ :
            Cell (P := ComboPrefix)))
    ∧ NonReducibleHolonomyTime (P := ComboPrefix) comboSemantics comboObs comboTargetObs := by
  refine ⟨combo_twistedHolonomy, combo_lagEvent, combo_not_autoRegulatedWrt_singleton_gaugeRefl, ?_⟩
  exact combo_nonReducibleHolonomyTime

end NontrivialCombinatorialInstance

end PrimitiveHolonomy

#print axioms PrimitiveHolonomy.holonomyRel_respects_probeSetoid
#print axioms PrimitiveHolonomy.holonomyRel_respects_probeSetoidOn
#print axioms PrimitiveHolonomy.combo_holonomy_all_id_iff_true
#print axioms PrimitiveHolonomy.combo_holonomy_id_id_iff_eq
#print axioms PrimitiveHolonomy.combo_twistedHolonomy
#print axioms PrimitiveHolonomy.combo_lagEvent
#print axioms PrimitiveHolonomy.combo_holonomy_all_id_ne_holonomy_id_id
#print axioms PrimitiveHolonomy.combo_not_factorsHolonomyTime
#print axioms PrimitiveHolonomy.combo_nonReducibleHolonomyTime
#print axioms PrimitiveHolonomy.combo_not_autoRegulatedWrt_singleton_gaugeRefl
#print axioms PrimitiveHolonomy.combo_rich_witness
#print axioms PrimitiveHolonomy.HolonomyCompatibleSetoid
#print axioms PrimitiveHolonomy.probeIndistinguishable_of_holonomyCompatibleSetoid
#print axioms PrimitiveHolonomy.holonomyCompatible_probeSetoid
#print axioms PrimitiveHolonomy.probeSetoid_terminal_holonomyCompatible
