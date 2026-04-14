import COFRS.Dynamics

/-!
# Primitive Holonomy: Regulation and Reduction

Gauges, corrected transport/holonomy, obstruction/auto-regulation, and the reduction/probe layer.
-/

universe u v w uQ

namespace PrimitiveHolonomy

variable {P : Type u}

section WithHistoryGraph

variable [HistoryGraph P]


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

/-- If two gauges agree pointwise, `CorrectedHolonomy` is invariant. -/
theorem correctedHolonomy_gauge_iff {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (φ₁ φ₂ : Gauge (P := P) obs target_obs)
    {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (hφ : ∀ {h' k' : P} (p' : HistoryGraph.Path h' k')
          (y y' : FiberPt (P := P) obs target_obs k'),
          φ₁ p' y y' ↔ φ₂ p' y y')
    (x x' : FiberPt (P := P) obs target_obs h) :
    CorrectedHolonomy sem obs target_obs φ₁ α x x' ↔
      CorrectedHolonomy sem obs target_obs φ₂ α x x' := by
  constructor
  · intro ⟨z, ⟨w, hw, hg1⟩, w', hw', hg1'⟩
    exact ⟨z, ⟨w, hw, (hφ p w z).mp hg1⟩, w', hw', (hφ q w' z).mp hg1'⟩
  · intro ⟨z, ⟨w, hw, hg2⟩, w', hw', hg2'⟩
    exact ⟨z, ⟨w, hw, (hφ p w z).mpr hg2⟩, w', hw', (hφ q w' z).mpr hg2'⟩


/-!
### 6.1 Invariance under re-labeling of observables (gauges / corrected holonomy)

If we postcompose both `obs : S → V` and `target_obs : P → V` by an equivalence `e : V ≃ V'`,
then the fiber types are canonically equivalent (via `fiberPtPostMap`), and the gauge / corrected
transport / corrected holonomy notions transport without changing truth.

These lemmas are used to show that `AutoRegulatedWrt` / `ObstructionWrt` are invariant under
observable re-labeling.
-/

section ObservableEquivGauge

variable {S : Type w} {V V' : Type w}

/-- Push a gauge forward along an equivalence of observables (`V ≃ V'`). -/
def gaugePost
    (obs : S → V) (target_obs : P → V) (e : Equiv V V')
    (φ : Gauge (P := P) obs target_obs) :
    Gauge (P := P) (obsPost e obs) (targetObsPost e target_obs) :=
  fun {h k : P} (p : HistoryGraph.Path h k) =>
    fun y y' =>
      φ (h := h) (k := k) p
        (fiberPtPostMapInv (P := P) e obs target_obs y)
        (fiberPtPostMapInv (P := P) e obs target_obs y')

/-- Pull a gauge back along an equivalence of observables (`V ≃ V'`). -/
def gaugePostInv
    (obs : S → V) (target_obs : P → V) (e : Equiv V V')
    (φ' : Gauge (P := P) (obsPost e obs) (targetObsPost e target_obs)) :
    Gauge (P := P) obs target_obs :=
  fun {h k : P} (p : HistoryGraph.Path h k) =>
    fun y y' =>
      φ' (h := h) (k := k) p
        (fiberPtPostMap (P := P) e obs target_obs y)
        (fiberPtPostMap (P := P) e obs target_obs y')

omit [HistoryGraph P] in
@[simp] theorem fiberPtPostMapInv_map
    (obs : S → V) (target_obs : P → V) (e : Equiv V V') {h : P}
    (x : FiberPt (P := P) obs target_obs h) :
    fiberPtPostMapInv (P := P) e obs target_obs (fiberPtPostMap (P := P) e obs target_obs x) = x := by
  apply Subtype.ext
  rfl

omit [HistoryGraph P] in
@[simp] theorem fiberPtPostMap_mapInv
    (obs : S → V) (target_obs : P → V) (e : Equiv V V') {h : P}
    (x : FiberPt (P := P) (obsPost e obs) (targetObsPost e target_obs) h) :
    fiberPtPostMap (P := P) e obs target_obs (fiberPtPostMapInv (P := P) e obs target_obs x) = x := by
  apply Subtype.ext
  rfl

omit [HistoryGraph P] in
theorem fiberPtPostMap_injective
    (obs : S → V) (target_obs : P → V) (e : Equiv V V') {h : P} :
    Function.Injective (fiberPtPostMap (P := P) e obs target_obs (h := h)) := by
  intro x x' hxx'
  -- apply the explicit inverse map and simplify
  have := congrArg (fiberPtPostMapInv (P := P) e obs target_obs) hxx'
  simpa using this

theorem gaugePostInv_gaugePost
    (obs : S → V) (target_obs : P → V) (e : Equiv V V')
    (φ : Gauge (P := P) obs target_obs)
    {h k : P} (p : HistoryGraph.Path h k)
    (y y' : FiberPt (P := P) obs target_obs k) :
    gaugePostInv (P := P) obs target_obs e (gaugePost (P := P) obs target_obs e φ) p y y' ↔
      φ p y y' := by
  dsimp [gaugePostInv, gaugePost]
  constructor
  · intro hg
    have h1 := fiberPtPostMapInv_map (P := P) obs target_obs e y
    have h2 := fiberPtPostMapInv_map (P := P) obs target_obs e y'
    rwa [h1, h2] at hg
  · intro hg
    have h1 := fiberPtPostMapInv_map (P := P) obs target_obs e y
    have h2 := fiberPtPostMapInv_map (P := P) obs target_obs e y'
    rwa [h1, h2]

theorem gaugePost_gaugePostInv
    (obs : S → V) (target_obs : P → V) (e : Equiv V V')
    (φ' : Gauge (P := P) (obsPost e obs) (targetObsPost e target_obs))
    {h k : P} (p : HistoryGraph.Path h k)
    (y y' : FiberPt (P := P) (obsPost e obs) (targetObsPost e target_obs) k) :
    gaugePost (P := P) obs target_obs e (gaugePostInv (P := P) obs target_obs e φ') p y y' ↔
      φ' p y y' := by
  dsimp [gaugePost, gaugePostInv]
  constructor
  · intro hg
    have h1 := fiberPtPostMap_mapInv (P := P) obs target_obs e y
    have h2 := fiberPtPostMap_mapInv (P := P) obs target_obs e y'
    rwa [h1, h2] at hg
  · intro hg
    have h1 := fiberPtPostMap_mapInv (P := P) obs target_obs e y
    have h2 := fiberPtPostMap_mapInv (P := P) obs target_obs e y'
    rwa [h1, h2]

theorem gaugeRefl_congr_postObsEquiv
    (obs : S → V) (target_obs : P → V) (e : Equiv V V')
    (φ : Gauge (P := P) obs target_obs) :
    GaugeRefl (P := P) obs target_obs φ ↔
      GaugeRefl (P := P) (obsPost e obs) (targetObsPost e target_obs)
        (gaugePost (P := P) obs target_obs e φ) := by
  constructor
  · intro hRefl h k p y
    -- unfold and use reflexivity on the pulled-back point
    simpa [gaugePost] using hRefl p (fiberPtPostMapInv (P := P) e obs target_obs y)
  · intro hRefl h k p y
    -- use reflexivity in the postcomposed world, then simplify
    have :
        gaugePost (P := P) obs target_obs e φ p
            (fiberPtPostMap (P := P) e obs target_obs y)
            (fiberPtPostMap (P := P) e obs target_obs y) :=
      hRefl p (fiberPtPostMap (P := P) e obs target_obs y)
    simpa [gaugePost] using this

theorem gaugeTotal_congr_postObsEquiv
    (obs : S → V) (target_obs : P → V) (e : Equiv V V')
    (φ : Gauge (P := P) obs target_obs) :
    GaugeTotal (P := P) obs target_obs φ ↔
      GaugeTotal (P := P) (obsPost e obs) (targetObsPost e target_obs)
        (gaugePost (P := P) obs target_obs e φ) := by
  constructor
  · intro hTot h k p y
    rcases hTot p (fiberPtPostMapInv (P := P) e obs target_obs y) with ⟨y', hy'⟩
    refine ⟨fiberPtPostMap (P := P) e obs target_obs y', ?_⟩
    simpa [gaugePost] using hy'
  · intro hTot h k p y
    rcases hTot p (fiberPtPostMap (P := P) e obs target_obs y) with ⟨y', hy'⟩
    refine ⟨fiberPtPostMapInv (P := P) e obs target_obs y', ?_⟩
    -- simplify using the map/inv simp lemma
    simpa [gaugePost] using hy'

theorem correctedTransport_congr_postObsEquiv
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V) (e : Equiv V V')
    (φ : Gauge (P := P) obs target_obs)
    {h k : P} (p : HistoryGraph.Path h k)
    (x : FiberPt (P := P) obs target_obs h) (y : FiberPt (P := P) obs target_obs k) :
    CorrectedTransport (P := P) sem obs target_obs φ p x y ↔
      CorrectedTransport (P := P) sem (obsPost e obs) (targetObsPost e target_obs)
        (gaugePost (P := P) obs target_obs e φ) p
        (fiberPtPostMap (P := P) e obs target_obs x)
        (fiberPtPostMap (P := P) e obs target_obs y) := by
  constructor
  · rintro ⟨z, hzT, hzG⟩
    refine ⟨fiberPtPostMap (P := P) e obs target_obs z, ?_, ?_⟩
    · -- transport is unchanged on underlying points
      simpa [CorrectedTransport, Transport] using hzT
    · simpa [CorrectedTransport, gaugePost] using hzG
  · rintro ⟨z, hzT, hzG⟩
    refine ⟨fiberPtPostMapInv (P := P) e obs target_obs z, ?_, ?_⟩
    · simpa [CorrectedTransport, Transport] using hzT
    · -- unfold gaugePost, then simplify the map/inv compositions
      simpa [CorrectedTransport, gaugePost] using hzG

theorem correctedHolonomy_congr_postObsEquiv
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V) (e : Equiv V V')
    (φ : Gauge (P := P) obs target_obs)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (x x' : FiberPt (P := P) obs target_obs h) :
    CorrectedHolonomy (P := P) sem obs target_obs φ α x x' ↔
      CorrectedHolonomy (P := P) sem (obsPost e obs) (targetObsPost e target_obs)
        (gaugePost (P := P) obs target_obs e φ) α
        (fiberPtPostMap (P := P) e obs target_obs x)
        (fiberPtPostMap (P := P) e obs target_obs x') := by
  constructor
  · intro hHol
    -- unfold as a relComp witness and map it
    unfold CorrectedHolonomy at hHol
    rcases hHol with ⟨y, hy1, hy2⟩
    refine ⟨fiberPtPostMap (P := P) e obs target_obs y, ?_, ?_⟩
    · -- corrected transport along p
      have := (correctedTransport_congr_postObsEquiv (P := P) sem obs target_obs e φ p x y).1 hy1
      simpa using this
    · -- corrected transport along q
      have := (correctedTransport_congr_postObsEquiv (P := P) sem obs target_obs e φ q x' y).1 hy2
      simpa using this
  · intro hHol
    unfold CorrectedHolonomy at hHol
    rcases hHol with ⟨y, hy1, hy2⟩
    let y0 : FiberPt (P := P) obs target_obs k :=
      fiberPtPostMapInv (P := P) e obs target_obs y
    refine ⟨y0, ?_, ?_⟩
    · have hy1' :
        CorrectedTransport (P := P) sem (obsPost e obs) (targetObsPost e target_obs)
          (gaugePost (P := P) obs target_obs e φ) p
          (fiberPtPostMap (P := P) e obs target_obs x)
          (fiberPtPostMap (P := P) e obs target_obs y0) := by
        simpa [y0] using hy1
      exact (correctedTransport_congr_postObsEquiv (P := P) sem obs target_obs e φ p x y0).2 hy1'
    · have hy2' :
        CorrectedTransport (P := P) sem (obsPost e obs) (targetObsPost e target_obs)
          (gaugePost (P := P) obs target_obs e φ) q
          (fiberPtPostMap (P := P) e obs target_obs x')
          (fiberPtPostMap (P := P) e obs target_obs y0) := by
        simpa [y0] using hy2
      exact (correctedTransport_congr_postObsEquiv (P := P) sem obs target_obs e φ q x' y0).2 hy2'

end ObservableEquivGauge

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
  fun c => CellSrc c ∈ C ∧ CellTgt c ∈ C

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
### 6.1b Invariance: obstruction / auto-regulation under observable re-labeling

The admissible-gauge variants (`Wrt`) are intended to be *invariant under re-labeling* of observable
values. Concretely, postcomposing both `obs : S → V` and `target_obs : P → V` by an equivalence
`e : V ≃ V'` should not change whether a given cell set is auto-regulated / obstructed.
-/

section ObservableEquivRegulation

variable {S : Type w} {V V' : Type w}

theorem autoRegulatedWrt_gaugeRefl_congr_postObsEquiv
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V) (e : Equiv V V')
    (J : Set (Cell (P := P))) :
    AutoRegulatedWrt (P := P) sem obs target_obs
      (fun φ => GaugeRefl (P := P) obs target_obs φ) J ↔
    AutoRegulatedWrt (P := P) sem (obsPost e obs) (targetObsPost e target_obs)
      (fun φ => GaugeRefl (P := P) (obsPost e obs) (targetObsPost e target_obs) φ) J := by
  constructor
  · rintro ⟨φ, hRefl, hflat⟩
    refine
      ⟨gaugePost (P := P) obs target_obs e φ,
        (gaugeRefl_congr_postObsEquiv (P := P) obs target_obs e φ).1 hRefl, ?_⟩
    intro c hc
    rcases c with ⟨h, k, p, q, ⟨α⟩⟩
    intro x₁ x₁'
    let x : FiberPt (P := P) obs target_obs h :=
      fiberPtPostMapInv (P := P) e obs target_obs x₁
    let x' : FiberPt (P := P) obs target_obs h :=
      fiberPtPostMapInv (P := P) e obs target_obs x₁'
    have hOrig : CorrectedHolonomy (P := P) sem obs target_obs φ α x x' ↔ x = x' := by
      simpa [x, x'] using (hflat (⟨h, k, p, q, ⟨α⟩⟩) hc x x')
    have hHol :
        CorrectedHolonomy (P := P) sem (obsPost e obs) (targetObsPost e target_obs)
          (gaugePost (P := P) obs target_obs e φ) α x₁ x₁' ↔
        CorrectedHolonomy (P := P) sem obs target_obs φ α x x' := by
      simpa [x, x'] using
        (correctedHolonomy_congr_postObsEquiv (P := P) sem obs target_obs e φ
            (p := p) (q := q) (α := α) x x').symm
    have hEq : x = x' ↔ x₁ = x₁' := by
      constructor
      · intro hxx
        have := congrArg (fiberPtPostMap (P := P) e obs target_obs) hxx
        simpa [x, x'] using this
      · intro hxx
        have := congrArg (fiberPtPostMapInv (P := P) e obs target_obs) hxx
        simpa [x, x'] using this
    calc
      CorrectedHolonomy (P := P) sem (obsPost e obs) (targetObsPost e target_obs)
          (gaugePost (P := P) obs target_obs e φ) α x₁ x₁'
          ↔ CorrectedHolonomy (P := P) sem obs target_obs φ α x x' := hHol
      _ ↔ x = x' := hOrig
      _ ↔ x₁ = x₁' := hEq
  · rintro ⟨φ', hRefl', hflat'⟩
    let φ : Gauge (P := P) obs target_obs :=
      gaugePostInv (P := P) obs target_obs e φ'
    have hRefl : GaugeRefl (P := P) obs target_obs φ := by
      intro h k p y
      -- unfold the pulled-back gauge and use reflexivity on the pushed-forward point
      simpa [φ, gaugePostInv] using
        hRefl' (p := p) (y := fiberPtPostMap (P := P) e obs target_obs y)
    refine ⟨φ, hRefl, ?_⟩
    intro c hc
    rcases c with ⟨h, k, p, q, ⟨α⟩⟩
    intro x x'
    let x₁ : FiberPt (P := P) (obsPost e obs) (targetObsPost e target_obs) h :=
      fiberPtPostMap (P := P) e obs target_obs x
    let x₁' : FiberPt (P := P) (obsPost e obs) (targetObsPost e target_obs) h :=
      fiberPtPostMap (P := P) e obs target_obs x'
    have hGaugeIff : ∀ {h' k' : P} (p' : HistoryGraph.Path h' k')
        (y y' : FiberPt (P := P) (obsPost e obs) (targetObsPost e target_obs) k'),
        gaugePost (P := P) obs target_obs e φ p' y y' ↔ φ' p' y y' := by
      intro h' k' p' y y'
      exact gaugePost_gaugePostInv (P := P) obs target_obs e φ' p' y y'
    have hPost :
        CorrectedHolonomy (P := P) sem (obsPost e obs) (targetObsPost e target_obs)
          φ' α x₁ x₁' ↔
          x₁ = x₁' := by
      simpa [x₁, x₁'] using (hflat' (⟨h, k, p, q, ⟨α⟩⟩) hc x₁ x₁')
    have hHol :
        CorrectedHolonomy (P := P) sem obs target_obs φ α x x' ↔
          CorrectedHolonomy (P := P) sem (obsPost e obs) (targetObsPost e target_obs)
            (gaugePost (P := P) obs target_obs e φ) α x₁ x₁' := by
      simpa [x₁, x₁'] using
        (correctedHolonomy_congr_postObsEquiv (P := P) sem obs target_obs e φ
            (p := p) (q := q) (α := α) x x')
    have hEq : x₁ = x₁' ↔ x = x' := by
      constructor
      · intro hxx
        have := congrArg (fiberPtPostMapInv (P := P) e obs target_obs) hxx
        simpa [x₁, x₁'] using this
      · intro hxx
        have := congrArg (fiberPtPostMap (P := P) e obs target_obs) hxx
        simpa [x₁, x₁'] using this
    have hHol' :
        CorrectedHolonomy (P := P) sem (obsPost e obs) (targetObsPost e target_obs)
          (gaugePost (P := P) obs target_obs e φ) α x₁ x₁' ↔ x = x' := by
      have hCorrGaugeEq :=
        correctedHolonomy_gauge_iff (P := P) sem (obsPost e obs) (targetObsPost e target_obs)
          (gaugePost (P := P) obs target_obs e φ) φ' α
          (fun p' y y' => hGaugeIff p' y y') x₁ x₁'
      exact hCorrGaugeEq.trans (hPost.trans hEq)
    show CorrectedHolonomy (P := P) sem obs target_obs φ α x x' ↔ x = x'
    exact hHol.trans hHol'

theorem obstructionWrt_gaugeRefl_congr_postObsEquiv
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V) (e : Equiv V V')
    (J : Set (Cell (P := P))) :
    ObstructionWrt (P := P) sem obs target_obs
      (fun φ => GaugeRefl (P := P) obs target_obs φ) J ↔
    ObstructionWrt (P := P) sem (obsPost e obs) (targetObsPost e target_obs)
      (fun φ => GaugeRefl (P := P) (obsPost e obs) (targetObsPost e target_obs) φ) J := by
  constructor
  · intro hObs φ' hRefl'
    let φ : Gauge (P := P) obs target_obs :=
      gaugePostInv (P := P) obs target_obs e φ'
    have hRefl : GaugeRefl (P := P) obs target_obs φ := by
      intro h k p y
      simpa [φ, gaugePostInv] using
        hRefl' (p := p) (y := fiberPtPostMap (P := P) e obs target_obs y)
    rcases hObs φ hRefl with ⟨c, hcJ, hw⟩
    refine ⟨c, hcJ, ?_⟩
    rcases c with ⟨h, k, p, q, ⟨α⟩⟩
    rcases hw with ⟨x, x', hxne, hHol⟩
    let x₁ : FiberPt (P := P) (obsPost e obs) (targetObsPost e target_obs) h :=
      fiberPtPostMap (P := P) e obs target_obs x
    let x₁' : FiberPt (P := P) (obsPost e obs) (targetObsPost e target_obs) h :=
      fiberPtPostMap (P := P) e obs target_obs x'
    refine ⟨x₁, x₁', ?_, ?_⟩
    · intro hEq
      apply hxne
      have := congrArg (fiberPtPostMapInv (P := P) e obs target_obs) hEq
      simpa [x₁, x₁'] using this
    · have hHolPost :
          CorrectedHolonomy (P := P) sem (obsPost e obs) (targetObsPost e target_obs)
            (gaugePost (P := P) obs target_obs e φ) α x₁ x₁' :=
        (correctedHolonomy_congr_postObsEquiv (P := P) sem obs target_obs e φ
            (p := p) (q := q) (α := α) x x').1 hHol
      have hGaugeIff : ∀ {h' k' : P} (p' : HistoryGraph.Path h' k')
          (y y' : FiberPt (P := P) (obsPost e obs) (targetObsPost e target_obs) k'),
          gaugePost (P := P) obs target_obs e φ p' y y' ↔ φ' p' y y' := by
        intro h' k' p' y y'
        exact gaugePost_gaugePostInv (P := P) obs target_obs e φ' p' y y'
      have hHolPostEta :
          CorrectedHolonomy (P := P) sem (obsPost e obs) (targetObsPost e target_obs)
            φ' α x₁ x₁' :=
        (correctedHolonomy_gauge_iff (P := P) sem (obsPost e obs) (targetObsPost e target_obs)
          (gaugePost (P := P) obs target_obs e φ) φ' α
          (fun p' y y' => hGaugeIff p' y y') x₁ x₁').mp hHolPost
      simpa using hHolPostEta
  · intro hObs φ hRefl
    have hRefl' :
        GaugeRefl (P := P) (obsPost e obs) (targetObsPost e target_obs)
          (gaugePost (P := P) obs target_obs e φ) :=
      (gaugeRefl_congr_postObsEquiv (P := P) obs target_obs e φ).1 hRefl
    rcases hObs (gaugePost (P := P) obs target_obs e φ) hRefl' with ⟨c, hcJ, hw⟩
    refine ⟨c, hcJ, ?_⟩
    rcases c with ⟨h, k, p, q, ⟨α⟩⟩
    rcases hw with ⟨x₁, x₁', hxne, hHol⟩
    let x : FiberPt (P := P) obs target_obs h :=
      fiberPtPostMapInv (P := P) e obs target_obs x₁
    let x' : FiberPt (P := P) obs target_obs h :=
      fiberPtPostMapInv (P := P) e obs target_obs x₁'
    refine ⟨x, x', ?_, ?_⟩
    · intro hEq
      apply hxne
      have := congrArg (fiberPtPostMap (P := P) e obs target_obs) hEq
      simpa [x, x'] using this
    · have hHol' :
          CorrectedHolonomy (P := P) sem (obsPost e obs) (targetObsPost e target_obs)
            (gaugePost (P := P) obs target_obs e φ) α
            (fiberPtPostMap (P := P) e obs target_obs x)
            (fiberPtPostMap (P := P) e obs target_obs x') := by
        simpa [x, x'] using hHol
      exact
        (correctedHolonomy_congr_postObsEquiv (P := P) sem obs target_obs e φ
            (p := p) (q := q) (α := α) x x').2 hHol'

end ObservableEquivRegulation
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
  refine ⟨(⟨h, k, p, q, ⟨α⟩⟩ : Cell (P := P)), ?_, ?_⟩
  · dsimp [Set.singleton]
    rfl
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

/--
A compact “dynamic no-go” package: twist + lag forces both compression failure and admissible obstruction.

This does **not** claim an external novelty; it is an internal classification interface.
-/
structure DiagonalDynamicClass {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k') : Prop where
  twisted : TwistedHolonomy sem obs target_obs α
  lag : LagEvent sem obs target_obs α step
  noVisiblePredictor : ¬ VisiblePredictsStep sem obs target_obs step
  obstructedRefl :
    ObstructionWrt sem obs target_obs
      (fun φ => GaugeRefl obs target_obs φ)
      (Set.singleton (⟨h, k, p, q, ⟨α⟩⟩ : Cell))
  notAutoRegulatedRefl :
    ¬ AutoRegulatedWrt sem obs target_obs
      (fun φ => GaugeRefl obs target_obs φ)
      (Set.singleton (⟨h, k, p, q, ⟨α⟩⟩ : Cell))


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
    exact ⟨φ, ⟨hOK, hFlat⟩⟩
  · intro hGood c hcJ
    rcases hGood c hcJ with ⟨φ, ⟨hOK, hFlat⟩⟩
    exact ⟨φ, hOK, hFlat⟩

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
    exact ⟨φ, hOK, fun c hcJ => ⟨hOK, hFlatAll c hcJ⟩⟩
  · intro h
    rcases h with ⟨φ, hOK, hGood⟩
    exact ⟨φ, hOK, fun c hcJ => (hGood c hcJ).2⟩

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
    exact ⟨φ, hOK, hFlatAll⟩
  · intro hI
    rcases hI with ⟨φ, hOK, hAll⟩
    exact ⟨φ, hOK, hAll⟩

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
    exact ⟨c, hcJ, hw⟩
  · intro hObs φ hOK
    rcases hObs φ hOK with ⟨c, hcJ, hTw⟩
    exact ⟨c, hcJ, hTw⟩

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
  have hTw : TwistedOnCell (P := P) sem obs target_obs φ c := hw
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
  fun i => Reach (P := P) h (s.c i)

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
available probe family grows. Everything here is constructive: no classical axioms, no propositional extensionality,
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


theorem probeObstruction_strict_chain_of_injectiveSeq
    {a : Nat → C.Obj} (ha : Function.Injective a)
    (hRangeFinite : ∀ n : Nat, (Set.range (fun i : Fin n => a i)).Finite)
    (hObs : ProbeObstruction (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h)) :
    ∃ x y : FiberPt (P := P) obs target_obs h,
      (∀ n : Nat,
        let Cn : Set C.Obj := Set.range (fun i : Fin n => a i)
        let Cn' : Set C.Obj := Set.range (fun i : Fin (n + 1) => a i)
        Cn.Finite ∧
        Cn ⊆ Cn' ∧
        (a n ∈ Cn' ∧ a n ∉ Cn) ∧
        ProbeIndist (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) Cn x y ∧
        ¬ StableAt (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) Cn x y) ∧
      ¬ ProbeIndist (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) Set.univ x y := by
  rcases hObs with ⟨x, y, hFin, hUniv⟩
  refine ⟨x, y, ?_, hUniv⟩
  intro n
  let Cn : Set C.Obj := Set.range (fun i : Fin n => a i)
  let Cn' : Set C.Obj := Set.range (fun i : Fin (n + 1) => a i)
  have hCnFinite : Cn.Finite := hRangeFinite n
  have hsub : Cn ⊆ Cn' := by
    intro c hc
    rcases hc with ⟨i, rfl⟩
    exact ⟨Fin.castSucc i, rfl⟩
  have hmem_succ : a n ∈ Cn' := by
    exact ⟨⟨n, Nat.lt_succ_self n⟩, rfl⟩
  have hnot_mem : a n ∉ Cn := by
    intro hmem
    rcases hmem with ⟨i, hi⟩
    have hEq : (i : Nat) = n := ha hi
    have hlt : n < n := by
      have hlt' : (i : Nat) < n := i.isLt
      exact hEq.rec (motive := fun t _ => t < n) hlt'
    exact (Nat.lt_irrefl n) hlt
  have hCn_xy : ProbeIndist (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) Cn x y :=
    hFin Cn hCnFinite
  have hNotStable :
      ¬ StableAt (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) Cn x y :=
    not_stableAt_of_indist_and_not_univ (P := P) (C := C) (fam := fam) (obs := obs)
      (target_obs := target_obs) (h := h) (C0 := Cn) hCn_xy hUniv
  refine ⟨hCnFinite, hsub, ⟨hmem_succ, hnot_mem⟩, hCn_xy, hNotStable⟩


end ProbeBudget

/-!
## Probe “quotient” (setoid-only)

This development is intentionally **setoid-only**: the probe “quotient” is the canonical
setoid `ProbeSetoid ...` on the fiber, and it is **terminal / greatest** among all fiber setoids
whose equivalence relation is holonomy-compatible.

No quotient type realization is used anywhere in this repository.
-/

section ProbeSetoidOnly

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

end ProbeSetoidOnly

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

/--
If `C0` covered all coefficients, then any global distinction would already appear on `C0`.
-/
theorem not_probeIndistinguishableOn_of_coeffCovers_and_not_probeIndistinguishable
    {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S) (C0 : Set C.Obj)
    (obs : S → V) (target_obs : P → V) (h : P)
    (hCover : CoeffCovers (P := P) C fam C0 obs target_obs)
    {x y : FiberPt (P := P) obs target_obs h} :
    ¬ ProbeIndistinguishable (P := P) C fam obs target_obs h x y →
      ¬ ProbeIndistinguishableOn (P := P) C fam C0 obs target_obs h x y := by
  intro hNot hOn
  exact hNot
    ((probeIndistinguishable_iff_probeIndistinguishableOn_of_coeffCovers
      (P := P) C fam C0 obs target_obs h hCover x y).2 hOn)

/--
Witness form of probe insufficiency: if a pair is still indistinguishable on `C0` but
distinguishable globally, then `C0` cannot cover all coefficients.
-/
theorem not_coeffCovers_of_probeIndistinguishableOn_and_not_probeIndistinguishable
    {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S) (C0 : Set C.Obj)
    (obs : S → V) (target_obs : P → V) (h : P)
    {x y : FiberPt (P := P) obs target_obs h}
    (hOn : ProbeIndistinguishableOn (P := P) C fam C0 obs target_obs h x y)
    (hNot : ¬ ProbeIndistinguishable (P := P) C fam obs target_obs h x y) :
    ¬ CoeffCovers (P := P) C fam C0 obs target_obs := by
  intro hCover
  exact
    (not_probeIndistinguishableOn_of_coeffCovers_and_not_probeIndistinguishable
      (P := P) C fam C0 obs target_obs h hCover hNot) hOn

/--
Under a probe obstruction, no finite coefficient family can already cover the full probe power:
the same witness pair stays indistinguishable on every finite budget, but not for the full family.
-/
theorem probeObstruction_forces_no_finite_coeffCover
    {P : Type u} [HistoryGraph P] {S V : Type w}
    (C : CoeffCat) (fam : SemFamily C P S)
    (obs : S → V) (target_obs : P → V) (h : P) :
    ProbeObstruction (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) →
      ∃ x y : FiberPt (P := P) obs target_obs h,
        ∀ C0 : Set C.Obj, Set.Finite C0 →
          ProbeIndist (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h) C0 x y
          ∧ ¬ CoeffCovers (P := P) C fam C0 obs target_obs := by
  rintro ⟨x, y, hFin, hUniv⟩
  refine ⟨x, y, ?_⟩
  intro C0 hC0
  refine ⟨hFin C0 hC0, ?_⟩
  intro hCover
  have hAll :
      ProbeIndistinguishable (P := P) C fam obs target_obs h x y :=
    probeIndistinguishable_of_probeIndistinguishableOn_of_coeffCovers
      (P := P) C fam C0 obs target_obs h hCover (hFin C0 hC0)
  have hOnUniv :
      ProbeIndist (P := P) (C := C) (fam := fam) (obs := obs) (target_obs := target_obs) (h := h)
        Set.univ x y :=
    probeIndistinguishableOn_of_probeIndistinguishable
      (P := P) C fam Set.univ obs target_obs h hAll
  exact hUniv hOnUniv



section ProbeOperational

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

end ProbeOperational


end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
Auto-generated: `#print axioms` for each non-private `theorem`/`lemma` in this file.
-/
#print axioms PrimitiveHolonomy.fiberPtPostMapInv_map
#print axioms PrimitiveHolonomy.fiberPtPostMap_mapInv
#print axioms PrimitiveHolonomy.fiberPtPostMap_injective
#print axioms PrimitiveHolonomy.gaugePostInv_gaugePost
#print axioms PrimitiveHolonomy.gaugePost_gaugePostInv
#print axioms PrimitiveHolonomy.gaugeRefl_congr_postObsEquiv
#print axioms PrimitiveHolonomy.gaugeTotal_congr_postObsEquiv
#print axioms PrimitiveHolonomy.correctedTransport_congr_postObsEquiv
#print axioms PrimitiveHolonomy.correctedHolonomy_congr_postObsEquiv
#print axioms PrimitiveHolonomy.correctedTransport_of_transport_of_gaugeRefl
#print axioms PrimitiveHolonomy.correctedHolonomy_of_holonomy_of_gaugeRefl
#print axioms PrimitiveHolonomy.not_correctedTransport_emptyGauge
#print axioms PrimitiveHolonomy.not_correctedHolonomy_emptyGauge
#print axioms PrimitiveHolonomy.is_constructive
#print axioms PrimitiveHolonomy.reach_refl
#print axioms PrimitiveHolonomy.reach_trans
#print axioms PrimitiveHolonomy.cofinal_range_of_scheduling
#print axioms PrimitiveHolonomy.autoRegulatedWrt_gaugeRefl_congr_postObsEquiv
#print axioms PrimitiveHolonomy.obstructionWrt_gaugeRefl_congr_postObsEquiv
#print axioms PrimitiveHolonomy.obstruction_mono_J
#print axioms PrimitiveHolonomy.obstructionWrt_mono_J
#print axioms PrimitiveHolonomy.autoRegulated_anti_J
#print axioms PrimitiveHolonomy.autoRegulatedWrt_anti_J
#print axioms PrimitiveHolonomy.autoRegulatedWrt_mono_OK
#print axioms PrimitiveHolonomy.obstructionWrt_anti_OK
#print axioms PrimitiveHolonomy.not_Obstruction_of_emptyGauge
#print axioms PrimitiveHolonomy.not_AutoRegulatedWrt_of_ObstructionWrt
#print axioms PrimitiveHolonomy.not_ObstructionWrt_of_AutoRegulatedWrt
#print axioms PrimitiveHolonomy.obstructionWrt_singleton_of_twistedHolonomy_of_gaugeRefl
#print axioms PrimitiveHolonomy.not_autoRegulatedWrt_singleton_of_twistedHolonomy_of_gaugeRefl
#print axioms PrimitiveHolonomy.autoRegulatedCofinal_of_autoRegulatedAlong
#print axioms PrimitiveHolonomy.obstructionCofinal_of_obstructionAlong
#print axioms PrimitiveHolonomy.autoRegulatedCofinalWrt_of_autoRegulatedAlongWrt
#print axioms PrimitiveHolonomy.obstructionCofinalWrt_of_obstructionAlongWrt
#print axioms PrimitiveHolonomy.not_AutoRegulated_of_Obstruction
#print axioms PrimitiveHolonomy.not_Obstruction_of_AutoRegulated
#print axioms PrimitiveHolonomy.not_AutoRegulatedAlong_of_ObstructionAlong
#print axioms PrimitiveHolonomy.not_ObstructionAlong_of_AutoRegulatedAlong
#print axioms PrimitiveHolonomy.locallyAutoRegulated_of_AutoRegulated
#print axioms PrimitiveHolonomy.locallyAutoRegulatedWrt_of_autoRegulatedWrt
#print axioms PrimitiveHolonomy.locallyAutoRegulatedWrt_iff_goodGaugeForCell_nonempty
#print axioms PrimitiveHolonomy.autoRegulatedWrt_iff_exists_goodGaugeForAllCells
#print axioms PrimitiveHolonomy.autoRegulatedWrt_iff_goodGaugeIntersection_nonempty
#print axioms PrimitiveHolonomy.obstructionWrt_iff_twistedOnCell
#print axioms PrimitiveHolonomy.twistedOnCell_not_goodGaugeForCellWrt
#print axioms PrimitiveHolonomy.obstructionWrt_implies_exists_cell_not_goodGauge
#print axioms PrimitiveHolonomy.localAndNotAutoRegulatedWrt_of_localFlatButObstructedCofinalWrt
#print axioms PrimitiveHolonomy.not_autoRegulatedWrt_of_localFlatButObstructedCofinalWrt
#print axioms PrimitiveHolonomy.factors_eq_of_codes
#print axioms PrimitiveHolonomy.witness_no_factor
#print axioms PrimitiveHolonomy.probeIndist_anti_mono
#print axioms PrimitiveHolonomy.not_stableAt_of_indist_and_not_univ
#print axioms PrimitiveHolonomy.probeObstruction_not_finitaryCompactness
#print axioms PrimitiveHolonomy.finitaryCompactness_not_probeObstruction
#print axioms PrimitiveHolonomy.probeObstruction_forces_no_finite_stabilization
#print axioms PrimitiveHolonomy.probeObstruction_strict_chain_of_injectiveSeq
#print axioms PrimitiveHolonomy.holonomyCompatible_probeSetoid
#print axioms PrimitiveHolonomy.probeIndistinguishable_of_holonomyCompatibleSetoid
#print axioms PrimitiveHolonomy.probeSetoid_terminal_holonomyCompatible
#print axioms PrimitiveHolonomy.coeffCovers_of_coeffCofinal_of_holonomyNatural_of_pushConservativeOnHolonomy
#print axioms PrimitiveHolonomy.probeIndistinguishableOn_of_probeIndistinguishable
#print axioms PrimitiveHolonomy.probeIndistinguishable_of_probeIndistinguishableOn_of_coeffCovers
#print axioms PrimitiveHolonomy.probeIndistinguishable_iff_probeIndistinguishableOn_of_coeffCovers
#print axioms PrimitiveHolonomy.not_probeIndistinguishableOn_of_coeffCovers_and_not_probeIndistinguishable
#print axioms PrimitiveHolonomy.not_coeffCovers_of_probeIndistinguishableOn_and_not_probeIndistinguishable
#print axioms PrimitiveHolonomy.probeObstruction_forces_no_finite_coeffCover
#print axioms PrimitiveHolonomy.holonomyRel_respects_probeSetoid
#print axioms PrimitiveHolonomy.holonomyRel_respects_probeSetoidOn
/- AXIOM_AUDIT_END -/
