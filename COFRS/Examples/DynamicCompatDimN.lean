import COFRS.Synthesis

/-!
# Primitive Holonomy (curated): dynamic parametric `CompatDim = n` example

This file provides a *dynamic* family of examples indexed by `n`.

It generalizes the earlier `Fin 3` dynamic witness without using `Fin` numerals
(which can introduce propositional extensionality through `OfNat` in some toolchains).

Model parameters:
- `n : Nat` with `1 < n` (so we can pick two distinct hidden values);
- `Pred : Fin n → Prop` controlling future compatibility.

Structure:
- prefixes `base`, `mid`, `fut`;
- paths `p,q : base → mid` (holonomy cell) and `step : base → fut` (future compatibility split);
- `p` and `q` erase hidden information to a fixed `erase : Fin n`;
- `step` preserves the full state and is compatible iff `Pred hidden`.

Results:
- `TwistedHolonomy` for the `(p ⇒ q)` cell;
- a `LagEvent` for `step` under `Pred i0 ∧ ¬ Pred i1`;
- hence `DiagonalDynamicClass` under `GaugeRefl`;
- and an exact compatibility dimension statement for `step`:
  `CompatDimEq … step n` under a `PairwisePropSeparated Pred` hypothesis.

The split theorem `profileDimSplit_step_stepDim_n_of_pairwisePropSeparated` is the canonical
parametric witness family for the abstract mediator-minimality hypothesis used by
`COFRS/Examples/IndependenceRelationMediationChain.lean`: the qualitative no-go lives on `step`,
while the finite lower-bound/exactness witness lives on `stepDim`.

All proofs are constructive.
-/

universe u v w uQ

namespace PrimitiveHolonomy
namespace Examples
namespace DynamicCompatDimN

section

variable (n : Nat) (hn : 1 < n)

/-- Three prefixes: `base` (source), `mid` (for the holonomy cell), and `fut` (for the future step). -/
inductive DPrefix where
  | base
  | mid
  | fut
  deriving DecidableEq

/-- Paths indexed by endpoints. -/
inductive DPath : DPrefix → DPrefix → Type where
  | id (h : DPrefix) : DPath h h
  | p : DPath DPrefix.base DPrefix.mid
  | q : DPath DPrefix.base DPrefix.mid
  | step : DPath DPrefix.base DPrefix.fut
  | stepDim : DPath DPrefix.base DPrefix.fut

 /-- Composition: only identities compose with anything (no composable non-identity pairs). -/
 def dComp : {h k l : DPrefix} → DPath h k → DPath k l → DPath h l
   | _h, _k, _l, r, s => by
       cases r with
       | id _ => exact s
       | p => cases s with | id _ => exact DPath.p
       | q => cases s with | id _ => exact DPath.q
       | step => cases s with | id _ => exact DPath.step
       | stepDim => cases s with | id _ => exact DPath.stepDim

 /-- The unique deformation witness `p ⇒ q`. -/
 inductive DDef : {h k : DPrefix} → DPath h k → DPath h k → Prop where
   | pq : DDef DPath.p DPath.q

 instance : HistoryGraph DPrefix where
   Path h k := DPath h k
   Deformation {_ _} pth qth := DDef pth qth
   idPath h := DPath.id h
   compPath := dComp

 def α_pq :
     HistoryGraph.Deformation (P := DPrefix) (h := DPrefix.base) (k := DPrefix.mid)
       (DPath.p : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid)
       (DPath.q : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid) :=
   DDef.pq

 /-- State space: visible `Bool` and hidden `Fin n`. -/
 abbrev DState : Type := LagState Bool (Fin n)

 def dObs : DState n → Bool := lagObs (Y := Bool) (B := Fin n)

 /-- Non-constant target observation across prefixes (avoids degenerate `Unit`-fibers). -/
 def dTargetObs : DPrefix → Bool
   | DPrefix.base => false
   | DPrefix.mid => true
   | DPrefix.fut => false

/-- A canonical erased hidden value `i0 : Fin n`, avoiding `OfNat` on `Fin`. -/
def i0 : Fin n :=
  ⟨0, Nat.lt_trans (Nat.succ_pos 0) hn⟩

/-- A second hidden value `i1 : Fin n`, using the hypothesis `1 < n`. -/
def i1 : Fin n :=
  ⟨1, hn⟩

theorem i0_ne_i1 : i0 n hn ≠ i1 n hn := by
  intro hEq
  have : (i0 n hn).val = (i1 n hn).val := congrArg Fin.val hEq
  exact Nat.zero_ne_one this

/-- Semantics for `DPath`, parameterized by `Pred : Fin n → Prop`. -/
def dRel2 (PredStep PredDim : Fin n → Prop) {h k : DPrefix} : DPath h k → Relation (DState n) (DState n)
  | DPath.id _ => relId
  | DPath.p => fun _x y => y.hidden = i0 n hn
  | DPath.q => fun _x y => y.hidden = i0 n hn
  | DPath.step => fun x y => x = y ∧ PredStep x.hidden
  | DPath.stepDim => fun x y => x = y ∧ PredDim x.hidden

theorem dRel2_comp (PredStep PredDim : Fin n → Prop)
    {h k l : DPrefix} (r : DPath h k) (s : DPath k l) (x y : DState n) :
    dRel2 (n := n) (hn := hn) PredStep PredDim (dComp r s) x y ↔
      relComp (dRel2 (n := n) (hn := hn) PredStep PredDim r) (dRel2 (n := n) (hn := hn) PredStep PredDim s) x y := by
  cases r with
  | id _ =>
      cases s <;>
        exact ⟨(fun h => ⟨_, rfl, h⟩), (fun ⟨_, rfl, h⟩ => h)⟩
  | p =>
      cases s with
      | id _ => exact ⟨(fun h => ⟨_, h, rfl⟩), (fun ⟨_, h, rfl⟩ => h)⟩
  | q =>
      cases s with
      | id _ => exact ⟨(fun h => ⟨_, h, rfl⟩), (fun ⟨_, h, rfl⟩ => h)⟩
  | step =>
      cases s with
      | id _ => exact ⟨(fun h => ⟨_, h, rfl⟩), (fun ⟨_, h, rfl⟩ => h)⟩
  | stepDim =>
      cases s with
      | id _ => exact ⟨(fun h => ⟨_, h, rfl⟩), (fun ⟨_, h, rfl⟩ => h)⟩

/-- Backwards-compatible semantics for `DPath.step` (uses the same predicate for both steps). -/
def dRel (Pred : Fin n → Prop) {h k : DPrefix} : DPath h k → Relation (DState n) (DState n) :=
  dRel2 (n := n) (hn := hn) Pred Pred

theorem dRel_comp (Pred : Fin n → Prop)
    {h k l : DPrefix} (r : DPath h k) (s : DPath k l) (x y : DState n) :
    dRel (n := n) (hn := hn) Pred (dComp r s) x y ↔
      relComp (dRel (n := n) (hn := hn) Pred r) (dRel (n := n) (hn := hn) Pred s) x y := by
  exact dRel2_comp (n := n) (hn := hn) Pred Pred r s x y

/-- Semantics instance parameterized by `Pred : Fin n → Prop`. -/
def dSemantics (Pred : Fin n → Prop) : Semantics DPrefix (DState n) where
  sem := fun {h k} r => dRel (n := n) (hn := hn) Pred r
  sem_id := by
    intro h x y
    cases h <;> rfl
  sem_comp := by
    intro _h _k _l r s x y
    exact dRel_comp (n := n) (hn := hn) Pred r s x y

/-- Semantics instance parameterized by two predicates: one for `step`, one for `stepDim`. -/
def dSemantics2 (PredStep PredDim : Fin n → Prop) : Semantics DPrefix (DState n) where
  sem := fun {h k} r => dRel2 (n := n) (hn := hn) PredStep PredDim r
  sem_id := by
    intro h x y
    cases h <;> rfl
  sem_comp := by
    intro _h _k _l r s x y
    exact dRel2_comp (n := n) (hn := hn) PredStep PredDim r s x y

 /-- Fiber point with visible `()` and hidden value `i` at any prefix `h`. -/
 def dX (h : DPrefix) (i : Fin n) : FiberPt (P := DPrefix) (dObs (n := n)) (dTargetObs) h :=
   ⟨⟨dTargetObs h, i⟩, rfl⟩

/-- Compatibility along `step` depends only on the hidden coordinate. -/
theorem compatible_step_iff_hidden (Pred : Fin n → Prop)
    (x : FiberPt (P := DPrefix) (dObs (n := n)) dTargetObs DPrefix.base) :
    Compatible (P := DPrefix) (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
      (h := DPrefix.base) (k := DPrefix.fut)
      (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) x ↔
      Pred x.1.hidden := by
  constructor
  · rintro ⟨y, hy⟩
    exact (hy : x.1 = y.1 ∧ Pred x.1.hidden).2
  · intro hPred
    -- Reuse the same ambient state `x.1` as a point of the `fut` fiber.
    -- Since `targetObs base = targetObs fut = false`, membership transfers.
    have hxmemBase : dObs (n := n) x.1 = dTargetObs DPrefix.base := x.2
    have hxmemFut : dObs (n := n) x.1 = dTargetObs DPrefix.fut := by
      dsimp [dTargetObs] at hxmemBase
      dsimp [dTargetObs]
      exact hxmemBase
    refine ⟨⟨x.1, hxmemFut⟩, ?_⟩
    · exact ⟨rfl, hPred⟩

/-- Compatibility along `stepDim` depends only on the hidden coordinate (via `PredDim`). -/
theorem compatible_stepDim_iff_hidden (PredStep PredDim : Fin n → Prop)
    (x : FiberPt (P := DPrefix) (dObs (n := n)) dTargetObs DPrefix.base) :
    Compatible (P := DPrefix) (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
      (h := DPrefix.base) (k := DPrefix.fut)
      (DPath.stepDim : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) x ↔
      PredDim x.1.hidden := by
  constructor
  · rintro ⟨y, hy⟩
    exact (hy : x.1 = y.1 ∧ PredDim x.1.hidden).2
  · intro hPred
    have hxmemBase : dObs (n := n) x.1 = dTargetObs DPrefix.base := x.2
    have hxmemFut : dObs (n := n) x.1 = dTargetObs DPrefix.fut := by
      dsimp [dTargetObs] at hxmemBase
      dsimp [dTargetObs]
      exact hxmemBase
    refine ⟨⟨x.1, hxmemFut⟩, ?_⟩
    exact ⟨rfl, hPred⟩

/-- Compatibility along `step` under `dSemantics2` depends only on the hidden coordinate. -/
theorem compatible_step2_iff_hidden (PredStep PredDim : Fin n → Prop)
    (x : FiberPt (P := DPrefix) (dObs (n := n)) dTargetObs DPrefix.base) :
    Compatible (P := DPrefix) (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
      (h := DPrefix.base) (k := DPrefix.fut)
      (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) x ↔
      PredStep x.1.hidden := by
  constructor
  · rintro ⟨y, hy⟩
    exact (hy : x.1 = y.1 ∧ PredStep x.1.hidden).2
  · intro hPred
    have hxmemBase : dObs (n := n) x.1 = dTargetObs DPrefix.base := x.2
    have hxmemFut : dObs (n := n) x.1 = dTargetObs DPrefix.fut := by
      dsimp [dTargetObs] at hxmemBase
      dsimp [dTargetObs]
      exact hxmemBase
    refine ⟨⟨x.1, hxmemFut⟩, ?_⟩
    exact ⟨rfl, hPred⟩

/-- Twisted holonomy witness for the `p ⇒ q` cell. -/
theorem twistedHolonomy_pq (Pred : Fin n → Prop) :
    TwistedHolonomy (P := DPrefix)
      (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
      (h := DPrefix.base) (k := DPrefix.mid)
      (p := (DPath.p : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid))
      (q := (DPath.q : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid))
      α_pq := by
  -- Choose two distinct fiber points at `base`.
  let x : FiberPt (P := DPrefix) (dObs (n := n)) dTargetObs DPrefix.base := dX (n := n) DPrefix.base (i0 n hn)
  let x' : FiberPt (P := DPrefix) (dObs (n := n)) dTargetObs DPrefix.base := dX (n := n) DPrefix.base (i1 n hn)
  have hxne : x ≠ x' := by
    intro hEq
    have : (i0 n hn) = (i1 n hn) := by
      have : x.1.hidden = x'.1.hidden := congrArg (fun z => z.1.hidden) hEq
      simpa [x, x'] using this
    exact (i0_ne_i1 n hn) this

  refine ⟨x, x', hxne, ?_⟩
  -- Prove holonomy by exhibiting a common transported target at `mid`.
  have hHolWitness :
      ∃ y : FiberPt (P := DPrefix) (dObs (n := n)) dTargetObs DPrefix.mid,
        Transport (P := DPrefix) (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
          (DPath.p : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid) x y ∧
        Transport (P := DPrefix) (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
          (DPath.q : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid) x' y := by
    refine ⟨dX (n := n) DPrefix.mid (i0 n hn), ?_, ?_⟩
    · -- `p` forces the target hidden to `i0`.
      rfl
    · -- `q` forces the target hidden to `i0`.
      rfl

  -- Convert the witness into `HolonomyRel`.
  exact (PrimitiveHolonomy.holonomy_def
    (P := DPrefix)
    (sem := dSemantics (n := n) (hn := hn) Pred)
    (obs := dObs (n := n))
    (target_obs := dTargetObs)
    (α := α_pq)
    (x := x) (x' := x')).2 hHolWitness

/-- Twisted holonomy witness for the `p ⇒ q` cell (for `dSemantics2`). -/
theorem twistedHolonomy_pq2 (PredStep PredDim : Fin n → Prop) :
    TwistedHolonomy (P := DPrefix)
      (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
      (h := DPrefix.base) (k := DPrefix.mid)
      (p := (DPath.p : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid))
      (q := (DPath.q : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid))
      α_pq := by
  let x : FiberPt (P := DPrefix) (dObs (n := n)) dTargetObs DPrefix.base := dX (n := n) DPrefix.base (i0 n hn)
  let x' : FiberPt (P := DPrefix) (dObs (n := n)) dTargetObs DPrefix.base := dX (n := n) DPrefix.base (i1 n hn)
  have hxne : x ≠ x' := by
    intro hEq
    have : (i0 n hn) = (i1 n hn) := by
      have : x.1.hidden = x'.1.hidden := congrArg (fun z => z.1.hidden) hEq
      simpa [x, x'] using this
    exact (i0_ne_i1 n hn) this

  refine ⟨x, x', hxne, ?_⟩
  have hHolWitness :
      ∃ y : FiberPt (P := DPrefix) (dObs (n := n)) dTargetObs DPrefix.mid,
        Transport (P := DPrefix) (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
          (DPath.p : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid) x y ∧
        Transport (P := DPrefix) (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
          (DPath.q : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid) x' y := by
    refine ⟨dX (n := n) DPrefix.mid (i0 n hn), ?_, ?_⟩ <;> rfl

  exact (PrimitiveHolonomy.holonomy_def
    (P := DPrefix)
    (sem := dSemantics2 (n := n) (hn := hn) PredStep PredDim)
    (obs := dObs (n := n))
    (target_obs := dTargetObs)
    (α := α_pq)
    (x := x) (x' := x')).2 hHolWitness

/-- A lag event for `step`, assuming `Pred i0` but `¬ Pred i1`. -/
theorem lagEvent_of_Pi0_notPi1
    (Pred : Fin n → Prop)
    (hPos : Pred (i0 n hn))
    (hNeg : ¬ Pred (i1 n hn)) :
    LagEvent (P := DPrefix)
      (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
      (h := DPrefix.base) (k := DPrefix.mid) (k' := DPrefix.fut)
      (p := (DPath.p : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid))
      (q := (DPath.q : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid))
      α_pq
      (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) := by
  let x : FiberPt (P := DPrefix) (dObs (n := n)) dTargetObs DPrefix.base := dX (n := n) DPrefix.base (i0 n hn)
  let x' : FiberPt (P := DPrefix) (dObs (n := n)) dTargetObs DPrefix.base := dX (n := n) DPrefix.base (i1 n hn)
  have hxne : x ≠ x' := by
    intro hEq
    have : (i0 n hn) = (i1 n hn) := by
      have : x.1.hidden = x'.1.hidden := congrArg (fun z => z.1.hidden) hEq
      simpa [x, x'] using this
    exact (i0_ne_i1 n hn) this

  have hHol :
      HolonomyRel (P := DPrefix)
        (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
        α_pq x x' := by
    -- Same witness as in `twistedHolonomy_pq`.
    have hHolWitness :
        ∃ y : FiberPt (P := DPrefix) (dObs (n := n)) dTargetObs DPrefix.mid,
          Transport (P := DPrefix) (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
            (DPath.p : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid) x y ∧
          Transport (P := DPrefix) (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
            (DPath.q : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid) x' y := by
      refine ⟨dX (n := n) DPrefix.mid (i0 n hn), rfl, rfl⟩
    exact (PrimitiveHolonomy.holonomy_def
      (P := DPrefix)
      (sem := dSemantics (n := n) (hn := hn) Pred)
      (obs := dObs (n := n))
      (target_obs := dTargetObs)
      (α := α_pq)
      (x := x) (x' := x')).2 hHolWitness

  have hCx :
      Compatible (P := DPrefix) (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
        (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) x := by
    -- `Compatible step x ↔ Pred x.hidden`.
    have : Pred x.1.hidden := by simpa [x] using hPos
    have hxCompat :
        Compatible (P := DPrefix) (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
          (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) x ↔ Pred x.1.hidden :=
      compatible_step_iff_hidden (n := n) (hn := hn) Pred x
    exact (hxCompat.mpr this)

  have hNCx' :
      ¬ Compatible (P := DPrefix) (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
        (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) x' := by
    intro hx'
    have hxCompat :
        Compatible (P := DPrefix) (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
          (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) x' ↔ Pred x'.1.hidden :=
      compatible_step_iff_hidden (n := n) (hn := hn) Pred x'
    have : Pred x'.1.hidden := hxCompat.mp hx'
    have : Pred (i1 n hn) := by simpa [x'] using this
    exact hNeg this

  exact ⟨x, x', hxne, hHol, hCx, hNCx'⟩

/-- A lag event for `step` under `dSemantics2`, assuming `PredStep i0` but `¬ PredStep i1`. -/
theorem lagEvent2_of_Pi0_notPi1
    (PredStep PredDim : Fin n → Prop)
    (hPos : PredStep (i0 n hn))
    (hNeg : ¬ PredStep (i1 n hn)) :
    LagEvent (P := DPrefix)
      (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
      (h := DPrefix.base) (k := DPrefix.mid) (k' := DPrefix.fut)
      (p := (DPath.p : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid))
      (q := (DPath.q : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid))
      α_pq
      (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) := by
  let x : FiberPt (P := DPrefix) (dObs (n := n)) dTargetObs DPrefix.base := dX (n := n) DPrefix.base (i0 n hn)
  let x' : FiberPt (P := DPrefix) (dObs (n := n)) dTargetObs DPrefix.base := dX (n := n) DPrefix.base (i1 n hn)
  have hxne : x ≠ x' := by
    intro hEq
    have : (i0 n hn) = (i1 n hn) := by
      have : x.1.hidden = x'.1.hidden := congrArg (fun z => z.1.hidden) hEq
      simpa [x, x'] using this
    exact (i0_ne_i1 n hn) this

  have hHol :
      HolonomyRel (P := DPrefix)
        (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
        α_pq x x' := by
    have hHolWitness :
        ∃ y : FiberPt (P := DPrefix) (dObs (n := n)) dTargetObs DPrefix.mid,
          Transport (P := DPrefix) (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
            (DPath.p : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid) x y ∧
          Transport (P := DPrefix) (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
            (DPath.q : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid) x' y := by
      refine ⟨dX (n := n) DPrefix.mid (i0 n hn), rfl, rfl⟩
    exact (PrimitiveHolonomy.holonomy_def
      (P := DPrefix)
      (sem := dSemantics2 (n := n) (hn := hn) PredStep PredDim)
      (obs := dObs (n := n))
      (target_obs := dTargetObs)
      (α := α_pq)
      (x := x) (x' := x')).2 hHolWitness

  have hCx :
      Compatible (P := DPrefix) (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
        (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) x := by
    have : PredStep x.1.hidden := by simpa [x] using hPos
    have hxCompat :
        Compatible (P := DPrefix) (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
          (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) x ↔ PredStep x.1.hidden :=
      compatible_step2_iff_hidden (n := n) (hn := hn) PredStep PredDim x
    exact (hxCompat.mpr this)

  have hNCx' :
      ¬ Compatible (P := DPrefix) (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
        (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) x' := by
    intro hx'
    have hxCompat :
        Compatible (P := DPrefix) (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
          (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) x' ↔ PredStep x'.1.hidden :=
      compatible_step2_iff_hidden (n := n) (hn := hn) PredStep PredDim x'
    have : PredStep x'.1.hidden := hxCompat.mp hx'
    have : PredStep (i1 n hn) := by simpa [x'] using this
    exact hNeg this

  exact ⟨x, x', hxne, hHol, hCx, hNCx'⟩

/-- Upper bound: compatibility along `step` is classified by `Fin n` via `hidden`. -/
theorem compatDimLe_step_n (Pred : Fin n → Prop) :
    CompatDimLe (P := DPrefix)
      (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
      (h := DPrefix.base) (k := DPrefix.fut)
      (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) n := by
  refine ⟨(fun x => x.1.hidden), Pred, ?_⟩
  intro x
  simpa using (compatible_step_iff_hidden (n := n) (hn := hn) Pred x)

/-- Upper bound: compatibility along `stepDim` is classified by `Fin n` via `hidden`. -/
theorem compatDimLe_stepDim_n (PredStep PredDim : Fin n → Prop) :
    CompatDimLe (P := DPrefix)
      (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
      (h := DPrefix.base) (k := DPrefix.fut)
      (DPath.stepDim : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) n := by
  refine ⟨(fun x => x.1.hidden), PredDim, ?_⟩
  intro x
  simpa using (compatible_stepDim_iff_hidden (n := n) (hn := hn) PredStep PredDim x)

/-- Pairwise separation hypothesis on `Pred : Fin n → Prop`. -/
def PairwisePropSeparated (Pred : Fin n → Prop) : Prop :=
  ∀ i j : Fin n, i ≠ j → ¬ (Pred i ↔ Pred j)

/-!
### Scope of the pairwise lower-bound hypothesis

The hypothesis `PairwisePropSeparated Pred` is a deliberately strong lower-bound device for a
dedicated quantitative branch: it lets the single-step predicate `Compatible ... step x : Prop`
force an exact `CompatDimEq ... step n` result by making all `n` finite classes propositionally
distinguishable.

This should not be read as the general form of an `n`-class mediator. A single fixed step carries
a binary truth value, while the broader mediator story may be distributed across a signature or
across a separate quantitative step. Accordingly, this file separates the qualitative lag/no-go
witness (`step`) from the dimensional exactness witness (`stepDim`) in
`profileDimSplit_step_stepDim_n_of_pairwisePropSeparated`.

The lemmas below record the boundary of the strong hypothesis: if one also asks for a concrete
binary split `Pred (i0 n hn)` and `¬ Pred (i1 n hn)`, then `PairwisePropSeparated Pred` cannot
hold once `n > 2`, because two indices outside the positive class would both be refutable and
hence propositionally equivalent.
-/

/-- A third canonical hidden value `i2 : Fin n` under `2 < n`, avoiding `OfNat` on `Fin`. -/
def i2 (h2n : 2 < n) : Fin n :=
  ⟨2, h2n⟩

theorem i0_ne_i2 (h2n : 2 < n) : i0 n hn ≠ i2 (n := n) h2n := by
  intro hEq
  have hval : (i0 n hn).val = (i2 (n := n) h2n).val := congrArg Fin.val hEq
  dsimp [i0, i2] at hval
  exact Nat.noConfusion hval

theorem i1_ne_i2 (h2n : 2 < n) : i1 n hn ≠ i2 (n := n) h2n := by
  intro hEq
  have hval : (i1 n hn).val = (i2 (n := n) h2n).val := congrArg Fin.val hEq
  dsimp [i1, i2] at hval
  have h01 : (0 : Nat) = 1 := by
    apply Nat.succ.inj
    exact hval
  exact Nat.zero_ne_one h01

theorem not_pairwisePropSeparated_of_Pred_i0_of_two_lt
    (h2n : 2 < n) (Pred : Fin n → Prop) (hPos : Pred (i0 n hn)) :
    ¬ PairwisePropSeparated (n := n) Pred := by
  intro hsep
  let j : Fin n := i1 n hn
  let k : Fin n := i2 (n := n) h2n
  have hjne : i0 n hn ≠ j := i0_ne_i1 n hn
  have hkne : i0 n hn ≠ k := i0_ne_i2 (n := n) (hn := hn) h2n
  have hjk : j ≠ k := i1_ne_i2 (n := n) (hn := hn) h2n

  have hNotj : ¬ Pred j := by
    intro hj
    have : Pred (i0 n hn) ↔ Pred j := ⟨(fun _ => hj), (fun _ => hPos)⟩
    exact hsep (i0 n hn) j hjne this

  have hNotk : ¬ Pred k := by
    intro hk
    have : Pred (i0 n hn) ↔ Pred k := ⟨(fun _ => hk), (fun _ => hPos)⟩
    exact hsep (i0 n hn) k hkne this

  have hIff : Pred j ↔ Pred k := by
    refine ⟨(fun hj => False.elim (hNotj hj)), (fun hk => False.elim (hNotk hk))⟩

  exact hsep j k hjk hIff

theorem not_exists_split_and_pairwisePropSeparated_Pred_of_two_lt (h2n : 2 < n) :
    ¬ ∃ Pred : Fin n → Prop,
        Pred (i0 n hn) ∧ ¬ Pred (i1 n hn) ∧ PairwisePropSeparated (n := n) Pred := by
  rintro ⟨Pred, hPos, _hNeg, hsep⟩
  exact (not_pairwisePropSeparated_of_Pred_i0_of_two_lt (n := n) (hn := hn) h2n Pred hPos) hsep

/-- Exactness: under `PairwisePropSeparated Pred`, the compatibility dimension is exactly `n`. -/
theorem compatDimEq_step_n_of_pairwisePropSeparated
    (Pred : Fin n → Prop) (hsep : PairwisePropSeparated (n := n) Pred) :
    CompatDimEq (P := DPrefix)
      (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
      (h := DPrefix.base) (k := DPrefix.fut)
      (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) n := by
  refine ⟨compatDimLe_step_n (n := n) (hn := hn) Pred, ?_⟩
  intro m hm
  -- Use the canonical witness family `i ↦ dX base i`.
  let x : Fin n → FiberPt (P := DPrefix) (dObs (n := n)) dTargetObs DPrefix.base :=
    fun i => dX (n := n) DPrefix.base i
  have hsepCompat :
      PairwiseCompatSeparated (P := DPrefix)
        (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
        (h := DPrefix.base) (k := DPrefix.fut)
        (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) x := by
    intro i j hij
    intro hCompat
    have : Pred i ↔ Pred j := by
      have hi :
          Compatible (P := DPrefix) (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
            (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) (x i) ↔ Pred i := by
        simpa using (compatible_step_iff_hidden (n := n) (hn := hn) Pred (x i))
      have hj :
          Compatible (P := DPrefix) (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
            (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) (x j) ↔ Pred j := by
        simpa using (compatible_step_iff_hidden (n := n) (hn := hn) Pred (x j))
      exact hi.symm.trans (hCompat.trans hj)
    exact hsep i j hij this

  exact
    PrimitiveHolonomy.not_compatDimLe_of_finite_witness_family
      (P := DPrefix)
      (sem := dSemantics (n := n) (hn := hn) Pred)
      (obs := dObs (n := n))
      (target_obs := dTargetObs)
      (step := (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut))
      (x := x)
      (hsep := hsepCompat)
      (hmn := hm)

/-- Exactness on `stepDim`: under `PairwisePropSeparated PredDim`, the dimension is exactly `n`. -/
theorem compatDimEq_stepDim_n_of_pairwisePropSeparated
    (PredStep PredDim : Fin n → Prop) (hsep : PairwisePropSeparated (n := n) PredDim) :
    CompatDimEq (P := DPrefix)
      (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
      (h := DPrefix.base) (k := DPrefix.fut)
      (DPath.stepDim : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) n := by
  refine ⟨compatDimLe_stepDim_n (n := n) (hn := hn) PredStep PredDim, ?_⟩
  intro m hm
  let x : Fin n → FiberPt (P := DPrefix) (dObs (n := n)) dTargetObs DPrefix.base :=
    fun i => dX (n := n) DPrefix.base i
  have hsepCompat :
      PairwiseCompatSeparated (P := DPrefix)
        (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
        (h := DPrefix.base) (k := DPrefix.fut)
        (DPath.stepDim : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) x := by
    intro i j hij
    intro hCompat
    have : PredDim i ↔ PredDim j := by
      have hi :
          Compatible (P := DPrefix)
              (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
              (DPath.stepDim : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) (x i) ↔
            PredDim i := by
        simpa using (compatible_stepDim_iff_hidden (n := n) (hn := hn) PredStep PredDim (x i))
      have hj :
          Compatible (P := DPrefix)
              (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
              (DPath.stepDim : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) (x j) ↔
            PredDim j := by
        simpa using (compatible_stepDim_iff_hidden (n := n) (hn := hn) PredStep PredDim (x j))
      exact hi.symm.trans (hCompat.trans hj)
    exact hsep i j hij this

  exact
    PrimitiveHolonomy.not_compatDimLe_of_finite_witness_family
      (P := DPrefix)
      (sem := dSemantics2 (n := n) (hn := hn) PredStep PredDim)
      (obs := dObs (n := n))
      (target_obs := dTargetObs)
      (step := (DPath.stepDim : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut))
      (x := x)
      (hsep := hsepCompat)
      (hmn := hm)

/--
A compact package: under `Pred i0` and `¬ Pred i1`, we obtain a `DiagonalDynamicClass` for the
cell `(p ⇒ q)` and the future step `step`.
-/
theorem diagonalDynamicClass_of_Pi0_notPi1
    (Pred : Fin n → Prop)
    (hPos : Pred (i0 n hn))
    (hNeg : ¬ Pred (i1 n hn)) :
    DiagonalDynamicClass (P := DPrefix)
      (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
      (h := DPrefix.base) (k := DPrefix.mid) (k' := DPrefix.fut)
      (p := (DPath.p : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid))
      (q := (DPath.q : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid))
      α_pq
      (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) := by
  have hTw :
      TwistedHolonomy (P := DPrefix)
        (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
        α_pq :=
    twistedHolonomy_pq (n := n) (hn := hn) Pred

  have hLag :
      LagEvent (P := DPrefix)
        (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
        α_pq
        (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) :=
    lagEvent_of_Pi0_notPi1 (n := n) (hn := hn) Pred hPos hNeg

  have hNoVis :
      ¬ VisiblePredictsStep (P := DPrefix)
        (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
        (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) := by
    exact not_visiblePredictsStep_of_lagEvent (P := DPrefix)
      (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
      (α := α_pq)
      (step := (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut))
      hLag

  refine ⟨hTw, hLag, hNoVis, ?_, ?_⟩
  · exact
      obstructionWrt_singleton_of_twistedHolonomy_of_gaugeRefl
        (P := DPrefix)
        (sem := dSemantics (n := n) (hn := hn) Pred)
        (obs := dObs (n := n))
        (target_obs := dTargetObs)
        (α := α_pq)
        hTw
  · exact
      not_autoRegulatedWrt_singleton_of_twistedHolonomy_of_gaugeRefl
        (P := DPrefix)
        (sem := dSemantics (n := n) (hn := hn) Pred)
        (obs := dObs (n := n))
        (target_obs := dTargetObs)
        (α := α_pq)
        hTw

/--
Same conclusion as `diagonalDynamicClass_of_Pi0_notPi1`, but for `dSemantics2`.
The `stepDim` branch does not interfere with the `(p ⇒ q)` cell nor the `step` lag witness.
-/
theorem diagonalDynamicClass2_of_Pi0_notPi1
    (PredStep PredDim : Fin n → Prop)
    (hPos : PredStep (i0 n hn))
    (hNeg : ¬ PredStep (i1 n hn)) :
    DiagonalDynamicClass (P := DPrefix)
      (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
      (h := DPrefix.base) (k := DPrefix.mid) (k' := DPrefix.fut)
      (p := (DPath.p : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid))
      (q := (DPath.q : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.mid))
      α_pq
      (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) := by
  have hTw :
      TwistedHolonomy (P := DPrefix)
        (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
        α_pq :=
    twistedHolonomy_pq2 (n := n) (hn := hn) PredStep PredDim

  have hLag :
      LagEvent (P := DPrefix)
        (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
        α_pq
        (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) :=
    lagEvent2_of_Pi0_notPi1 (n := n) (hn := hn) PredStep PredDim hPos hNeg

  have hNoVis :
      ¬ VisiblePredictsStep (P := DPrefix)
        (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
        (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) := by
    exact not_visiblePredictsStep_of_lagEvent (P := DPrefix)
      (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
      (α := α_pq)
      (step := (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut))
      hLag

  refine ⟨hTw, hLag, hNoVis, ?_, ?_⟩
  · exact
      obstructionWrt_singleton_of_twistedHolonomy_of_gaugeRefl
        (P := DPrefix)
        (sem := dSemantics2 (n := n) (hn := hn) PredStep PredDim)
        (obs := dObs (n := n))
        (target_obs := dTargetObs)
        (α := α_pq)
        hTw
  · exact
      not_autoRegulatedWrt_singleton_of_twistedHolonomy_of_gaugeRefl
        (P := DPrefix)
        (sem := dSemantics2 (n := n) (hn := hn) PredStep PredDim)
        (obs := dObs (n := n))
        (target_obs := dTargetObs)
        (α := α_pq)
        hTw

/-- The dynamic cell `(p ⇒ q)` as a `Cell`. -/
def cell_pq : Cell (P := DPrefix) :=
  ⟨DPrefix.base, DPrefix.mid, DPath.p, DPath.q, ⟨α_pq⟩⟩

/-- A `DynamicNoGoProfile` for the cell `(p ⇒ q)` and the future step `step`. -/
theorem profile_of_Pi0_notPi1
    (Pred : Fin n → Prop)
    (hPos : Pred (i0 n hn))
    (hNeg : ¬ Pred (i1 n hn)) :
    DynamicNoGoProfile (P := DPrefix)
      (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
      (cell_pq)
      (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) := by
  dsimp [DynamicNoGoProfile, cell_pq]
  have hTw :
      TwistedHolonomy (P := DPrefix)
        (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
        α_pq :=
    twistedHolonomy_pq (n := n) (hn := hn) Pred
  have hLag :
      LagEvent (P := DPrefix)
        (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
        α_pq
        (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) :=
    lagEvent_of_Pi0_notPi1 (n := n) (hn := hn) Pred hPos hNeg
  have hNoVis :
      ¬ VisiblePredictsStep (P := DPrefix)
        (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
        (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) := by
    exact not_visiblePredictsStep_of_lagEvent (P := DPrefix)
      (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
      (α := α_pq)
      (step := (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut))
      hLag
  have hNotAuto :
      ¬ AutoRegulatedWrt (P := DPrefix)
        (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
        (fun φ => GaugeRefl (P := DPrefix) (dObs (n := n)) dTargetObs φ)
        (Set.singleton (⟨DPrefix.base, DPrefix.mid, DPath.p, DPath.q, ⟨α_pq⟩⟩ : Cell (P := DPrefix))) :=
    not_autoRegulatedWrt_singleton_of_twistedHolonomy_of_gaugeRefl
      (P := DPrefix)
      (sem := dSemantics (n := n) (hn := hn) Pred)
      (obs := dObs (n := n))
      (target_obs := dTargetObs)
      (α := α_pq)
      hTw
  exact ⟨hTw, hLag, hNoVis, hNotAuto⟩

/--
Same `DynamicNoGoProfile` as `profile_of_Pi0_notPi1`, but for `dSemantics2`.
This closes the qualitative profile on `step` while leaving `stepDim` free for quantitative work.
-/
theorem profile2_of_Pi0_notPi1
    (PredStep PredDim : Fin n → Prop)
    (hPos : PredStep (i0 n hn))
    (hNeg : ¬ PredStep (i1 n hn)) :
    DynamicNoGoProfile (P := DPrefix)
      (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
      (cell_pq)
      (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) := by
  dsimp [DynamicNoGoProfile, cell_pq]
  have hTw :
      TwistedHolonomy (P := DPrefix)
        (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
        α_pq :=
    twistedHolonomy_pq2 (n := n) (hn := hn) PredStep PredDim
  have hLag :
      LagEvent (P := DPrefix)
        (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
        α_pq
        (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) :=
    lagEvent2_of_Pi0_notPi1 (n := n) (hn := hn) PredStep PredDim hPos hNeg
  have hNoVis :
      ¬ VisiblePredictsStep (P := DPrefix)
        (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
        (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut) := by
    exact not_visiblePredictsStep_of_lagEvent (P := DPrefix)
      (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
      (α := α_pq)
      (step := (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut))
      hLag
  have hNotAuto :
      ¬ AutoRegulatedWrt (P := DPrefix)
        (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
        (fun φ => GaugeRefl (P := DPrefix) (dObs (n := n)) dTargetObs φ)
        (Set.singleton (⟨DPrefix.base, DPrefix.mid, DPath.p, DPath.q, ⟨α_pq⟩⟩ : Cell (P := DPrefix))) :=
    not_autoRegulatedWrt_singleton_of_twistedHolonomy_of_gaugeRefl
      (P := DPrefix)
      (sem := dSemantics2 (n := n) (hn := hn) PredStep PredDim)
      (obs := dObs (n := n))
      (target_obs := dTargetObs)
      (α := α_pq)
      hTw
  exact ⟨hTw, hLag, hNoVis, hNotAuto⟩

/-- Same profile plus the quantitative claim `CompatDimEq … step n`. -/
theorem profileDim_step_n_of_pairwisePropSeparated
    (Pred : Fin n → Prop)
    (hPos : Pred (i0 n hn))
    (hNeg : ¬ Pred (i1 n hn))
    (hsep : PairwisePropSeparated (n := n) Pred) :
    DynamicNoGoProfileDim (P := DPrefix)
      (dSemantics (n := n) (hn := hn) Pred) (dObs (n := n)) dTargetObs
      (cell_pq)
      (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut)
      n := by
  refine ⟨profile_of_Pi0_notPi1 (n := n) (hn := hn) Pred hPos hNeg, ?_⟩
  exact
    compatDimEq_step_n_of_pairwisePropSeparated (n := n) (hn := hn) Pred hsep

/--
Split package (usable for all `n > 1`):

- `step` carries the qualitative no-go profile under `PredStep i0` and `¬ PredStep i1`;
- `stepDim` carries the quantitative exactness `CompatDimEq … stepDim n` under a separate
  `PairwisePropSeparated PredDim` hypothesis.

This is the file's main non-vacuity bridge to the independence/mediation chain: it exhibits a
concrete parametric family where the abstract exact finite mediator assumption `CompatDimEq … n`
is realized constructively.
-/
theorem profileDimSplit_step_stepDim_n_of_pairwisePropSeparated
    (PredStep PredDim : Fin n → Prop)
    (hPos : PredStep (i0 n hn))
    (hNeg : ¬ PredStep (i1 n hn))
    (hsep : PairwisePropSeparated (n := n) PredDim) :
    DynamicNoGoProfile (P := DPrefix)
        (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
        (cell_pq)
        (DPath.step : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut)
      ∧
      CompatDimEq (P := DPrefix)
        (dSemantics2 (n := n) (hn := hn) PredStep PredDim) (dObs (n := n)) dTargetObs
        (h := DPrefix.base) (k := DPrefix.fut)
        (DPath.stepDim : HistoryGraph.Path (P := DPrefix) DPrefix.base DPrefix.fut)
        n := by
  refine ⟨profile2_of_Pi0_notPi1 (n := n) (hn := hn) PredStep PredDim hPos hNeg, ?_⟩
  exact
    compatDimEq_stepDim_n_of_pairwisePropSeparated (n := n) (hn := hn) PredStep PredDim hsep

end

end DynamicCompatDimN
end Examples
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
Constructive gate: the declarations below must not depend on any axioms, `Classical`, `propext`,
or other forbidden principles.
-/
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.DPrefix
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.DPath
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.dComp
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.α_pq
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.DState
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.dObs
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.dTargetObs
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.i0
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.i1
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.i0_ne_i1
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.dRel2
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.dRel
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.dRel2_comp
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.dRel_comp
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.dSemantics
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.dSemantics2
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.dX
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.compatible_step_iff_hidden
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.compatible_stepDim_iff_hidden
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.compatible_step2_iff_hidden
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.twistedHolonomy_pq
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.twistedHolonomy_pq2
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.lagEvent_of_Pi0_notPi1
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.lagEvent2_of_Pi0_notPi1
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.compatDimLe_step_n
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.compatDimLe_stepDim_n
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.PairwisePropSeparated
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.i2
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.i0_ne_i2
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.i1_ne_i2
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.not_pairwisePropSeparated_of_Pred_i0_of_two_lt
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.not_exists_split_and_pairwisePropSeparated_Pred_of_two_lt
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.compatDimEq_step_n_of_pairwisePropSeparated
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.compatDimEq_stepDim_n_of_pairwisePropSeparated
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.diagonalDynamicClass_of_Pi0_notPi1
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.diagonalDynamicClass2_of_Pi0_notPi1
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.cell_pq
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.profile_of_Pi0_notPi1
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.profile2_of_Pi0_notPi1
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.profileDim_step_n_of_pairwisePropSeparated
#print axioms PrimitiveHolonomy.Examples.DynamicCompatDimN.profileDimSplit_step_stepDim_n_of_pairwisePropSeparated
/- AXIOM_AUDIT_END -/
