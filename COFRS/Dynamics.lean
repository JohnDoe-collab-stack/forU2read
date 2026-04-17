import COFRS.Foundations
import COFRS.Combinatorics.FinCompression

/-!
# Primitive Holonomy: Dynamics

This module contains the lag/compatibility layer and the minimal information-theoretic
interfaces (visible predictors, compatibility dimension).
-/

universe u v w uQ

namespace PrimitiveHolonomy

variable {P : Type u}

section WithHistoryGraph

variable [HistoryGraph P]


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

/-- The canonical mediator type at `h`: a predicate on all dependent future steps. -/
abbrev CanonicalMediator (h : P) : Type _ :=
  Future h → Prop

/-- Compatibility along a dependent future step. -/
def CompatibleFuture {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h : P} (step : Future (P := P) h) (x : FiberPt (P := P) obs target_obs h) : Prop :=
  Compatible sem obs target_obs step.2 x

/-- Full compatibility signature: for each future step, whether `x` remains compatible. -/
def Sig {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h : P} (x : FiberPt (P := P) obs target_obs h) : Future (P := P) h → Prop :=
  fun step => CompatibleFuture (P := P) sem obs target_obs step x

/-- Name the canonical mediator map explicitly (it is just `Sig`). -/
abbrev canonicalMediator
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h : P} (x : FiberPt (P := P) obs target_obs h) :
    CanonicalMediator (h := h) :=
  Sig (P := P) sem obs target_obs x

/-- Restrict the full signature `Sig` to an indexed family of future steps. -/
def SigFam {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h : P} {F : Type v} (ι : F → Future (P := P) h)
    (x : FiberPt (P := P) obs target_obs h) : F → Prop :=
  fun f => Sig (P := P) sem obs target_obs x (ι f)

/-- Convert equality of propositions into an iff (axiom-free). -/
theorem iff_of_eq {P Q : Prop} (h : P = Q) : P ↔ Q := by
  cases h
  exact Iff.rfl

theorem sigFam_iff_of_summary_correct
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h : P} {F : Type v} (ι : F → Future (P := P) h)
    {Q : Type uQ} (σ : FiberPt (P := P) obs target_obs h → Q)
    (pred : Q → F → Prop)
    (Hcorr : ∀ x f, pred (σ x) f ↔ SigFam (P := P) sem obs target_obs ι x f)
    {x x' : FiberPt (P := P) obs target_obs h}
    (hσ : σ x = σ x') :
    ∀ f, SigFam (P := P) sem obs target_obs ι x f ↔ SigFam (P := P) sem obs target_obs ι x' f :=
by
  intro f
  have hx : pred (σ x) f ↔ pred (σ x') f :=
    iff_of_eq (congrArg (fun q => pred q f) hσ)
  exact (Hcorr x f).symm.trans (hx.trans (Hcorr x' f))

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
  have hx : pred (σ x) step ↔ pred (σ x') step :=
    iff_of_eq (congrArg (fun q => pred q step) hσ)
  exact (Hcorr x step).symm.trans (hx.trans (Hcorr x' step))

/--
Full-signature factorization: a summary `σ` respects the canonical signature `Sig`
if equal summaries imply equal signatures on every future step.
-/
def SigFactorsThrough
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h : P} {Q : Type uQ} (σ : FiberPt (P := P) obs target_obs h → Q) : Prop :=
  ∀ {x x' : FiberPt (P := P) obs target_obs h},
    σ x = σ x' →
      ∀ step, Sig (P := P) sem obs target_obs x step ↔ Sig (P := P) sem obs target_obs x' step

theorem sigFactorsThrough_of_summary_correct
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h : P}
    {Q : Type uQ} (σ : FiberPt (P := P) obs target_obs h → Q)
    (pred : Q → Future (P := P) h → Prop)
    (Hcorr : ∀ x step, pred (σ x) step ↔ CompatibleFuture (P := P) sem obs target_obs step x) :
    SigFactorsThrough (P := P) sem obs target_obs σ := by
  intro x x' hσ
  exact sig_iff_of_summary_correct (P := P) sem obs target_obs σ pred Hcorr hσ

/--
Finite *global* compression of the canonical mediator `Sig`:
there is a finite summary with `n` values that predicts compatibility for **every** future step.

This is strictly stronger than step-local `CompatDimLe … step n`, which only predicts compatibility
for a single fixed `step`.
-/
def CompatSigDimLe
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h : P} (n : Nat) : Prop :=
  ∃ (σ : FiberPt (P := P) obs target_obs h → Fin n)
      (pred : Fin n → Future (P := P) h → Prop),
    ∀ x step, pred (σ x) step ↔ CompatibleFuture (P := P) sem obs target_obs step x

/--
Exact global signature dimension `n`: globally compressible into `Fin n`,
and not globally compressible into any strict smaller `m < n`.
-/
def CompatSigDimEq
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h : P} (n : Nat) : Prop :=
  CompatSigDimLe (P := P) sem obs target_obs (h := h) n ∧
    ∀ m : Nat, m < n → ¬ CompatSigDimLe (P := P) sem obs target_obs (h := h) m

theorem sigFactorsThrough_of_compatSigDimLe
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h : P} {n : Nat} :
    CompatSigDimLe (P := P) sem obs target_obs (h := h) n →
      ∃ σ : FiberPt (P := P) obs target_obs h → Fin n,
        SigFactorsThrough (P := P) sem obs target_obs σ :=
by
  rintro ⟨σ, pred, Hcorr⟩
  refine ⟨σ, ?_⟩
  exact sigFactorsThrough_of_summary_correct (P := P) sem obs target_obs σ pred Hcorr

/-- A finite summary that respects `Sig` yields a global `CompatSigDimLe` witness. -/
theorem compatSigDimLe_of_sigFactorsThrough
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h : P} {n : Nat}
    (σ : FiberPt (P := P) obs target_obs h → Fin n)
    (hσ : SigFactorsThrough (P := P) sem obs target_obs σ) :
    CompatSigDimLe (P := P) sem obs target_obs (h := h) n :=
by
  let pred : Fin n → Future (P := P) h → Prop :=
    fun i step =>
      ∃ x' : FiberPt (P := P) obs target_obs h,
        σ x' = i ∧ CompatibleFuture (P := P) sem obs target_obs step x'
  refine ⟨σ, pred, ?_⟩
  intro x step
  constructor
  · rintro ⟨x', hx', hxCompat⟩
    have hEq : σ x' = σ x := hx'.trans rfl
    have hSig :
        Sig (P := P) sem obs target_obs x' step ↔ Sig (P := P) sem obs target_obs x step :=
      (hσ (x := x') (x' := x) hEq) step
    -- `Sig … step` is definitionaly `CompatibleFuture … step …`
    exact (hSig.mp hxCompat)
  · intro hxCompat
    exact ⟨x, rfl, hxCompat⟩

/--
Global finite compression of `Sig` is equivalent to the existence of a finite summary that
respects `Sig` (in the sense of `SigFactorsThrough`).
-/
theorem compatSigDimLe_iff_exists_sigFactorsThrough
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h : P} (n : Nat) :
    CompatSigDimLe (P := P) sem obs target_obs (h := h) n ↔
      ∃ σ : FiberPt (P := P) obs target_obs h → Fin n,
        SigFactorsThrough (P := P) sem obs target_obs σ :=
by
  constructor
  · intro hSig
    exact sigFactorsThrough_of_compatSigDimLe (P := P) sem obs target_obs (h := h) (n := n) hSig
  · rintro ⟨σ, hσ⟩
    exact compatSigDimLe_of_sigFactorsThrough (P := P) sem obs target_obs (h := h) (n := n) σ hσ

/-- Monotonicity: if `CompatSigDimLe … m` and `m ≤ n`, then `CompatSigDimLe … n`. -/
theorem compatSigDimLe_mono
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h : P} {m n : Nat} (hmn : m ≤ n) :
    CompatSigDimLe (P := P) sem obs target_obs (h := h) m →
      CompatSigDimLe (P := P) sem obs target_obs (h := h) n := by
  rintro ⟨σ, pred, Hcorr⟩
  let emb : Fin m → Fin n := PrimitiveHolonomy.Combinatorics.finEmbed hmn
  let σ' : FiberPt (P := P) obs target_obs h → Fin n := fun x => emb (σ x)
  let pred' : Fin n → Future (P := P) h → Prop :=
    fun i step => ∃ j : Fin m, emb j = i ∧ pred j step
  refine ⟨σ', pred', ?_⟩
  intro x step
  constructor
  · rintro ⟨j, hj, hjPred⟩
    have : j = σ x := by
      apply PrimitiveHolonomy.Combinatorics.finEmbed_injective hmn
      simpa [σ'] using hj
    subst this
    exact (Hcorr x step).1 hjPred
  · intro hxCompat
    have : pred (σ x) step := (Hcorr x step).2 hxCompat
    refine ⟨σ x, rfl, this⟩

/--
Exactness packaging: `CompatSigDimEq … n` yields a finite summary `σ : fiber → Fin n`
that respects `Sig`, together with the minimality statement expressed directly on summaries.
-/
theorem exists_sigFactorsThrough_of_compatSigDimEq
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h : P} {n : Nat} :
    CompatSigDimEq (P := P) sem obs target_obs (h := h) n →
      ∃ σ : FiberPt (P := P) obs target_obs h → Fin n,
        SigFactorsThrough (P := P) sem obs target_obs σ
        ∧ ∀ m : Nat, m < n →
            ¬ (∃ σm : FiberPt (P := P) obs target_obs h → Fin m,
                SigFactorsThrough (P := P) sem obs target_obs σm) := by
  rintro ⟨hLe, hMin⟩
  rcases sigFactorsThrough_of_compatSigDimLe (P := P) sem obs target_obs (h := h) (n := n) hLe with
    ⟨σ, hσ⟩
  refine ⟨σ, hσ, ?_⟩
  intro m hm
  rintro ⟨σm, hσm⟩
  have hLe_m :
      CompatSigDimLe (P := P) sem obs target_obs (h := h) m :=
    compatSigDimLe_of_sigFactorsThrough (P := P) sem obs target_obs (h := h) (n := m) σm hσm
  exact (hMin m hm) hLe_m

/-- Exact global dimension `2` (alias for readability). -/
abbrev CompatSigDimEqTwo
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h : P} : Prop :=
  CompatSigDimEq (P := P) sem obs target_obs (h := h) 2

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
    have h := hsig step
    dsimp [Sig, CompatibleFuture, CompatibleFuture] at h
    exact h
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



/-!
### 5.2 Compression / prediction (visible summaries)

This is the minimal interface needed to turn a *dynamic separation* (like `LagEvent`) into an
impossibility of predicting future compatibility from purely visible data.

Key point: any `σ` that factors through `obs` is constant on each fiber.
-/

/-- A step separates the current fiber if it is compatible with one micro-state but not another. -/
def StepSeparatesFiber {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) : Prop :=
  ∃ x x' : FiberPt obs target_obs h,
    x ≠ x' ∧ Compatible sem obs target_obs step x ∧
      ¬ Compatible sem obs target_obs step x'

/-- A *visible* predictor for compatibility with a fixed future step (σ factors through `obs`). -/
def VisiblePredictsStep {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) : Prop :=
  ∃ (Q : Type w)
    (σ : FiberPt obs target_obs h → Q)
    (pred : Q → Prop),
      (∃ f : V → Q, ∀ x, σ x = f (obs x.1)) ∧
      ∀ x : FiberPt obs target_obs h,
        Compatible sem obs target_obs step x ↔ pred (σ x)

/-- The strongest form: the.1 visible observation `obs x` itself predicts compatibility. -/
def ObsPredictsStep {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) : Prop :=
  ∃ pred : V → Prop,
    ∀ x : FiberPt obs target_obs h,
      Compatible sem obs target_obs step x ↔ pred (obs x.1)



/--
Visible compatibility dimension: `Compatible step x` can be predicted from a finite summary with `n` values,
and this summary factors through `obs`.

This is the quantitative.1 version of `VisiblePredictsStep` with codomain `Fin n`.
-/
def VisibleCompatDimLe {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) : Prop :=
  ∃ (σ : FiberPt obs target_obs h → Fin n) (pred : Fin n → Prop),
    (∃ f : V → Fin n, ∀ x, σ x = f (obs x.1)) ∧
    ∀ x : FiberPt obs target_obs h,
      Compatible sem obs target_obs step x ↔ pred (σ x)

/-- Any visible finite-class predictor is a visible predictor (in the `VisiblePredictsStep` sense). -/
theorem visiblePredictsStep_of_visibleCompatDimLe
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) :
    VisibleCompatDimLe (P := P) sem obs target_obs step n →
      VisiblePredictsStep (P := P) sem obs target_obs step := by
  rintro ⟨σ, pred, hσ, hcorr⟩
  refine ⟨ULift.{w, 0} (Fin n), (fun x => ULift.up.{w, 0} (σ x)), (fun q => pred q.down), ?_, ?_⟩
  · rcases hσ with ⟨f, hf⟩
    refine ⟨(fun v => ULift.up.{w, 0} (f v)), ?_⟩
    intro x
    exact congrArg (fun i => ULift.up.{w, 0} i) (hf x)
  · intro x
    exact hcorr x


/-!
### 5.3 Invariance under re-labeling of observables

The statements `VisiblePredictsStep`, `VisibleCompatDimLe`, and `CompatDimLe` should not depend on the
*names* of observable.1 values, only on the induced fibers.

If we postcompose both `obs : S → V` and `target_obs : P → V` by an equivalence `e : V ≃ V'`, the fiber
types are canonically equivalent, and all the prediction/dimension notions transfer.
-/

section ObservableEquiv

variable {S : Type w} {V V' : Type w}

def obsPost (e : Equiv V V') (obs : S → V) : S → V' :=
  fun s => e.toFun (obs s)

def targetObsPost (e : Equiv V V') (target_obs : P → V) : P → V' :=
  fun h => e.toFun (target_obs h)

/-- Map a fiber point along a postcomposition equivalence of observables. -/
def fiberPtPostMap (e : Equiv V V') (obs : S → V) (target_obs : P → V) {h : P} :
    FiberPt obs target_obs h →
      FiberPt (obsPost e obs) (targetObsPost e target_obs) h :=
  fun x =>
    ⟨x.1, by
      -- `x.2 : obs x = target_obs h`
      exact congrArg e.toFun x.2⟩

/-- Inverse map a fiber point along a postcomposition equivalence of observables. -/
def fiberPtPostMapInv (e : Equiv V V') (obs : S → V) (target_obs : P → V) {h : P} :
    FiberPt (obsPost e obs) (targetObsPost e target_obs) h →
      FiberPt obs target_obs h :=
  fun x =>
    ⟨x.1, by
      -- Unfold the fiber membership and cancel the postcomposition via `invFun`.
      change obs x.1 = target_obs h
      have hxEq := x.2
      dsimp [Fiber] at hxEq
      dsimp [obsPost, targetObsPost] at hxEq
      have hxInv : e.invFun (e.toFun (obs x.1)) = e.invFun (e.toFun (target_obs h)) :=
        congrArg e.invFun hxEq
      have hxL : e.invFun (e.toFun (obs x.1)) = obs x.1 :=
        e.left_inv (obs x.1)
      have hxR : e.invFun (e.toFun (target_obs h)) = target_obs h :=
        e.left_inv (target_obs h)
      exact hxL.symm.trans (hxInv.trans hxR)⟩

theorem compatible_congr_postObsEquiv
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (e : Equiv V V') {h k : P} (step : HistoryGraph.Path h k)
    (x : FiberPt obs target_obs h) :
    Compatible sem obs target_obs step x ↔
      Compatible sem (obsPost e obs) (targetObsPost e target_obs) step
        (fiberPtPostMap e obs target_obs x) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨fiberPtPostMap e obs target_obs y, ?_⟩
    exact hy
  · rintro ⟨y, hy⟩
    refine ⟨fiberPtPostMapInv e obs target_obs y, ?_⟩
    exact hy

theorem compatible_congr_postObsEquiv_inv
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (e : Equiv V V') {h k : P} (step : HistoryGraph.Path h k)
    (x : FiberPt (obsPost e obs) (targetObsPost e target_obs) h) :
    Compatible sem (obsPost e obs) (targetObsPost e target_obs) step x ↔
      Compatible sem obs target_obs step (fiberPtPostMapInv e obs target_obs x) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨fiberPtPostMapInv e obs target_obs y, ?_⟩
    exact hy
  · rintro ⟨y, hy⟩
    refine ⟨fiberPtPostMap e obs target_obs y, ?_⟩
    exact hy

theorem visiblePredictsStep_congr_postObsEquiv
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (e : Equiv V V') {h k : P} (step : HistoryGraph.Path h k) :
    VisiblePredictsStep sem obs target_obs step ↔
      VisiblePredictsStep sem (obsPost e obs) (targetObsPost e target_obs) step := by
  constructor
  · rintro ⟨Q, σ, pred, hσ, hcorr⟩
    rcases hσ with ⟨f, hf⟩
    refine ⟨Q, (fun x => σ (fiberPtPostMapInv e obs target_obs x)), pred, ?_, ?_⟩
    · refine ⟨(fun v' => f (e.invFun v')), ?_⟩
      intro x
      have hx : σ (fiberPtPostMapInv e obs target_obs x) = f (obs x.1) :=
        hf (fiberPtPostMapInv e obs target_obs x)
      show σ (fiberPtPostMapInv e obs target_obs x) = f (e.invFun (obsPost e obs x.1))
      rw [obsPost, show e.invFun ((@Equiv.toFun V V' e) (obs x.1)) = obs x.1 from e.left_inv (obs x.1)]
      exact hx
    · intro x
      have hx : Compatible sem obs target_obs step (fiberPtPostMapInv e obs target_obs x) ↔
          pred (σ (fiberPtPostMapInv e obs target_obs x)) :=
        hcorr (fiberPtPostMapInv e obs target_obs x)
      have hC :
          Compatible sem (obsPost e obs) (targetObsPost e target_obs) step x ↔
            Compatible sem obs target_obs step (fiberPtPostMapInv e obs target_obs x) :=
        compatible_congr_postObsEquiv_inv sem obs target_obs e step x
      exact hC.trans hx
  · rintro ⟨Q, σ, pred, hσ, hcorr⟩
    rcases hσ with ⟨f, hf⟩
    refine ⟨Q, (fun x => σ (fiberPtPostMap e obs target_obs x)), pred, ?_, ?_⟩
    · refine ⟨(fun v => f ((@Equiv.toFun V V' e) v)), ?_⟩
      intro x
      exact hf (fiberPtPostMap e obs target_obs x)
    · intro x
      have hx : Compatible sem (obsPost e obs) (targetObsPost e target_obs) step
            (fiberPtPostMap e obs target_obs x) ↔
          pred (σ (fiberPtPostMap e obs target_obs x)) :=
        hcorr (fiberPtPostMap e obs target_obs x)
      have hC :
          Compatible sem obs target_obs step x ↔
            Compatible sem (obsPost e obs) (targetObsPost e target_obs) step
              (fiberPtPostMap e obs target_obs x) :=
        compatible_congr_postObsEquiv sem obs target_obs e step x
      exact hC.trans hx

theorem visibleCompatDimLe_congr_postObsEquiv
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (e : Equiv V V') {h k : P} (step : HistoryGraph.Path h k) (n : Nat) :
    VisibleCompatDimLe sem obs target_obs step n ↔
      VisibleCompatDimLe sem (obsPost e obs) (targetObsPost e target_obs) step n := by
  constructor
  · rintro ⟨σ, pred, hσ, hcorr⟩
    rcases hσ with ⟨f, hf⟩
    refine ⟨(fun x => σ (fiberPtPostMapInv e obs target_obs x)), pred, ?_, ?_⟩
    · refine ⟨(fun v' => f (e.invFun v')), ?_⟩
      intro x
      have hx : σ (fiberPtPostMapInv e obs target_obs x) = f (obs x.1) :=
        hf (fiberPtPostMapInv e obs target_obs x)
      show σ (fiberPtPostMapInv e obs target_obs x) = f (e.invFun (obsPost e obs x.1))
      rw [obsPost, show e.invFun ((@Equiv.toFun V V' e) (obs x.1)) = obs x.1 from e.left_inv (obs x.1)]
      exact hx
    · intro x
      have hx : Compatible sem obs target_obs step (fiberPtPostMapInv e obs target_obs x) ↔
          pred (σ (fiberPtPostMapInv e obs target_obs x)) :=
        hcorr (fiberPtPostMapInv e obs target_obs x)
      have hC :
          Compatible sem (obsPost e obs) (targetObsPost e target_obs) step x ↔
            Compatible sem obs target_obs step (fiberPtPostMapInv e obs target_obs x) :=
        compatible_congr_postObsEquiv_inv sem obs target_obs e step x
      exact hC.trans hx
  · rintro ⟨σ, pred, hσ, hcorr⟩
    rcases hσ with ⟨f, hf⟩
    refine ⟨(fun x => σ (fiberPtPostMap e obs target_obs x)), pred, ?_, ?_⟩
    · refine ⟨(fun v => f ((@Equiv.toFun V V' e) v)), ?_⟩
      intro x
      exact hf (fiberPtPostMap e obs target_obs x)
    · intro x
      have hx : Compatible sem (obsPost e obs) (targetObsPost e target_obs) step
            (fiberPtPostMap e obs target_obs x) ↔
          pred (σ (fiberPtPostMap e obs target_obs x)) :=
        hcorr (fiberPtPostMap e obs target_obs x)
      have hC :
          Compatible sem obs target_obs step x ↔
            Compatible sem (obsPost e obs) (targetObsPost e target_obs) step
              (fiberPtPostMap e obs target_obs x) :=
        compatible_congr_postObsEquiv sem obs target_obs e step x
      exact hC.trans hx

end ObservableEquiv




/--
Compatibility dimension: `Compatible step x` can be predicted from a finite summary with `n` values.

This is *not* required to factor through `obs`; it measures how much hidden information is needed.
-/
def CompatDimLe {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) : Prop :=
  ∃ (σ : FiberPt obs target_obs h → Fin n) (pred : Fin n → Prop),
    ∀ x : FiberPt obs target_obs h,
      Compatible sem obs target_obs step x ↔ pred (σ x)

/-- `extObs` refines `obs` on the fiber over `h` if `obs` factors through `extObs`. -/
def RefinesOnFiber
    {S V : Type w} (obs : S → V) (target_obs : P → V) (h : P)
    {W : Type w} (extObs : FiberPt (P := P) obs target_obs h → W) : Prop :=
  ∃ π : W → V, ∀ x, obs x.1 = π (extObs x)

/-- Compatibility along `step` factors through an observable on the fiber over `h`. -/
def CompatFactorsThrough
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k)
    {W : Type w} (extObs : FiberPt (P := P) obs target_obs h → W) : Prop :=
  ∃ pred : W → Prop, ∀ x, Compatible (P := P) sem obs target_obs step x ↔ pred (extObs x)

/--
A **canonical finite refining lift** on the observable fiber over `h` for a step `step`.

The key point is that compatibility depends only on the *finite supplement* `Fin n`,
while `V` is retained only to witness the refinement of the visible interface.
-/
structure RefiningLiftData
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (h : P) {k : P} (step : HistoryGraph.Path h k) (n : Nat) : Type w where
  extObs : FiberPt (P := P) obs target_obs h → V × Fin n
  refines_fst : ∀ x, obs x.1 = (extObs x).1
  predFin : Fin n → Prop
  factors : ∀ x, Compatible (P := P) sem obs target_obs step x ↔ predFin ((extObs x).2)

/-- `RefiningLiftData` always yields a `RefinesOnFiber` witness (projection to `V` is `Prod.fst`). -/
theorem refiningLiftData_refinesOnFiber
    {S V : Type w} {sem : Semantics P S} {obs : S → V} {target_obs : P → V}
    {h : P} {k : P} {step : HistoryGraph.Path h k} {n : Nat}
    (L : RefiningLiftData (P := P) sem obs target_obs h step n) :
    RefinesOnFiber (P := P) obs target_obs h L.extObs := by
  refine ⟨Prod.fst, ?_⟩
  intro x
  simpa using (L.refines_fst x)

/-- Existence of a refining lift on the fiber (as a `Prop`). -/
abbrev RefiningLift
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (h : P) {k : P} (step : HistoryGraph.Path h k) (n : Nat) : Prop :=
  Nonempty (RefiningLiftData (P := P) sem obs target_obs h step n)

/-- Alias emphasizing that the lift is defined **on the observable fiber over `h`**. -/
abbrev RefiningLiftOnFiber
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (h : P) {k : P} (step : HistoryGraph.Path h k) (n : Nat) : Prop :=
  RefiningLift (P := P) sem obs target_obs h step n

/--
From an internal finite classifier (`CompatDimLe … n`), we can build an explicit *refining* lift
`extObs : fiber(h) → V × Fin n` such that compatibility factors through `extObs`.

This is the minimal “interface lift” claim: the lift is not a new magical observation; it
strictly refines the original `obs` by adding only a finite index.
-/
theorem refiningLift_of_compatDimLe_prop
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) :
    CompatDimLe (P := P) sem obs target_obs step n →
      RefiningLift (P := P) sem obs target_obs h step n := by
  rintro ⟨σ, predFin, hcorr⟩
  let extObs : FiberPt (P := P) obs target_obs h → V × Fin n := fun x => (obs x.1, σ x)
  refine ⟨
    { extObs := extObs
      refines_fst := (by intro x; rfl)
      predFin := predFin
      factors := (by intro x; simpa [extObs] using (hcorr x)) }⟩

theorem refiningLift_of_compatDimLe
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) :
    CompatDimLe (P := P) sem obs target_obs step n →
      ∃ extObs : FiberPt (P := P) obs target_obs h → V × Fin n,
        RefinesOnFiber (P := P) obs target_obs h extObs ∧
          CompatFactorsThrough (P := P) sem obs target_obs step extObs := by
  rintro ⟨σ, predFin, hcorr⟩
  let extObs : FiberPt (P := P) obs target_obs h → V × Fin n := fun x => (obs x.1, σ x)
  refine ⟨extObs, ?_, ?_⟩
  · refine ⟨Prod.fst, ?_⟩
    intro x
    rfl
  · refine ⟨(fun w : V × Fin n => predFin w.2), ?_⟩
    intro x
    simpa [extObs] using (hcorr x)

/-- Any `RefiningLift` induces `CompatDimLe` (read off its `Fin n` supplement). -/
theorem compatDimLe_of_refiningLift
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) :
    RefiningLift (P := P) sem obs target_obs h step n →
    CompatDimLe (P := P) sem obs target_obs step n := by
  rintro ⟨L⟩
  refine ⟨(fun x => (L.extObs x).2), L.predFin, ?_⟩
  intro x
  simpa using (L.factors x)

/-- Canonical equivalence: compatibility dimension `≤ n` iff there exists a refining lift with `Fin n` supplement. -/
theorem compatDimLe_iff_refiningLift
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) :
    CompatDimLe (P := P) sem obs target_obs step n ↔
      RefiningLift (P := P) sem obs target_obs h step n := by
  constructor
  · exact refiningLift_of_compatDimLe_prop (P := P) sem obs target_obs step n
  · exact compatDimLe_of_refiningLift (P := P) sem obs target_obs step n

/--
Global compression implies step-local compression:
compressing the full signature `Sig` into `Fin n` yields a `CompatDimLe … step n` witness
for any fixed `step`.
-/
theorem compatDimLe_of_compatSigDimLe
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) {n : Nat} :
    CompatSigDimLe (P := P) sem obs target_obs (h := h) n →
      CompatDimLe (P := P) sem obs target_obs step n :=
by
  rintro ⟨σ, pred, Hcorr⟩
  let fut : Future h := ⟨k, step⟩
  refine ⟨σ, (fun i => pred i fut), ?_⟩
  intro x
  have := Hcorr x fut
  simpa [CompatibleFuture, fut] using this.symm

/-- `CompatSigDimLe` also yields a refining lift for any fixed `step`. -/
theorem refiningLift_of_compatSigDimLe
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) :
    CompatSigDimLe (P := P) sem obs target_obs (h := h) n →
      RefiningLift (P := P) sem obs target_obs h step n :=
by
  intro hSig
  exact (compatDimLe_iff_refiningLift (P := P) sem obs target_obs step n).1
    ((compatDimLe_of_compatSigDimLe (P := P) sem obs target_obs step) hSig)

/-- Monotonicity: if `CompatDimLe … m` and `m ≤ n`, then `CompatDimLe … n`. -/
theorem compatDimLe_mono
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) {m n : Nat} (hmn : m ≤ n) :
    CompatDimLe (P := P) sem obs target_obs step m →
      CompatDimLe (P := P) sem obs target_obs step n := by
  rintro ⟨σ, pred, hcorr⟩
  let emb : Fin m → Fin n := PrimitiveHolonomy.Combinatorics.finEmbed hmn
  let σ' : FiberPt (P := P) obs target_obs h → Fin n := fun x => emb (σ x)
  let pred' : Fin n → Prop := fun i => ∃ j : Fin m, emb j = i ∧ pred j
  refine ⟨σ', pred', ?_⟩
  intro x
  constructor
  · intro hC
    have : pred (σ x) := (hcorr x).1 hC
    exact ⟨σ x, rfl, this⟩
  · rintro ⟨j, hj, hjPred⟩
    have : j = σ x := by
      apply PrimitiveHolonomy.Combinatorics.finEmbed_injective hmn
      simpa [σ'] using hj
    subst this
    exact (hcorr x).2 hjPred

/-- Exact dimension `n`: possible with `n`, impossible with any strict smaller `m < n`. -/
def CompatDimEq
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) : Prop :=
  CompatDimLe (P := P) sem obs target_obs step n ∧
    ∀ m : Nat, m < n → ¬ CompatDimLe (P := P) sem obs target_obs step m

/-- From exact dimension, a refining lift exists at that exact finite supplement size. -/
theorem refiningLift_of_compatDimEq
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) :
    CompatDimEq (P := P) sem obs target_obs step n →
      RefiningLift (P := P) sem obs target_obs h step n := by
  intro hEq
  exact (compatDimLe_iff_refiningLift (P := P) sem obs target_obs step n).1 hEq.1

/-- Exactness packaging: if `CompatDimEq … n`, then there is no refining lift with any strict smaller supplement. -/
theorem no_smaller_refiningLift_of_compatDimEq
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) :
    CompatDimEq (P := P) sem obs target_obs step n →
      ∀ m : Nat, m < n → ¬ RefiningLift (P := P) sem obs target_obs h step m := by
  rintro ⟨_, hMin⟩ m hm hLift
  have hDim : CompatDimLe (P := P) sem obs target_obs step m :=
    (compatDimLe_iff_refiningLift (P := P) sem obs target_obs step m).2 hLift
  exact hMin m hm hDim

/-- Invariance of `CompatDimLe` under postcomposition of observables by an equivalence. -/
theorem compatDimLe_congr_postObsEquiv
    {S : Type w} {V V' : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (e : Equiv V V') {h k : P} (step : HistoryGraph.Path h k) (n : Nat) :
    CompatDimLe (P := P) sem obs target_obs step n ↔
      CompatDimLe (P := P) sem (obsPost e obs) (targetObsPost e target_obs) step n := by
  constructor
  · rintro ⟨σ, pred, hcorr⟩
    refine ⟨(fun x => σ (fiberPtPostMapInv (P := P) e obs target_obs x)), pred, ?_⟩
    intro x
    have hx : Compatible (P := P) sem obs target_obs step (fiberPtPostMapInv (P := P) e obs target_obs x) ↔
        pred (σ (fiberPtPostMapInv (P := P) e obs target_obs x)) :=
      hcorr (fiberPtPostMapInv (P := P) e obs target_obs x)
    have hC :
        Compatible (P := P) sem (obsPost e obs) (targetObsPost e target_obs) step x ↔
          Compatible (P := P) sem obs target_obs step (fiberPtPostMapInv (P := P) e obs target_obs x) := by
      simpa using (compatible_congr_postObsEquiv_inv (P := P) sem obs target_obs e step x)
    exact hC.trans hx
  · rintro ⟨σ, pred, hcorr⟩
    refine ⟨(fun x => σ (fiberPtPostMap (P := P) e obs target_obs x)), pred, ?_⟩
    intro x
    have hx : Compatible (P := P) sem (obsPost e obs) (targetObsPost e target_obs) step
          (fiberPtPostMap (P := P) e obs target_obs x) ↔
        pred (σ (fiberPtPostMap (P := P) e obs target_obs x)) :=
      hcorr (fiberPtPostMap (P := P) e obs target_obs x)
    have hC :
        Compatible (P := P) sem obs target_obs step x ↔
          Compatible (P := P) sem (obsPost e obs) (targetObsPost e target_obs) step
            (fiberPtPostMap (P := P) e obs target_obs x) :=
      compatible_congr_postObsEquiv (P := P) sem obs target_obs e step x
    exact hC.trans hx

 /-- Invariance of `RefiningLift` under postcomposition of observables by an equivalence. -/
theorem refiningLift_congr_postObsEquiv
    {S : Type w} {V V' : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (e : Equiv V V') {h k : P} (step : HistoryGraph.Path h k) (n : Nat) :
    RefiningLift (P := P) sem obs target_obs h step n ↔
      RefiningLift (P := P) sem (obsPost e obs) (targetObsPost e target_obs) h step n := by
  have hDim :
      CompatDimLe (P := P) sem obs target_obs step n ↔
        CompatDimLe (P := P) sem (obsPost e obs) (targetObsPost e target_obs) step n :=
    compatDimLe_congr_postObsEquiv (P := P) sem obs target_obs e step n
  calc
    RefiningLift (P := P) sem obs target_obs h step n ↔
        CompatDimLe (P := P) sem obs target_obs step n := by
          symm
          exact compatDimLe_iff_refiningLift (P := P) sem obs target_obs step n
    _ ↔ CompatDimLe (P := P) sem (obsPost e obs) (targetObsPost e target_obs) step n := hDim
    _ ↔ RefiningLift (P := P) sem (obsPost e obs) (targetObsPost e target_obs) h step n := by
          exact compatDimLe_iff_refiningLift (P := P) sem (obsPost e obs) (targetObsPost e target_obs) step n

/-- A visible dimension bound is in particular a compatibility dimension bound. -/
theorem visibleCompatDimLe_imp_compatDimLe
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) :
    VisibleCompatDimLe (P := P) sem obs target_obs step n →
      CompatDimLe (P := P) sem obs target_obs step n := by
  rintro ⟨σ, pred, _hσ, hcorr⟩
  exact ⟨σ, pred, hcorr⟩


/-- “Dimension exactly 2” in the minimal sense: possible with 2, impossible with 1. -/
def CompatDimEqTwo {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) : Prop :=
  CompatDimLe sem obs target_obs step 2 ∧ ¬ CompatDimLe sem obs target_obs step 1

/--
Alias used for the 'dimensionnelle' discussion: a small finite summary that predicts compatibility.

This is currently just a name for `CompatDimLe`.
-/
abbrev LagDimLe {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) : Prop :=
  CompatDimLe sem obs target_obs step n

/-- Alias: 'dimension exactly 2' for `LagDimLe`. -/
abbrev LagDimEqTwo {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) : Prop :=
  CompatDimEqTwo sem obs target_obs step


/-- A `Fin n` summary with injective encoding always gives `CompatDimLe … n`. -/
theorem compatDimLe_of_injective_summary
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) {n : Nat}
    (σ : FiberPt (P := P) obs target_obs h → Fin n)
    (hσ : Function.Injective σ) :
    CompatDimLe (P := P) sem obs target_obs step n := by
  let pred : Fin n → Prop :=
    fun i => ∃ x : FiberPt (P := P) obs target_obs h, σ x = i ∧ Compatible (P := P) sem obs target_obs step x
  refine ⟨σ, pred, ?_⟩
  intro x
  constructor
  · intro hC
    exact ⟨x, rfl, hC⟩
  · intro hp
    rcases hp with ⟨x', hx', hC'⟩
    have hx : x' = x := by
      apply hσ
      simpa using hx'
    simpa [hx] using hC'

end WithHistoryGraph

/-- Two fiber points of a `LagState` are equal if their hidden components are equal. -/
theorem fiberPt_eq_of_hidden_eq
    {Y B : Type w} {target_obs : P → Y} {h : P}
    (x x' : FiberPt (P := P) (obs := (lagObs (Y := Y) (B := B))) target_obs h)
    (hh : x.1.hidden = x'.1.hidden) : x = x' := by
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
          have hhid : hid = hid' := by
            simpa using hh
          cases hhid
          rfl

section WithHistoryGraph

variable [HistoryGraph P]

/-- If the hidden component embeds into `Fin n`, then compatibility has dimension ≤ `n`. -/
theorem compatDimLe_of_hiddenEmb
    {Y B : Type w} (sem : Semantics P (LagState Y B)) (target_obs : P → Y)
    {h k : P} (step : HistoryGraph.Path h k) {n : Nat}
    (f : B → Fin n) (hf : Function.Injective f) :
    CompatDimLe (P := P) sem (lagObs (Y := Y) (B := B)) target_obs step n := by
  let σ : FiberPt (P := P) (obs := (lagObs (Y := Y) (B := B))) target_obs h → Fin n :=
    fun x => f x.1.hidden
  have hσ : Function.Injective σ := by
    intro x x' hxx'
    apply fiberPt_eq_of_hidden_eq (P := P) (target_obs := target_obs) x x'
    exact hf hxx'
  exact
    compatDimLe_of_injective_summary (P := P) sem (lagObs (Y := Y) (B := B)) target_obs step σ hσ

/--
Compatibility along `step` is classified by at most `n` classes that depend only on the `hidden` component.

This isolates the realization-dependent upper-bound mechanism used by examples like the bool-hidden diagonal.
-/
def HiddenCompatClassifiedByFin
    {Y B : Type w} (sem : Semantics P (LagState Y B)) (target_obs : P → Y)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) : Prop :=
  ∃ (τ : FiberPt (P := P) (obs := (lagObs (Y := Y) (B := B))) target_obs h → Fin n)
    (pred : Fin n → Prop),
      (∀ x x' : FiberPt (P := P) (obs := (lagObs (Y := Y) (B := B))) target_obs h,
        x.1.hidden = x'.1.hidden →
          τ x = τ x') ∧
      ∀ x : FiberPt (P := P) (obs := (lagObs (Y := Y) (B := B))) target_obs h,
        Compatible (P := P) sem (lagObs (Y := Y) (B := B)) target_obs step x ↔ pred (τ x)

/-- A hidden finite classifier yields an upper bound on compatibility dimension. -/
theorem compatDimLe_of_hiddenCompatClassifiedByFin
    {Y B : Type w} (sem : Semantics P (LagState Y B)) (target_obs : P → Y)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) :
    HiddenCompatClassifiedByFin (P := P) sem target_obs step n →
      CompatDimLe (P := P) sem (lagObs (Y := Y) (B := B)) target_obs step n := by
  rintro ⟨τ, pred, _hτ, hcorr⟩
  exact ⟨τ, pred, hcorr⟩

/-- Helper: constructive replacement for `Nat.lt_one_iff` (axiom-free). -/
theorem nat_eq_zero_of_lt_one {n : Nat} (hn : n < 1) : n = 0 := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      exfalso
      have : Nat.succ n < Nat.succ 0 := hn
      have : n < 0 := Nat.lt_of_succ_lt_succ this
      exact Nat.not_lt_zero n this

theorem not_compatDimLe_one_of_stepSeparatesFiber
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) :
    StepSeparatesFiber sem obs target_obs step →
      ¬ CompatDimLe sem obs target_obs step 1 := by
  intro hSep hDim
  rcases hSep with ⟨x, x', _hxne, hx, hx'⟩
  rcases hDim with ⟨σ, pred, hcorr⟩
  have hσ : σ x = σ x' := by
    apply Fin.ext
    have hx0 : (σ x).val = 0 := nat_eq_zero_of_lt_one (σ x).isLt
    have hx'0 : (σ x').val = 0 := nat_eq_zero_of_lt_one (σ x').isLt
    exact hx0.trans hx'0.symm
  have hp : pred (σ x) := (hcorr x).1 hx
  have hp' : pred (σ x') := Eq.mp (congrArg pred hσ) hp
  have hxCompat' : Compatible sem obs target_obs step x' := (hcorr x').2 hp'
  exact hx' hxCompat'

theorem not_compatDimLe_one_of_lagEvent
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k') :
    LagEvent sem obs target_obs α step →
      ¬ CompatDimLe sem obs target_obs step 1 := by
  intro hLag
  rcases hLag with ⟨x, x', hxne, _hHol, hx, hx'⟩
  refine not_compatDimLe_one_of_stepSeparatesFiber sem obs target_obs step ?_
  exact ⟨x, x', hxne, hx, hx'⟩



/-- Pairwise separation of compatibility on a finite witness family indexed by `Fin n`. -/
def PairwiseCompatSeparated
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) {n : Nat}
    (x : Fin n → FiberPt (P := P) obs target_obs h) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    ¬ (Compatible (P := P) sem obs target_obs step (x i) ↔
       Compatible (P := P) sem obs target_obs step (x j))

/--
General finite lower bound: if `n` witnesses are pairwise compatibility-separated, then
no `Fin m` predictor exists for any `m < n`.

This is the constructive pigeonhole step that turns explicit finite families into dimension
lower bounds.
-/
theorem not_compatDimLe_of_finite_witness_family
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k)
    {n m : Nat}
    (x : Fin n → FiberPt (P := P) obs target_obs h)
    (hsep : PairwiseCompatSeparated (P := P) sem obs target_obs step x)
    (hmn : m < n) :
    ¬ CompatDimLe (P := P) sem obs target_obs step m := by
  intro hDim
  rcases hDim with ⟨σ, pred, hcorr⟩
  let f : Fin n → Fin m := fun i => σ (x i)
  rcases PrimitiveHolonomy.Combinatorics.exists_ne_map_eq_of_lt_fin (m := m) (n := n) hmn f with
    ⟨i, j, hij, hEq⟩
  have hCompatEq :
      Compatible (P := P) sem obs target_obs step (x i) ↔
        Compatible (P := P) sem obs target_obs step (x j) := by
    have hpred : pred (σ (x i)) ↔ pred (σ (x j)) :=
      iff_of_eq (congrArg pred hEq)
    exact (hcorr (x i)).trans (hpred.trans (hcorr (x j)).symm)
  exact hsep i j hij hCompatEq

/--
Lower bound for dimension 2: if the step yields three fiber points whose compatibility propositions
are pairwise *not equivalent*, then no `Fin 2` predictor can exist.

This is the minimal “3-way separation witness” pattern used for Step D in the roadmap.
-/
theorem not_compatDimLe_two_of_three_witnesses
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k)
    (x0 x1 x2 : FiberPt (P := P) obs target_obs h)
    (h01 : ¬ (Compatible (P := P) sem obs target_obs step x0 ↔
      Compatible (P := P) sem obs target_obs step x1))
    (h02 : ¬ (Compatible (P := P) sem obs target_obs step x0 ↔
      Compatible (P := P) sem obs target_obs step x2))
    (h12 : ¬ (Compatible (P := P) sem obs target_obs step x1 ↔
      Compatible (P := P) sem obs target_obs step x2)) :
    ¬ CompatDimLe (P := P) sem obs target_obs step 2 := by
  intro hDim
  rcases hDim with ⟨σ, pred, hcorr⟩

  -- Helper: every `Fin 2` value has `val = 0` or `val = 1`.
  have fin2_val_eq_zero_or_eq_one : ∀ i : Fin 2, i.val = 0 ∨ i.val = 1 := by
    intro i
    cases i with
    | mk v hv =>
        cases v with
        | zero =>
            left
            rfl
        | succ v' =>
            have hv' : v' = 0 := by
              have : v' < 1 := by
                have : Nat.succ v' < 2 := hv
                exact Nat.lt_of_succ_lt_succ this
              exact nat_eq_zero_of_lt_one this
            subst hv'
            right
            rfl

  -- If two points are assigned the same class, their compatibility is equivalent.
  have compat_iff_of_sigma_eq :
      ∀ {x y : FiberPt (P := P) obs target_obs h}, σ x = σ y →
        (Compatible (P := P) sem obs target_obs step x ↔
          Compatible (P := P) sem obs target_obs step y) := by
    intro x y hσ
    have hpred : pred (σ x) ↔ pred (σ y) :=
      iff_of_eq (congrArg pred hσ)
    exact (hcorr x).trans (hpred.trans (hcorr y).symm)

  by_cases hx01 : σ x0 = σ x1
  · exact h01 (compat_iff_of_sigma_eq hx01)
  · by_cases hx02 : σ x0 = σ x2
    · exact h02 (compat_iff_of_sigma_eq hx02)
    · -- Now `σ x1 = σ x2` must hold since `Fin 2` has only two values.
      have hx12 : σ x1 = σ x2 := by
        rcases fin2_val_eq_zero_or_eq_one (σ x0) with h0 | h0
        · -- `val = 0`, so both `σ x1` and `σ x2` must have `val = 1`.
          have h1 : (σ x1).val = 1 := by
            rcases fin2_val_eq_zero_or_eq_one (σ x1) with h10 | h11
            ·
              exfalso
              apply hx01
              apply Fin.ext
              exact h0.trans h10.symm
            · exact h11
          have h2 : (σ x2).val = 1 := by
            rcases fin2_val_eq_zero_or_eq_one (σ x2) with h20 | h21
            ·
              exfalso
              apply hx02
              apply Fin.ext
              exact h0.trans h20.symm
            · exact h21
          apply Fin.ext
          exact h1.trans h2.symm
        · -- `val = 1`, so both `σ x1` and `σ x2` must have `val = 0`.
          have h1 : (σ x1).val = 0 := by
            rcases fin2_val_eq_zero_or_eq_one (σ x1) with h10 | h11
            · exact h10
            ·
              exfalso
              apply hx01
              apply Fin.ext
              exact h0.trans h11.symm
          have h2 : (σ x2).val = 0 := by
            rcases fin2_val_eq_zero_or_eq_one (σ x2) with h20 | h21
            · exact h20
            ·
              exfalso
              apply hx02
              apply Fin.ext
              exact h0.trans h21.symm
          apply Fin.ext
          exact h1.trans h2.symm
      exact h12 (compat_iff_of_sigma_eq hx12)

/--
Exactness pattern (dimension 2): a lag event gives the lower bound `¬ CompatDimLe 1`,
while a hidden classifier into `Fin 2` gives the upper bound `CompatDimLe 2`.
-/
theorem compatDimEqTwo_of_lagEvent_and_hiddenCompatClassifiedByFin_two
    {Y B : Type w} (sem : Semantics P (LagState Y B)) (target_obs : P → Y)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k') :
    LagEvent (P := P) sem (lagObs (Y := Y) (B := B)) target_obs α step →
    HiddenCompatClassifiedByFin (P := P) sem target_obs step 2 →
      CompatDimEqTwo (P := P) sem (lagObs (Y := Y) (B := B)) target_obs step := by
  intro hLag hCls
  refine ⟨?_, ?_⟩
  · exact compatDimLe_of_hiddenCompatClassifiedByFin (P := P) sem target_obs step 2 hCls
  · exact
      not_compatDimLe_one_of_lagEvent (P := P) sem (lagObs (Y := Y) (B := B)) target_obs
        (α := α) (step := step) hLag

theorem visiblePredictsStep_of_obsPredictsStep
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) :
    ObsPredictsStep sem obs target_obs step →
      VisiblePredictsStep sem obs target_obs step := by
  rintro ⟨pred, hpred⟩
  refine ⟨V, (fun x => obs x.1), pred, ?_, ?_⟩
  · refine ⟨(fun v => v), ?_⟩
    intro x
    rfl
  · intro x
    exact hpred x

theorem stepSeparatesFiber_of_lagEvent
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k') :
    LagEvent sem obs target_obs α step →
      StepSeparatesFiber sem obs target_obs step := by
  rintro ⟨x, x', hxne, _hHol, hx, hx'⟩
  exact ⟨x, x', hxne, hx, hx'⟩

theorem not_visiblePredictsStep_of_stepSeparatesFiber
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k) :
    StepSeparatesFiber sem obs target_obs step →
      ¬ VisiblePredictsStep sem obs target_obs step := by
  intro hSep hVis
  rcases hSep with ⟨x, x', hxne, hx, hx'⟩
  rcases hVis with ⟨Q, σ, pred, hσ, hcorr⟩
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
  have hp : pred (σ x) := (hcorr x).1 hx
  have hp' : pred (σ x') := by
    exact Eq.mp (congrArg pred hσxx') hp
  have hxCompat' : Compatible sem obs target_obs step x' := (hcorr x').2 hp'
  exact hx' hxCompat'

theorem not_visiblePredictsStep_of_lagEvent
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k') :
    LagEvent sem obs target_obs α step →
      ¬ VisiblePredictsStep sem obs target_obs step := by
  intro hLag
  refine not_visiblePredictsStep_of_stepSeparatesFiber sem obs target_obs step ?_
  exact stepSeparatesFiber_of_lagEvent sem obs target_obs α step hLag

/--
**Abstract Observable Under-Factorization / Internal Lift Theorem**

If a lag event occurs for `step` (hence no visible-only predictor exists), but compatibility is
internally classifiable by `n` finite classes, then:

1) the visible interface is insufficient (`¬ VisiblePredictsStep … step`);
2) an explicit refining lift `extObs` exists through which compatibility factors.
-/
theorem nonDescent_and_refiningLift_of_lagEvent_and_compatDimLe
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k') (n : Nat) :
    LagEvent (P := P) sem obs target_obs (h := h) (k := k) (k' := k') (p := p) (q := q) α step →
    CompatDimLe (P := P) sem obs target_obs step n →
      (¬ VisiblePredictsStep (P := P) sem obs target_obs (h := h) (k := k') step)
        ∧
      (∃ extObs : FiberPt (P := P) obs target_obs h → V × Fin n,
        RefinesOnFiber (P := P) obs target_obs h extObs ∧
          CompatFactorsThrough (P := P) sem obs target_obs step extObs) := by
  intro hLag hDim
  refine ⟨not_visiblePredictsStep_of_lagEvent (P := P) sem obs target_obs (α := α) (step := step) hLag, ?_⟩
  exact refiningLift_of_compatDimLe (P := P) sem obs target_obs step n hDim

/--
Canonical packaging of the core result:

`LagEvent` gives non-descending visible insufficiency, and `CompatDimLe … n` gives a *canonical*
`RefiningLift` whose supplement `Fin n` alone controls compatibility.
-/
theorem nonDescent_and_refiningLiftStruct_of_lagEvent_and_compatDimLe
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k') (n : Nat) :
    LagEvent (P := P) sem obs target_obs (h := h) (k := k) (k' := k') (p := p) (q := q) α step →
    CompatDimLe (P := P) sem obs target_obs step n →
      (¬ VisiblePredictsStep (P := P) sem obs target_obs (h := h) (k := k') step)
        ∧
      RefiningLift (P := P) sem obs target_obs h step n := by
  intro hLag hDim
  refine ⟨
    not_visiblePredictsStep_of_lagEvent (P := P) sem obs target_obs (α := α) (step := step) hLag,
    refiningLift_of_compatDimLe_prop (P := P) sem obs target_obs step n hDim⟩


/-- Lag forbids any visible finite-class predictor (hence.1 visible compatibility dimension for any `n`). -/
theorem not_visibleCompatDimLe_of_lagEvent
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k') (n : Nat) :
    LagEvent sem obs target_obs α step →
      ¬ VisibleCompatDimLe (P := P) sem obs target_obs step n := by
  intro hLag hVis
  have hPred : VisiblePredictsStep (P := P) sem obs target_obs step :=
    visiblePredictsStep_of_visibleCompatDimLe (P := P) sem obs target_obs step n hVis
  exact (not_visiblePredictsStep_of_lagEvent (P := P) sem obs target_obs α step hLag) hPred

/-- Lag forbids visible compatibility dimension `1`. -/
theorem not_visibleCompatDimLe_one_of_lagEvent
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k') :
    LagEvent sem obs target_obs α step →
      ¬ VisibleCompatDimLe (P := P) sem obs target_obs step 1 := by
  intro hLag
  exact not_visibleCompatDimLe_of_lagEvent (P := P) sem obs target_obs α step 1 hLag

/--
Specialized `2`-class form of the internal-vs-visible split:
a lag event plus a hidden binary classifier yields exact internal dimension `2`,
while still forbidding any visible-only predictor.
-/
theorem hiddenCompatClassifiedByFin_two_and_lagEvent_yield_dimTwo_but_no_visible_predictor
    {Y B : Type w} (sem : Semantics P (LagState Y B)) (target_obs : P → Y)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k') :
    HiddenCompatClassifiedByFin (P := P) sem target_obs step 2 →
      LagEvent (P := P) sem (lagObs (Y := Y) (B := B)) target_obs α step →
        CompatDimEqTwo (P := P) sem (lagObs (Y := Y) (B := B)) target_obs step
        ∧ ¬ VisiblePredictsStep (P := P) sem (lagObs (Y := Y) (B := B)) target_obs step := by
  intro hCls hLag
  refine ⟨
    compatDimEqTwo_of_lagEvent_and_hiddenCompatClassifiedByFin_two
      (P := P) sem target_obs α step hLag hCls,
    not_visiblePredictsStep_of_lagEvent
      (P := P) sem (lagObs (Y := Y) (B := B)) target_obs α step hLag⟩





/--
If compatibility is recoverable from a hidden finite classifier while a lag event occurs,
then the step has an internal finite summary but no visible-only predictor at any finite budget.

This isolates the structural pattern “internally recoverable, visibly unreadable”.
-/
theorem hiddenCompatClassifiedByFin_and_lagEvent_yield_internal_recovery_but_no_visible_predictor
    {Y B : Type w} (sem : Semantics P (LagState Y B)) (target_obs : P → Y)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k') (n : Nat) :
    HiddenCompatClassifiedByFin (P := P) sem target_obs step n →
      LagEvent (P := P) sem (lagObs (Y := Y) (B := B)) target_obs α step →
        CompatDimLe (P := P) sem (lagObs (Y := Y) (B := B)) target_obs step n
        ∧ ¬ VisiblePredictsStep (P := P) sem (lagObs (Y := Y) (B := B)) target_obs step
        ∧ ∀ m : Nat, ¬ VisibleCompatDimLe (P := P) sem (lagObs (Y := Y) (B := B)) target_obs step m := by
  intro hCls hLag
  refine ⟨
    compatDimLe_of_hiddenCompatClassifiedByFin (P := P) sem target_obs step n hCls,
    not_visiblePredictsStep_of_lagEvent (P := P) sem (lagObs (Y := Y) (B := B)) target_obs α step hLag,
    ?_⟩
  intro m
  exact not_visibleCompatDimLe_of_lagEvent
    (P := P) sem (lagObs (Y := Y) (B := B)) target_obs α step m hLag

/-- A lag event forbids even the strongest (obs-only) predictor. -/
theorem not_obsPredictsStep_of_lagEvent
    {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k') :
    LagEvent sem obs target_obs α step →
      ¬ ObsPredictsStep sem obs target_obs step := by
  intro hLag hObs
  have hVis : VisiblePredictsStep sem obs target_obs step :=
    visiblePredictsStep_of_obsPredictsStep sem obs target_obs step hObs
  exact (not_visiblePredictsStep_of_lagEvent sem obs target_obs α step hLag) hVis

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


-- NOTE (2026-03-25):
-- The earlier theorem `hiddenCompatClassifiedByFin_to_compatDimLe_enriched` was removed.
-- Reason: with `obs' := (lagObs, hidden)` and `target_obs' := (target_obs, default)`,
-- the source (and target) fibers force `hidden = default`, and `Compatible` quantifies over
-- witnesses in a strictly smaller fiber than the corresponding `lagObs`-fiber. This breaks
-- the intended equivalence and makes the statement either false in general or vacuous.

end WithHistoryGraph

end PrimitiveHolonomy


/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
Auto-generated: `#print axioms` for each `def`, `abbrev`, `theorem`/`lemma` in this file,
ordered by line of appearance.
-/
#print axioms PrimitiveHolonomy.Compatible
#print axioms PrimitiveHolonomy.LagEvent
#print axioms PrimitiveHolonomy.lag_of_witness
#print axioms PrimitiveHolonomy.Future
#print axioms PrimitiveHolonomy.CanonicalMediator
#print axioms PrimitiveHolonomy.CompatibleFuture
#print axioms PrimitiveHolonomy.Sig
#print axioms PrimitiveHolonomy.canonicalMediator
#print axioms PrimitiveHolonomy.SigFam
#print axioms PrimitiveHolonomy.iff_of_eq
#print axioms PrimitiveHolonomy.sigFam_iff_of_summary_correct
#print axioms PrimitiveHolonomy.sig_iff_of_summary_correct
#print axioms PrimitiveHolonomy.SigFactorsThrough
#print axioms PrimitiveHolonomy.sigFactorsThrough_of_summary_correct
#print axioms PrimitiveHolonomy.CompatSigDimLe
#print axioms PrimitiveHolonomy.CompatSigDimEq
#print axioms PrimitiveHolonomy.sigFactorsThrough_of_compatSigDimLe
#print axioms PrimitiveHolonomy.compatSigDimLe_of_sigFactorsThrough
#print axioms PrimitiveHolonomy.compatSigDimLe_iff_exists_sigFactorsThrough
#print axioms PrimitiveHolonomy.compatSigDimLe_mono
#print axioms PrimitiveHolonomy.exists_sigFactorsThrough_of_compatSigDimEq
#print axioms PrimitiveHolonomy.CompatSigDimEqTwo
#print axioms PrimitiveHolonomy.summary_separates_compatible_witness
#print axioms PrimitiveHolonomy.lagEvent_gives_summary_witness
#print axioms PrimitiveHolonomy.StepSeparatesFiber
#print axioms PrimitiveHolonomy.VisiblePredictsStep
#print axioms PrimitiveHolonomy.ObsPredictsStep
#print axioms PrimitiveHolonomy.VisibleCompatDimLe
#print axioms PrimitiveHolonomy.visiblePredictsStep_of_visibleCompatDimLe
#print axioms PrimitiveHolonomy.obsPost
#print axioms PrimitiveHolonomy.targetObsPost
#print axioms PrimitiveHolonomy.fiberPtPostMap
#print axioms PrimitiveHolonomy.fiberPtPostMapInv
#print axioms PrimitiveHolonomy.compatible_congr_postObsEquiv
#print axioms PrimitiveHolonomy.compatible_congr_postObsEquiv_inv
#print axioms PrimitiveHolonomy.visiblePredictsStep_congr_postObsEquiv
#print axioms PrimitiveHolonomy.visibleCompatDimLe_congr_postObsEquiv
#print axioms PrimitiveHolonomy.CompatDimLe
#print axioms PrimitiveHolonomy.RefinesOnFiber
#print axioms PrimitiveHolonomy.CompatFactorsThrough
#print axioms PrimitiveHolonomy.RefiningLiftData
#print axioms PrimitiveHolonomy.refiningLiftData_refinesOnFiber
#print axioms PrimitiveHolonomy.RefiningLift
#print axioms PrimitiveHolonomy.RefiningLiftOnFiber
#print axioms PrimitiveHolonomy.refiningLift_of_compatDimLe_prop
#print axioms PrimitiveHolonomy.refiningLift_of_compatDimLe
#print axioms PrimitiveHolonomy.compatDimLe_of_refiningLift
#print axioms PrimitiveHolonomy.compatDimLe_iff_refiningLift
#print axioms PrimitiveHolonomy.compatDimLe_of_compatSigDimLe
#print axioms PrimitiveHolonomy.refiningLift_of_compatSigDimLe
#print axioms PrimitiveHolonomy.compatDimLe_mono
#print axioms PrimitiveHolonomy.CompatDimEq
#print axioms PrimitiveHolonomy.refiningLift_of_compatDimEq
#print axioms PrimitiveHolonomy.no_smaller_refiningLift_of_compatDimEq
#print axioms PrimitiveHolonomy.compatDimLe_congr_postObsEquiv
#print axioms PrimitiveHolonomy.refiningLift_congr_postObsEquiv
#print axioms PrimitiveHolonomy.visibleCompatDimLe_imp_compatDimLe
#print axioms PrimitiveHolonomy.CompatDimEqTwo
#print axioms PrimitiveHolonomy.LagDimLe
#print axioms PrimitiveHolonomy.LagDimEqTwo
#print axioms PrimitiveHolonomy.compatDimLe_of_injective_summary
#print axioms PrimitiveHolonomy.fiberPt_eq_of_hidden_eq
#print axioms PrimitiveHolonomy.compatDimLe_of_hiddenEmb
#print axioms PrimitiveHolonomy.HiddenCompatClassifiedByFin
#print axioms PrimitiveHolonomy.compatDimLe_of_hiddenCompatClassifiedByFin
#print axioms PrimitiveHolonomy.nat_eq_zero_of_lt_one
#print axioms PrimitiveHolonomy.not_compatDimLe_one_of_stepSeparatesFiber
#print axioms PrimitiveHolonomy.not_compatDimLe_one_of_lagEvent
#print axioms PrimitiveHolonomy.PairwiseCompatSeparated
#print axioms PrimitiveHolonomy.not_compatDimLe_of_finite_witness_family
#print axioms PrimitiveHolonomy.not_compatDimLe_two_of_three_witnesses
#print axioms PrimitiveHolonomy.compatDimEqTwo_of_lagEvent_and_hiddenCompatClassifiedByFin_two
#print axioms PrimitiveHolonomy.visiblePredictsStep_of_obsPredictsStep
#print axioms PrimitiveHolonomy.stepSeparatesFiber_of_lagEvent
#print axioms PrimitiveHolonomy.not_visiblePredictsStep_of_stepSeparatesFiber
#print axioms PrimitiveHolonomy.not_visiblePredictsStep_of_lagEvent
#print axioms PrimitiveHolonomy.nonDescent_and_refiningLift_of_lagEvent_and_compatDimLe
#print axioms PrimitiveHolonomy.nonDescent_and_refiningLiftStruct_of_lagEvent_and_compatDimLe
#print axioms PrimitiveHolonomy.not_visibleCompatDimLe_of_lagEvent
#print axioms PrimitiveHolonomy.not_visibleCompatDimLe_one_of_lagEvent
#print axioms PrimitiveHolonomy.hiddenCompatClassifiedByFin_two_and_lagEvent_yield_dimTwo_but_no_visible_predictor
#print axioms PrimitiveHolonomy.hiddenCompatClassifiedByFin_and_lagEvent_yield_internal_recovery_but_no_visible_predictor
#print axioms PrimitiveHolonomy.not_obsPredictsStep_of_lagEvent
#print axioms PrimitiveHolonomy.StepDependsOnHidden
#print axioms PrimitiveHolonomy.lag_of_twist_and_hidden_step
/- AXIOM_AUDIT_END -/
