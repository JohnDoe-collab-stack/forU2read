/-!
# Primitive Holonomy: the 2-geometry before any collapsing/identification

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

namespace Relation

/-- Reflexive-transitive closure of a relation (minimal, constructive). -/
inductive ReflTransGen {α : Type u} (r : α → α → Prop) : α → α → Prop where
  | refl (a : α) : ReflTransGen r a a
  | tail {a b c : α} : ReflTransGen r a b → r b c → ReflTransGen r a c

namespace ReflTransGen

/-- Single-step embedding into the reflexive-transitive closure. -/
theorem single {α : Type u} {r : α → α → Prop} {a b : α} (hab : r a b) : ReflTransGen r a b :=
  tail (refl a) hab

end ReflTransGen

end Relation

namespace Nat

/-- Constructive oddness predicate (so we do not depend on Std/Mathlib's `Nat.Odd`). -/
def Odd (n : Nat) : Prop := ∃ k : Nat, n = 2 * k + 1

end Nat

/-!
### Minimal `Equiv`

We avoid importing Std/Mathlib, so we define the tiny amount of "equivalence of types"
needed for postcomposition invariance in the dynamics layer.
-/
structure Equiv (A : Type u) (B : Type v) where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ a : A, invFun (toFun a) = a
  right_inv : ∀ b : B, toFun (invFun b) = b

-- This project runs without the usual prelude `Set`/set-builder notation.
-- We keep a local, constructive definition: a set is just a predicate.
abbrev Set (α : Type u) : Type u := α → Prop

instance {α : Type u} : Membership α (Set α) where
  mem s x := s x

instance {α : Type u} : HasSubset (Set α) where
  Subset s t := ∀ ⦃x⦄, x ∈ s → x ∈ t

namespace Set

def univ {α : Type u} : Set α := fun _ => True

def range {α : Type u} {β : Type v} (f : α → β) : Set β :=
  fun y => ∃ x, f x = y

def singleton {α : Type u} (a : α) : Set α :=
  fun x => x = a

@[simp] theorem mem_singleton {α : Type u} {a : α} (x : α) : x ∈ (singleton a) ↔ x = a :=
  Iff.rfl

@[simp] theorem mem_singleton_iff {α : Type u} {a x : α} : x ∈ (singleton a) ↔ x = a :=
  Iff.rfl

/-- Constructive finiteness: `s` is covered by a finite list of representatives. -/
def Finite {α : Type u} (s : Set α) : Prop :=
  ∃ n : Nat, ∃ f : Fin n → α, ∀ x, x ∈ s → ∃ i : Fin n, f i = x

end Set

/-!
### Minimal `Preorder`

We avoid importing Std/Mathlib order theory. This is just enough for "time shots".
-/
class Preorder (A : Type uQ) extends LE A where
  le_refl : ∀ a : A, a ≤ a
  le_trans : ∀ {a b c : A}, a ≤ b → b ≤ c → a ≤ c

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
  fun x => obs x = target_obs h

/-- The type of points in the fiber above `h`. -/
abbrev FiberPt {S V : Type w} (obs : S → V) (target_obs : P → V) (h : P) : Type w :=
  { x : S // Fiber (P := P) obs target_obs h x }

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
  constructor
  · intro hp
    exact ⟨hp, x.2, y.2⟩
  · intro hdoc
    exact hdoc.1

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


end WithHistoryGraph

end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
Auto-generated: `#print axioms` for each non-private `theorem`/`lemma` in this file.
-/
#print axioms PrimitiveHolonomy.hidden_ne_of_ne
#print axioms PrimitiveHolonomy.transport_eq_transportDoc
#print axioms PrimitiveHolonomy.holonomy_congr
#print axioms PrimitiveHolonomy.holonomy_def
/- AXIOM_AUDIT_END -/
