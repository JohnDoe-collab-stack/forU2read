/-!
# Self-contained multi-interface algebra and dynamic profile

This file is intentionally standalone: it imports no file from the project and no external module.
It reconstructs, in one place, the finite multi-interface algebra and the minimal dynamic vocabulary
needed for the end-to-end non-descent theorem.

Constructive only.
-/

namespace PrimitiveHolonomy
namespace Standalone

universe p u v w y a

/-- Minimal 2-structure for histories, reconstructed locally. -/
class HistoryGraph (P : Type u) where
  Path : P → P → Type v
  Deformation : {h k : P} → Path h k → Path h k → Prop
  idPath (h : P) : Path h h
  compPath {h k l : P} : Path h k → Path k l → Path h l

/-- Constructive relation type. -/
def Relation (A : Type u) (B : Type v) := A → B → Prop

/-- Pointwise equivalence of relations. -/
def RelEq {A : Type u} {B : Type v} (R S : Relation A B) : Prop :=
  ∀ x y, R x y ↔ S x y

/-- Relational composition. -/
def relComp {A : Type u} {B : Type v} {C : Type w}
    (R : Relation A B) (S : Relation B C) : Relation A C :=
  fun a c => ∃ b, R a b ∧ S b c

/-- Relational identity. -/
def relId {A : Type u} : Relation A A :=
  fun x y => x = y

/-- Relational semantics for histories, reconstructed locally. -/
structure Semantics (P : Type u) [HistoryGraph P] (S : Type w) where
  sem : {h k : P} → HistoryGraph.Path h k → Relation S S
  sem_id : ∀ h, RelEq (sem (HistoryGraph.idPath h)) relId
  sem_comp : ∀ {h k l} (p : HistoryGraph.Path h k) (q : HistoryGraph.Path k l),
    RelEq (sem (HistoryGraph.compPath p q)) (relComp (sem p) (sem q))

/-- Fiber of ambiguity above `h`. -/
def Fiber {P : Type u} {S V : Type w} (obs : S → V) (target_obs : P → V) (h : P) : S → Prop :=
  fun x => obs x = target_obs h

/-- Point in the fiber above `h`. -/
abbrev FiberPt {P : Type u} {S V : Type w}
    (obs : S → V) (target_obs : P → V) (h : P) : Type w :=
  { x : S // Fiber (P := P) obs target_obs h x }

section WithHistoryGraph

variable {P : Type p} [HistoryGraph P]

/-- Transport restricted to fibers. -/
def Transport {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (p : HistoryGraph.Path h k) :
    Relation (FiberPt (P := P) obs target_obs h) (FiberPt (P := P) obs target_obs k) :=
  fun x y => sem.sem p x.1 y.1

/-- Compatibility with the observed value at the end of a step. -/
def Compatible {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (p : HistoryGraph.Path h k)
    (x : FiberPt (P := P) obs target_obs h) : Prop :=
  ∃ y : FiberPt (P := P) obs target_obs k, Transport sem obs target_obs p x y

/-- A step separates the current fiber when compatibility differs on two fiber points. -/
def StepSeparatesFiber {S V : Type w} (sem : Semantics P S) (obs : S → V)
    (target_obs : P → V) {h k : P} (step : HistoryGraph.Path h k) : Prop :=
  ∃ x x' : FiberPt (P := P) obs target_obs h,
    x ≠ x' ∧ Compatible (P := P) sem obs target_obs step x ∧
      ¬ Compatible (P := P) sem obs target_obs step x'

/-- A finite refining lift for one compatibility truth. -/
structure RefiningLiftData {S V : Type w} (sem : Semantics P S) (obs : S → V)
    (target_obs : P → V) (h : P) {k : P} (step : HistoryGraph.Path h k) (n : Nat) where
  extObs : FiberPt (P := P) obs target_obs h → V × Fin n
  predFin : Fin n → Prop
  factors : ∀ x : FiberPt (P := P) obs target_obs h,
    Compatible (P := P) sem obs target_obs step x ↔ predFin ((extObs x).2)

/-- Existence of a finite refining lift. -/
def RefiningLift {S V : Type w} (sem : Semantics P S) (obs : S → V)
    (target_obs : P → V) (h : P) {k : P} (step : HistoryGraph.Path h k) (n : Nat) : Prop :=
  ∃ _L : RefiningLiftData (P := P) sem obs target_obs h step n, True

/-- Exact finite compatibility dimension for a single step. -/
def CompatDimEq {S V : Type w} (sem : Semantics P S) (obs : S → V)
    (target_obs : P → V) {h k : P} (step : HistoryGraph.Path h k) (n : Nat) : Prop :=
  RefiningLift (P := P) sem obs target_obs h step n ∧
    ∀ m : Nat, m < n → ¬ RefiningLift (P := P) sem obs target_obs h step m

/-- Exact dimension yields a refining lift at that dimension. -/
theorem refiningLift_of_compatDimEq {S V : Type w} (sem : Semantics P S) (obs : S → V)
    (target_obs : P → V) {h k : P} (step : HistoryGraph.Path h k) (n : Nat) :
    CompatDimEq (P := P) sem obs target_obs step n →
      RefiningLift (P := P) sem obs target_obs h step n := by
  intro hDim
  exact hDim.1

/-- Exact dimension excludes every smaller refining lift. -/
theorem no_smaller_refiningLift_of_compatDimEq {S V : Type w} (sem : Semantics P S)
    (obs : S → V) (target_obs : P → V) {h k : P} (step : HistoryGraph.Path h k)
    (n : Nat) :
    CompatDimEq (P := P) sem obs target_obs step n →
      ∀ m : Nat, m < n → ¬ RefiningLift (P := P) sem obs target_obs h step m := by
  intro hDim
  exact hDim.2

end WithHistoryGraph

namespace MultiInterface

variable {J : Type u} {S : Type v} {V : Type w} {Y : Type y}
/-!
## Constructive finite counting by explicit lists

The numerical `rho` is computed from explicit finite enumerations. This avoids quotienting pairs
and avoids proof-carrying finite indices.
-/

/-- Constructive finite sum over a list of natural numbers. -/
def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

/-- Constructive count over an explicit finite list with explicit decidability data. -/
def countListD {A : Type a} (xs : List A) (P : A → Prop)
    (decP : ∀ x, Decidable (P x)) : Nat :=
  match xs with
  | [] => 0
  | x :: xs =>
      match decP x with
      | isTrue _ => Nat.succ (countListD xs P decP)
      | isFalse _ => countListD xs P decP

/-- Constructive count over an explicit finite list. -/
def countList {A : Type a} (xs : List A) (P : A → Prop) [∀ x, Decidable (P x)] : Nat :=
  countListD xs P (fun _ => inferInstance)

/-- Structural "all entries fail `P`", avoiding membership elimination. -/
inductive AllFalse {A : Type a} (P : A → Prop) : List A → Prop
  | nil : AllFalse P []
  | cons {a : A} {xs : List A} : ¬ P a → AllFalse P xs → AllFalse P (a :: xs)

theorem countListD_eq_zero_of_allFalse
    {A : Type a} (xs : List A) (P : A → Prop) (decP : ∀ x, Decidable (P x)) :
    AllFalse P xs → countListD xs P decP = 0 := by
  intro h
  induction xs with
  | nil =>
      rfl
  | cons a xs ih =>
      cases h with
      | cons hHead hTail =>
          unfold countListD
          cases hDec : decP a with
          | isTrue hPa =>
              exact False.elim (hHead hPa)
          | isFalse _hNotPa =>
              exact ih hTail

theorem countList_eq_zero_of_allFalse
    {A : Type a} (xs : List A) (P : A → Prop) [∀ x, Decidable (P x)] :
    AllFalse P xs → countList xs P = 0 := by
  exact countListD_eq_zero_of_allFalse xs P (fun _ => inferInstance)

/--
Type-valued membership in an explicit list.

This is intentionally not `List.Mem`: it lets the finite bridge stay quotient-free and avoid
propositional extensionality in audited declarations.
-/
inductive InList {A : Type a} (a : A) : List A → Prop
  | head {xs : List A} : InList a (a :: xs)
  | tail {b : A} {xs : List A} : InList a xs → InList a (b :: xs)

theorem allFalse_not_of_inList
    {A : Type a} {P : A → Prop} {a : A} {xs : List A} :
    AllFalse P xs → InList a xs → ¬ P a := by
  intro hAll hIn
  induction hAll with
  | nil =>
      cases hIn
  | cons hHead _hTail ih =>
      cases hIn with
      | head =>
          exact hHead
      | tail hTailIn =>
          exact ih hTailIn

/-- Boolean count over an explicit list. This is the computable core used by `rho`. -/
def countListBool {A : Type a} : List A → (A → Bool) → Nat
  | [], _b => 0
  | a :: xs, b =>
      match b a with
      | true => Nat.succ (countListBool xs b)
      | false => countListBool xs b

/-- Structural statement that a boolean predicate is false on every listed element. -/
inductive AllFalseBool {A : Type a} (b : A → Bool) : List A → Prop
  | nil : AllFalseBool b []
  | cons {a : A} {xs : List A} :
      b a = false → AllFalseBool b xs → AllFalseBool b (a :: xs)

theorem countListBool_eq_zero_of_allFalseBool
    {A : Type a} (xs : List A) (b : A → Bool) :
    AllFalseBool b xs → countListBool xs b = 0 := by
  intro h
  induction xs with
  | nil =>
      rfl
  | cons a xs ih =>
      cases h with
      | cons hHead hTail =>
          unfold countListBool
          rw [hHead]
          exact ih hTail

theorem allFalseBool_false_of_inList
    {A : Type a} {b : A → Bool} {a : A} {xs : List A} :
    AllFalseBool b xs → InList a xs → b a = false := by
  intro hAll hIn
  induction hAll with
  | nil =>
      cases hIn
  | cons hHead _hTail ih =>
      cases hIn with
      | head =>
          exact hHead
      | tail hTailIn =>
          exact ih hTailIn

theorem countListBool_pos_of_inList_true
    {A : Type a} (xs : List A) (b : A → Bool) (a : A) :
    InList a xs → b a = true → 0 < countListBool xs b := by
  induction xs with
  | nil =>
      intro hIn _hTrue
      cases hIn
  | cons c xs ih =>
      intro hIn hTrue
      cases hIn with
      | head =>
          unfold countListBool
          cases hba : b a with
          | false =>
              have hContr : false = true := hba.symm.trans hTrue
              cases hContr
          | true =>
              exact Nat.succ_pos _
      | tail hTail =>
          have hPos : 0 < countListBool xs b := ih hTail hTrue
          unfold countListBool
          cases b c with
          | false =>
              exact hPos
          | true =>
              exact Nat.succ_pos _

theorem exists_inList_true_of_countListBool_pos
    {A : Type a} (xs : List A) (b : A → Bool) :
    0 < countListBool xs b → ∃ a : A, InList a xs ∧ b a = true := by
  induction xs with
  | nil =>
      intro h
      unfold countListBool at h
      exact False.elim (Nat.not_lt_zero 0 h)
  | cons x xs ih =>
      intro h
      unfold countListBool at h
      cases hb : b x with
      | false =>
          rw [hb] at h
          rcases ih h with ⟨a, hIn, hTrue⟩
          exact ⟨a, InList.tail hIn, hTrue⟩
      | true =>
          exact ⟨x, InList.head, hb⟩

/--
Monotonicity of boolean counts on an explicit list.

If every listed `b`-hit is also a `c`-hit, then the `b` count is bounded by the
`c` count.
-/
theorem countListBool_le_of_true_imp
    {A : Type a} (xs : List A) (b c : A → Bool) :
    (∀ x : A, InList x xs → b x = true → c x = true) →
      countListBool xs b ≤ countListBool xs c := by
  induction xs with
  | nil =>
      intro _h
      exact Nat.le_refl _
  | cons x xs ih =>
      intro h
      unfold countListBool
      cases hb : b x with
      | false =>
          cases hc : c x with
          | false =>
              exact ih (fun y hy hby => h y (InList.tail hy) hby)
          | true =>
              exact Nat.le_trans
                (ih (fun y hy hby => h y (InList.tail hy) hby))
                (Nat.le_succ _)
      | true =>
          have hcTrue : c x = true := h x InList.head hb
          cases hc : c x with
          | false =>
              rw [hc] at hcTrue
              cases hcTrue
          | true =>
              exact Nat.succ_le_succ
                (ih (fun y hy hby => h y (InList.tail hy) hby))

/--
Strict monotonicity of boolean counts on an explicit list.

If every listed `b`-hit is a `c`-hit, and at least one listed element is a
`c`-hit but not a `b`-hit, then the `b` count is strictly smaller.
-/
theorem countListBool_lt_of_exists_false_true
    {A : Type a} (xs : List A) (b c : A → Bool) :
    (∀ x : A, InList x xs → b x = true → c x = true) →
      (∃ x : A, InList x xs ∧ b x = false ∧ c x = true) →
        countListBool xs b < countListBool xs c := by
  induction xs with
  | nil =>
      intro _hImp hExists
      rcases hExists with ⟨x, hIn, _hb, _hc⟩
      cases hIn
  | cons x xs ih =>
      intro hImp hExists
      let hImpTail : ∀ y : A, InList y xs → b y = true → c y = true :=
        fun y hy hby => hImp y (InList.tail hy) hby
      unfold countListBool
      cases hb : b x with
      | false =>
          cases hc : c x with
          | false =>
              refine ih hImpTail ?_
              rcases hExists with ⟨y, hIn, hbyFalse, hcyTrue⟩
              cases hIn with
              | head =>
                  rw [hc] at hcyTrue
                  cases hcyTrue
              | tail hTail =>
                  exact ⟨y, hTail, hbyFalse, hcyTrue⟩
          | true =>
              exact Nat.lt_succ_of_le
                (countListBool_le_of_true_imp xs b c hImpTail)
      | true =>
          have hcTrue : c x = true := hImp x InList.head hb
          cases hc : c x with
          | false =>
              rw [hc] at hcTrue
              cases hcTrue
          | true =>
              refine Nat.succ_lt_succ (ih hImpTail ?_)
              rcases hExists with ⟨y, hIn, hbyFalse, hcyTrue⟩
              cases hIn with
              | head =>
                  rw [hb] at hbyFalse
                  cases hbyFalse
              | tail hTail =>
                  exact ⟨y, hTail, hbyFalse, hcyTrue⟩

/--
Witness extraction from a strict boolean-count inequality under pointwise implication.
-/
theorem exists_false_true_of_countListBool_lt
    {A : Type a} (xs : List A) (b c : A → Bool) :
    (∀ x : A, InList x xs → b x = true → c x = true) →
      countListBool xs b < countListBool xs c →
        ∃ x : A, InList x xs ∧ b x = false ∧ c x = true := by
  induction xs with
  | nil =>
      intro _hImp hLt
      unfold countListBool at hLt
      exact False.elim (Nat.lt_irrefl 0 hLt)
  | cons x xs ih =>
      intro hImp hLt
      let hImpTail : ∀ y : A, InList y xs → b y = true → c y = true :=
        fun y hy hby => hImp y (InList.tail hy) hby
      unfold countListBool at hLt
      cases hb : b x with
      | false =>
          rw [hb] at hLt
          cases hc : c x with
          | false =>
              rw [hc] at hLt
              exact
                let hTail : countListBool xs b < countListBool xs c := hLt
                match ih hImpTail hTail with
                | ⟨y, hIn, hbyFalse, hcyTrue⟩ =>
                    ⟨y, InList.tail hIn, hbyFalse, hcyTrue⟩
          | true =>
              rw [hc] at hLt
              exact ⟨x, InList.head, hb, hc⟩
      | true =>
          rw [hb] at hLt
          have hcTrue : c x = true := hImp x InList.head hb
          cases hc : c x with
          | false =>
              rw [hc] at hcTrue
              cases hcTrue
          | true =>
              rw [hc] at hLt
              have hTail : countListBool xs b < countListBool xs c :=
                Nat.lt_of_succ_lt_succ hLt
              match ih hImpTail hTail with
              | ⟨y, hIn, hbyFalse, hcyTrue⟩ =>
                  exact ⟨y, InList.tail hIn, hbyFalse, hcyTrue⟩

def inList_append_left
    {A : Type a} {a : A} {xs ys : List A} :
    InList a xs → InList a (xs ++ ys)
  | InList.head => InList.head
  | InList.tail hTail => InList.tail (inList_append_left hTail)

def inList_append_right
    {A : Type a} {a : A} (xs : List A) {ys : List A} :
    InList a ys → InList a (xs ++ ys) :=
  match xs with
  | [] => fun h => h
  | _ :: xs => fun h => InList.tail (inList_append_right xs h)

theorem allFalse_append
    {A : Type a} {P : A → Prop} {xs ys : List A} :
    AllFalse P xs → AllFalse P ys → AllFalse P (xs ++ ys) := by
  intro hXs hYs
  induction hXs with
  | nil =>
      exact hYs
  | cons hHead _hTail ih =>
      exact AllFalse.cons hHead ih

/-- A subfamily of interfaces, represented constructively as a predicate on indices. -/
abbrev Subfamily (J : Type u) : Type u := J → Prop

/-- `K` is included in `I`. -/
def Subfamily.Subset (K I : Subfamily J) : Prop :=
  ∀ ⦃j : J⦄, K j → I j

/-- `K` is a proper subfamily of `I`, witnessed without propositional extensionality. -/
def Subfamily.Proper (K I : Subfamily J) : Prop :=
  Subfamily.Subset K I ∧ ∃ j : J, I j ∧ ¬ K j

/-- Add one interface to a subfamily, constructively. -/
def Subfamily.Insert (I : Subfamily J) (j0 : J) : Subfamily J :=
  fun j => I j ∨ j = j0

/-- Remove one interface from a subfamily, constructively. -/
def Subfamily.Remove (I : Subfamily J) (j0 : J) : Subfamily J :=
  fun j => I j ∧ j ≠ j0

/-- A subfamily is included in the result of inserting one interface. -/
theorem Subfamily.subset_insert (I : Subfamily J) (j0 : J) :
    Subfamily.Subset I (Subfamily.Insert I j0) := by
  intro j hj
  exact Or.inl hj

/-- Removing one interface gives a subfamily of the original family. -/
theorem Subfamily.remove_subset (I : Subfamily J) (j0 : J) :
    Subfamily.Subset (Subfamily.Remove I j0) I := by
  intro j hj
  exact hj.1

/-- Two states are indistinguishable by every interface in `I`. -/
def JointSame (obs : J → S → V) (I : Subfamily J) (x y : S) : Prop :=
  ∀ j : J, I j → obs j x = obs j y

/-- Target distinction required by `sigma`. -/
def RequiredDistinction (sigma : S → Y) (x y : S) : Prop :=
  sigma x ≠ sigma y

/-- Distinctions required by `sigma` but lost by interface `j`. -/
def Loss (obs : J → S → V) (sigma : S → Y) (j : J) (x y : S) : Prop :=
  RequiredDistinction sigma x y ∧ obs j x = obs j y

/-- Distinctions required by `sigma` and separated by interface `j`. -/
def InterfaceSeparates (obs : J → S → V) (sigma : S → Y) (j : J) (x y : S) : Prop :=
  RequiredDistinction sigma x y ∧ obs j x ≠ obs j y

/--
Residual common to a subfamily `I`: a required distinction that every interface in `I` loses.

For `I = ∅`, this reduces to all required distinctions, because the universal condition is vacuous.
-/
def Residual (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (x y : S) : Prop :=
  RequiredDistinction sigma x y ∧ JointSame obs I x y

/-- A subfamily has empty residual: no required target distinction is still jointly lost. -/
def ResidualEmpty (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) : Prop :=
  ∀ x y : S, ¬ Residual obs sigma I x y

/-- Nonempty residual, as a constructive witness. -/
def ResidualNonempty (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) : Prop :=
  ∃ x y : S, Residual obs sigma I x y

/--
Local usefulness of an interface after a current subfamily:
there is a currently residual distinction that the new interface separates.
-/
def LocallyUsefulInterface
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (j : J) : Prop :=
  ∃ x y : S, Residual obs sigma I x y ∧ InterfaceSeparates obs sigma j x y

/--
Local redundancy of an interface after a current subfamily:
it loses every distinction that is already residual for the current subfamily.
-/
def LocallyRedundantInterface
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (j : J) : Prop :=
  ∀ x y : S, Residual obs sigma I x y → Loss obs sigma j x y

/--
Two interfaces have the same loss profile on the current residual.
This is a pointwise, quotient-free profile equality.
-/
def SameLossProfileOn
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (j k : J) : Prop :=
  ∀ x y : S, Residual obs sigma I x y →
    (Loss obs sigma j x y ↔ Loss obs sigma k x y)

/--
Two interfaces are loss-profile separated on the current residual when one loses a residual
distinction that the other separates.
-/
def LossProfileSeparated
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (j k : J) : Prop :=
  ∃ x y : S, Residual obs sigma I x y ∧
    ((Loss obs sigma j x y ∧ InterfaceSeparates obs sigma k x y) ∨
      (Loss obs sigma k x y ∧ InterfaceSeparates obs sigma j x y))

/--
A residual for `I \ {j0}` is exactly a required distinction lost by every other interface in `I`.
-/
theorem residual_remove_iff_required_and_other_losses
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (j0 : J) (x y : S) :
    Residual obs sigma (Subfamily.Remove I j0) x y ↔
      RequiredDistinction sigma x y ∧
        ∀ j : J, I j → j ≠ j0 → obs j x = obs j y := by
  constructor
  · intro hRes
    exact ⟨hRes.1, fun j hjI hjNe => hRes.2 j ⟨hjI, hjNe⟩⟩
  · intro h
    exact ⟨h.1, fun j hj => h.2 j hj.1 hj.2⟩

/--
Residual after inserting one interface is exactly the old residual restricted to the
distinctions that the inserted interface also loses.
-/
theorem residual_insert_iff_residual_and_loss
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (j0 : J) (x y : S) :
    Residual obs sigma (Subfamily.Insert I j0) x y ↔
      Residual obs sigma I x y ∧ Loss obs sigma j0 x y := by
  constructor
  · intro hRes
    refine ⟨?_, ?_⟩
    · exact ⟨hRes.1, fun j hj => hRes.2 j (Or.inl hj)⟩
    · exact ⟨hRes.1, hRes.2 j0 (Or.inr rfl)⟩
  · intro h
    refine ⟨h.1.1, ?_⟩
    intro j hj
    cases hj with
    | inl hjI =>
        exact h.1.2 j hjI
    | inr hEq =>
        cases hEq
        exact h.2.2

/--
An interface is locally useful exactly when inserting it removes at least one currently
residual distinction.
-/
theorem locallyUsefulInterface_iff_exists_residual_not_insert
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (j0 : J) :
    LocallyUsefulInterface obs sigma I j0 ↔
      ∃ x y : S, Residual obs sigma I x y ∧
        ¬ Residual obs sigma (Subfamily.Insert I j0) x y := by
  constructor
  · intro hUseful
    rcases hUseful with ⟨x, y, hResI, hSep⟩
    refine ⟨x, y, hResI, ?_⟩
    intro hInserted
    have hLoss : Loss obs sigma j0 x y :=
      (residual_insert_iff_residual_and_loss obs sigma I j0 x y).mp hInserted |>.2
    exact hSep.2 hLoss.2
  · intro hRemoved
    rcases hRemoved with ⟨x, y, hResI, hNotInserted⟩
    refine ⟨x, y, hResI, ?_⟩
    refine ⟨hResI.1, ?_⟩
    intro hEq
    have hLoss : Loss obs sigma j0 x y := ⟨hResI.1, hEq⟩
    exact hNotInserted
      ((residual_insert_iff_residual_and_loss obs sigma I j0 x y).mpr
        ⟨hResI, hLoss⟩)

/--
An interface is locally redundant exactly when insertion leaves the residual relation
pointwise unchanged.
-/
theorem locallyRedundantInterface_iff_insert_residual_iff
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (j0 : J) :
    LocallyRedundantInterface obs sigma I j0 ↔
      ∀ x y : S,
        (Residual obs sigma (Subfamily.Insert I j0) x y ↔
          Residual obs sigma I x y) := by
  constructor
  · intro hRed x y
    constructor
    · intro hInserted
      exact (residual_insert_iff_residual_and_loss obs sigma I j0 x y).mp hInserted |>.1
    · intro hResI
      exact (residual_insert_iff_residual_and_loss obs sigma I j0 x y).mpr
        ⟨hResI, hRed x y hResI⟩
  · intro hSame x y hResI
    have hInserted : Residual obs sigma (Subfamily.Insert I j0) x y :=
      (hSame x y).mpr hResI
    exact (residual_insert_iff_residual_and_loss obs sigma I j0 x y).mp hInserted |>.2

/-- Same loss profile is reflexive on every residual. -/
theorem sameLossProfileOn_refl
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (j : J) :
    SameLossProfileOn obs sigma I j j := by
  intro x y _hRes
  constructor
  · intro h
    exact h
  · intro h
    exact h

/--
Closure of `sigma` by a subfamily `I`, stated quotient-free:
jointly indistinguishable states have equal target value.
-/
def Closed (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) : Prop :=
  ∀ x y : S, JointSame obs I x y → sigma x = sigma y

/-!
## Finite numerical residual

The numerical `rho` is defined from explicit lists of states and interfaces.

It counts ordered listed pairs of states whose target distinction is still lost by all listed
interfaces. If the state list is exhaustive, `rho = 0` is equivalent to residual emptiness.
-/

def JointSameList (obs : J → S → V) : List J → S → S → Prop
  | [], _x, _y => True
  | j :: js, x, y => obs j x = obs j y ∧ JointSameList obs js x y

def ResidualList (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (x y : S) : Prop :=
  RequiredDistinction sigma x y ∧ JointSameList obs interfaces x y

def eqBool [DecidableEq V] (x y : V) : Bool :=
  match (inferInstance : Decidable (x = y)) with
  | isTrue _ => true
  | isFalse _ => false

def neqBool [DecidableEq Y] (x y : Y) : Bool :=
  match (inferInstance : Decidable (x = y)) with
  | isTrue _ => false
  | isFalse _ => true

def JointSameListBool [DecidableEq V]
    (obs : J → S → V) : List J → S → S → Bool
  | [], _x, _y => true
  | j :: js, x, y =>
      match eqBool (obs j x) (obs j y) with
      | true => JointSameListBool obs js x y
      | false => false

def ResidualListBool [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (x y : S) : Bool :=
  match neqBool (sigma x) (sigma y) with
  | true => JointSameListBool obs interfaces x y
  | false => false

/-- Boolean witness that interface `j` loses the required distinction `(x,y)`. -/
def LossBool [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y) (j : J) (x y : S) : Bool :=
  match neqBool (sigma x) (sigma y) with
  | true => eqBool (obs j x) (obs j y)
  | false => false

/-- Boolean witness that interface `j` separates the required distinction `(x,y)`. -/
def InterfaceSeparatesBool [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y) (j : J) (x y : S) : Bool :=
  match neqBool (sigma x) (sigma y) with
  | true =>
      match eqBool (obs j x) (obs j y) with
      | true => false
      | false => true
  | false => false

/-- Incidence count: how many listed interfaces lose the distinction `(x,y)`. -/
def lossIncidence
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (x y : S) : Nat :=
  countListBool interfaces (fun j => LossBool obs sigma j x y)

/-- Incidence count: how many listed interfaces separate the distinction `(x,y)`. -/
def separationIncidence
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (x y : S) : Nat :=
  countListBool interfaces (fun j => InterfaceSeparatesBool obs sigma j x y)

theorem eq_of_eqBool_true
    [DecidableEq V] {x y : V} :
    eqBool x y = true → x = y := by
  unfold eqBool
  cases (inferInstance : Decidable (x = y)) with
  | isTrue hEq =>
      intro _h
      exact hEq
  | isFalse hNe =>
      intro h
      cases h

theorem eqBool_true_of_eq
    [DecidableEq V] {x y : V} :
    x = y → eqBool x y = true := by
  intro hEq
  unfold eqBool
  cases (inferInstance : Decidable (x = y)) with
  | isTrue _h =>
      rfl
  | isFalse hNe =>
      exact False.elim (hNe hEq)

theorem ne_of_eqBool_false
    [DecidableEq V] {x y : V} :
    eqBool x y = false → x ≠ y := by
  unfold eqBool
  cases (inferInstance : Decidable (x = y)) with
  | isTrue _hEq =>
      intro h
      cases h
  | isFalse hNe =>
      intro _h
      exact hNe

theorem eqBool_false_of_ne
    [DecidableEq V] {x y : V} :
    x ≠ y → eqBool x y = false := by
  intro hNe
  unfold eqBool
  cases (inferInstance : Decidable (x = y)) with
  | isTrue hEq =>
      exact False.elim (hNe hEq)
  | isFalse _hNe =>
      rfl

theorem requiredDistinction_of_neqBool_true
    [DecidableEq Y] {x y : S} (sigma : S → Y) :
    neqBool (sigma x) (sigma y) = true → RequiredDistinction sigma x y := by
  unfold neqBool RequiredDistinction
  cases (inferInstance : Decidable (sigma x = sigma y)) with
  | isTrue _hEq =>
      intro h
      cases h
  | isFalse hNe =>
      intro _h
      exact hNe

theorem neqBool_true_of_requiredDistinction
    [DecidableEq Y] {x y : S} (sigma : S → Y) :
    RequiredDistinction sigma x y → neqBool (sigma x) (sigma y) = true := by
  intro hReq
  unfold RequiredDistinction at hReq
  unfold neqBool
  cases (inferInstance : Decidable (sigma x = sigma y)) with
  | isTrue hEq =>
      exact False.elim (hReq hEq)
  | isFalse _hNe =>
      rfl

theorem loss_of_lossBool_true
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y) (j : J) (x y : S) :
    LossBool obs sigma j x y = true → Loss obs sigma j x y := by
  intro h
  unfold LossBool at h
  cases hReq : neqBool (sigma x) (sigma y) with
  | false =>
      rw [hReq] at h
      cases h
  | true =>
      rw [hReq] at h
      exact ⟨requiredDistinction_of_neqBool_true sigma hReq, eq_of_eqBool_true h⟩

theorem lossBool_true_of_loss
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y) (j : J) (x y : S) :
    Loss obs sigma j x y → LossBool obs sigma j x y = true := by
  intro hLoss
  unfold LossBool
  have hReq : neqBool (sigma x) (sigma y) = true :=
    neqBool_true_of_requiredDistinction sigma hLoss.1
  rw [hReq]
  exact eqBool_true_of_eq hLoss.2

theorem interfaceSeparates_of_bool_true
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y) (j : J) (x y : S) :
    InterfaceSeparatesBool obs sigma j x y = true →
      InterfaceSeparates obs sigma j x y := by
  intro h
  unfold InterfaceSeparatesBool at h
  cases hReq : neqBool (sigma x) (sigma y) with
  | false =>
      rw [hReq] at h
      cases h
  | true =>
      rw [hReq] at h
      cases hEq : eqBool (obs j x) (obs j y) with
      | true =>
          rw [hEq] at h
          cases h
      | false =>
          exact ⟨requiredDistinction_of_neqBool_true sigma hReq, ne_of_eqBool_false hEq⟩

theorem bool_true_of_interfaceSeparates
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y) (j : J) (x y : S) :
    InterfaceSeparates obs sigma j x y →
      InterfaceSeparatesBool obs sigma j x y = true := by
  intro hSep
  unfold InterfaceSeparatesBool
  have hReq : neqBool (sigma x) (sigma y) = true :=
    neqBool_true_of_requiredDistinction sigma hSep.1
  rw [hReq]
  have hNe : eqBool (obs j x) (obs j y) = false :=
    eqBool_false_of_ne hSep.2
  rw [hNe]

theorem lossIncidence_pos_iff_exists_loss
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (x y : S) :
    0 < lossIncidence obs sigma interfaces x y ↔
      ∃ j : J, InList j interfaces ∧ Loss obs sigma j x y := by
  constructor
  · intro hPos
    unfold lossIncidence at hPos
    rcases exists_inList_true_of_countListBool_pos
        interfaces
        (fun j => LossBool obs sigma j x y)
        hPos with
      ⟨j, hIn, hTrue⟩
    exact ⟨j, hIn, loss_of_lossBool_true obs sigma j x y hTrue⟩
  · intro hExists
    rcases hExists with ⟨j, hIn, hLoss⟩
    unfold lossIncidence
    exact countListBool_pos_of_inList_true
      interfaces
      (fun k => LossBool obs sigma k x y)
      j hIn (lossBool_true_of_loss obs sigma j x y hLoss)

theorem separationIncidence_pos_iff_exists_interfaceSeparates
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (x y : S) :
    0 < separationIncidence obs sigma interfaces x y ↔
      ∃ j : J, InList j interfaces ∧ InterfaceSeparates obs sigma j x y := by
  constructor
  · intro hPos
    unfold separationIncidence at hPos
    rcases exists_inList_true_of_countListBool_pos
        interfaces
        (fun j => InterfaceSeparatesBool obs sigma j x y)
        hPos with
      ⟨j, hIn, hTrue⟩
    exact ⟨j, hIn, interfaceSeparates_of_bool_true obs sigma j x y hTrue⟩
  · intro hExists
    rcases hExists with ⟨j, hIn, hSep⟩
    unfold separationIncidence
    exact countListBool_pos_of_inList_true
      interfaces
      (fun k => InterfaceSeparatesBool obs sigma k x y)
      j hIn (bool_true_of_interfaceSeparates obs sigma j x y hSep)

theorem jointSameList_of_bool_true
    [DecidableEq V]
    (obs : J → S → V) (interfaces : List J) (x y : S) :
    JointSameListBool obs interfaces x y = true → JointSameList obs interfaces x y := by
  induction interfaces with
  | nil =>
      intro _h
      exact True.intro
  | cons j js ih =>
      intro h
      unfold JointSameListBool at h
      cases hEq : eqBool (obs j x) (obs j y) with
      | false =>
          rw [hEq] at h
          cases h
      | true =>
          rw [hEq] at h
          exact ⟨eq_of_eqBool_true hEq, ih h⟩

theorem bool_true_of_jointSameList
    [DecidableEq V]
    (obs : J → S → V) (interfaces : List J) (x y : S) :
    JointSameList obs interfaces x y → JointSameListBool obs interfaces x y = true := by
  induction interfaces with
  | nil =>
      intro _h
      rfl
  | cons j js ih =>
      intro h
      unfold JointSameListBool
      have hEq : eqBool (obs j x) (obs j y) = true := eqBool_true_of_eq h.1
      rw [hEq]
      exact ih h.2

theorem residualList_of_bool_true
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (x y : S) :
    ResidualListBool obs sigma interfaces x y = true →
      ResidualList obs sigma interfaces x y := by
  intro h
  unfold ResidualListBool at h
  cases hReq : neqBool (sigma x) (sigma y) with
  | false =>
      rw [hReq] at h
      cases h
  | true =>
      rw [hReq] at h
      exact ⟨requiredDistinction_of_neqBool_true sigma hReq,
        jointSameList_of_bool_true obs interfaces x y h⟩

theorem bool_true_of_residualList
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (x y : S) :
    ResidualList obs sigma interfaces x y →
      ResidualListBool obs sigma interfaces x y = true := by
  intro h
  unfold ResidualListBool
  have hReq : neqBool (sigma x) (sigma y) = true :=
    neqBool_true_of_requiredDistinction sigma h.1
  rw [hReq]
  exact bool_true_of_jointSameList obs interfaces x y h.2

theorem allFalseBool_of_allFalse_residualList
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y) (interfaces : List J)
    (pairs : List (S × S)) :
    AllFalse (fun xy : S × S => ResidualList obs sigma interfaces xy.1 xy.2) pairs →
      AllFalseBool
        (fun xy : S × S => ResidualListBool obs sigma interfaces xy.1 xy.2)
        pairs := by
  intro h
  induction pairs with
  | nil =>
      exact AllFalseBool.nil
  | cons xy pairs ih =>
      cases h with
      | cons hHead hTail =>
          refine AllFalseBool.cons ?_ (ih hTail)
          cases hBool : ResidualListBool obs sigma interfaces xy.1 xy.2 with
          | false =>
              rfl
          | true =>
              have hRes : ResidualList obs sigma interfaces xy.1 xy.2 :=
                residualList_of_bool_true obs sigma interfaces xy.1 xy.2 hBool
              exact False.elim (hHead hRes)

def decidableJointSameList
    [DecidableEq V]
    (obs : J → S → V) (interfaces : List J) (x y : S) :
    Decidable (JointSameList obs interfaces x y) :=
  match interfaces with
  | [] => isTrue True.intro
  | j :: js =>
      match (inferInstance : Decidable (obs j x = obs j y)),
          decidableJointSameList obs js x y with
      | isTrue hEq, isTrue hTail =>
          isTrue ⟨hEq, hTail⟩
      | isTrue _hEq, isFalse hNotTail =>
          isFalse (fun h => hNotTail h.2)
      | isFalse hNe, _ =>
          isFalse (fun h => hNe h.1)

def decidableResidualList
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y) (interfaces : List J)
    (x y : S) :
    Decidable (ResidualList obs sigma interfaces x y) := by
  have decReq : Decidable (RequiredDistinction sigma x y) := by
    dsimp [RequiredDistinction]
    exact inferInstance
  cases decReq with
  | isTrue hReq =>
      cases decidableJointSameList obs interfaces x y with
      | isTrue hJoint =>
          exact isTrue ⟨hReq, hJoint⟩
      | isFalse hNotJoint =>
          refine isFalse ?_
          intro hRes
          exact hNotJoint hRes.2
  | isFalse hNotReq =>
      refine isFalse ?_
      intro hRes
      exact hNotReq hRes.1

def pairWith (x : S) : List S → List (S × S)
  | [] => []
  | y :: ys => (x, y) :: pairWith x ys

def pairLists : List S → List S → List (S × S)
  | [], _ys => []
  | x :: xs, ys => pairWith x ys ++ pairLists xs ys

def inList_pairWith_of_inList
    (x : S) {y : S} {ys : List S} :
    InList y ys → InList (x, y) (pairWith x ys)
  | InList.head => InList.head
  | InList.tail hTail => InList.tail (inList_pairWith_of_inList x hTail)

def inList_pairLists_of_inList
    {x y : S} {rows cols : List S} :
    InList x rows → InList y cols → InList (x, y) (pairLists rows cols)
  | InList.head, hY => inList_append_left (inList_pairWith_of_inList x hY)
  | InList.tail hTail, hY => inList_append_right _ (inList_pairLists_of_inList hTail hY)

theorem jointSameList_eq_of_inList
    (obs : J → S → V) {interfaces : List J} {x y : S} {j : J} :
    JointSameList obs interfaces x y → InList j interfaces → obs j x = obs j y := by
  intro hJoint hIn
  induction interfaces with
  | nil =>
      cases hIn
  | cons k ks ih =>
      cases hIn with
      | head =>
          exact hJoint.1
      | tail hTail =>
          exact ih hJoint.2 hTail

theorem loss_of_residualList_of_inList
    (obs : J → S → V) (sigma : S → Y)
    {interfaces : List J} {x y : S} {j : J} :
    ResidualList obs sigma interfaces x y → InList j interfaces →
      Loss obs sigma j x y := by
  intro hRes hIn
  exact ⟨hRes.1, jointSameList_eq_of_inList obs hRes.2 hIn⟩

theorem residualList_of_requiredDistinction_and_all_loss
    (obs : J → S → V) (sigma : S → Y)
    {interfaces : List J} {x y : S} :
    RequiredDistinction sigma x y →
      (∀ j : J, InList j interfaces → Loss obs sigma j x y) →
        ResidualList obs sigma interfaces x y := by
  intro hReq hAll
  refine ⟨hReq, ?_⟩
  induction interfaces with
  | nil =>
      exact True.intro
  | cons j js ih =>
      exact ⟨(hAll j InList.head).2,
        ih (fun k hk => hAll k (InList.tail hk))⟩

theorem residualList_iff_requiredDistinction_and_all_loss
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (x y : S) :
    ResidualList obs sigma interfaces x y ↔
      RequiredDistinction sigma x y ∧
        ∀ j : J, InList j interfaces → Loss obs sigma j x y := by
  constructor
  · intro hRes
    exact ⟨hRes.1, fun j hIn => loss_of_residualList_of_inList obs sigma hRes hIn⟩
  · intro h
    exact residualList_of_requiredDistinction_and_all_loss obs sigma h.1 h.2

theorem jointSame_of_jointSameList
    (obs : J → S → V) {interfaces : List J} {I : Subfamily J} {x y : S}
    (hEnum : ∀ j : J, I j → InList j interfaces) :
    JointSameList obs interfaces x y → JointSame obs I x y := by
  intro hList j hj
  exact jointSameList_eq_of_inList obs hList (hEnum j hj)

theorem jointSameList_of_jointSame
    (obs : J → S → V) {interfaces : List J} {I : Subfamily J} {x y : S}
    (hEnum : ∀ j : J, InList j interfaces → I j) :
    JointSame obs I x y → JointSameList obs interfaces x y := by
  intro hJoint
  induction interfaces with
  | nil =>
      exact True.intro
  | cons j js ih =>
      refine ⟨?_, ?_⟩
      · exact hJoint j (hEnum j InList.head)
      · exact ih (fun k hk => hEnum k (InList.tail hk))

theorem residual_of_residualList
    (obs : J → S → V) (sigma : S → Y)
    {interfaces : List J} {I : Subfamily J} {x y : S}
    (hEnum : ∀ j : J, I j → InList j interfaces) :
    ResidualList obs sigma interfaces x y → Residual obs sigma I x y := by
  intro hRes
  exact ⟨hRes.1, jointSame_of_jointSameList obs hEnum hRes.2⟩

theorem residualList_of_residual
    (obs : J → S → V) (sigma : S → Y)
    {interfaces : List J} {I : Subfamily J} {x y : S}
    (hEnum : ∀ j : J, InList j interfaces → I j) :
    Residual obs sigma I x y → ResidualList obs sigma interfaces x y := by
  intro hRes
  exact ⟨hRes.1, jointSameList_of_jointSame obs hEnum hRes.2⟩

theorem allFalse_pairWith_of_residualEmpty
    (obs : J → S → V) (sigma : S → Y)
    {interfaces : List J} {I : Subfamily J}
    (hEnum : ∀ j : J, I j → InList j interfaces)
    (hEmpty : ResidualEmpty obs sigma I)
    (x : S) (ys : List S) :
    AllFalse (fun xy : S × S => ResidualList obs sigma interfaces xy.1 xy.2)
      (pairWith x ys) := by
  induction ys with
  | nil =>
      exact AllFalse.nil
  | cons y ys ih =>
      refine AllFalse.cons ?_ ih
      intro hResList
      exact hEmpty x y (residual_of_residualList obs sigma hEnum hResList)

theorem allFalse_pairLists_of_residualEmpty
    (obs : J → S → V) (sigma : S → Y)
    {interfaces : List J} {I : Subfamily J}
    (hEnum : ∀ j : J, I j → InList j interfaces)
    (hEmpty : ResidualEmpty obs sigma I)
    (rows cols : List S) :
    AllFalse (fun xy : S × S => ResidualList obs sigma interfaces xy.1 xy.2)
      (pairLists rows cols) := by
  induction rows with
  | nil =>
      exact AllFalse.nil
  | cons x xs ih =>
      exact allFalse_append
        (allFalse_pairWith_of_residualEmpty obs sigma hEnum hEmpty x cols)
        ih

/-- Numerical residual size over explicit lists of states and interfaces. -/
def rho
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) : Nat :=
  countListBool (pairLists states states)
    (fun xy : S × S => ResidualListBool obs sigma interfaces xy.1 xy.2)

theorem rho_eq_zero_of_allFalse_residualPairs
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) :
    AllFalse (fun xy : S × S => ResidualList obs sigma interfaces xy.1 xy.2)
        (pairLists states states) →
      rho states obs sigma interfaces = 0 := by
  intro h
  unfold rho
  exact countListBool_eq_zero_of_allFalseBool
    (pairLists states states)
    (fun xy : S × S => ResidualListBool obs sigma interfaces xy.1 xy.2)
    (allFalseBool_of_allFalse_residualList obs sigma interfaces
      (pairLists states states) h)

/--
If the explicit interface list enumerates the subfamily, residual emptiness forces numerical
zero residual on any explicit state list.
-/
theorem rho_eq_zero_of_residualEmpty_of_interface_enumeration
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (I : Subfamily J)
    (hEnumLeft : ∀ j : J, I j → InList j interfaces)
    (hEmpty : ResidualEmpty obs sigma I) :
    rho states obs sigma interfaces = 0 :=
  rho_eq_zero_of_allFalse_residualPairs states obs sigma interfaces
    (allFalse_pairLists_of_residualEmpty obs sigma hEnumLeft hEmpty states states)

/--
If explicit states cover all states and explicit interfaces enumerate the subfamily both ways,
then numerical zero residual is exactly residual emptiness.
-/
theorem rho_eq_zero_iff_residualEmpty_of_exhaustive_states
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (I : Subfamily J)
    (hStates : ∀ s : S, InList s states)
    (hEnumLeft : ∀ j : J, I j → InList j interfaces)
    (hEnumRight : ∀ j : J, InList j interfaces → I j) :
    rho states obs sigma interfaces = 0 ↔ ResidualEmpty obs sigma I := by
  constructor
  · intro hRho x y hRes
    have hPair : InList (x, y) (pairLists states states) :=
      inList_pairLists_of_inList (hStates x) (hStates y)
    have hResListed : ResidualList obs sigma interfaces x y :=
      residualList_of_residual obs sigma hEnumRight hRes
    have hBoolTrue :
        ResidualListBool obs sigma interfaces (x, y).1 (x, y).2 = true :=
      bool_true_of_residualList obs sigma interfaces x y hResListed
    have hPos : 0 < rho states obs sigma interfaces := by
      unfold rho
      exact countListBool_pos_of_inList_true
        (pairLists states states)
        (fun xy : S × S => ResidualListBool obs sigma interfaces xy.1 xy.2)
        (x, y) hPair hBoolTrue
    have hZeroPos : 0 < 0 := by
      rw [hRho] at hPos
      exact hPos
    exact Nat.not_lt_zero 0 hZeroPos
  · intro hEmpty
    exact rho_eq_zero_of_residualEmpty_of_interface_enumeration
      states obs sigma interfaces I hEnumLeft hEmpty

/--
With exhaustive states and a two-sided interface enumeration, positive numerical residual is
exactly an explicit propositional residual witness.
-/
theorem rho_pos_iff_residualNonempty_of_exhaustive_states
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (I : Subfamily J)
    (hStates : ∀ s : S, InList s states)
    (hEnumLeft : ∀ j : J, I j → InList j interfaces)
    (hEnumRight : ∀ j : J, InList j interfaces → I j) :
    0 < rho states obs sigma interfaces ↔ ResidualNonempty obs sigma I := by
  constructor
  · intro hPos
    unfold rho at hPos
    rcases exists_inList_true_of_countListBool_pos
        (pairLists states states)
        (fun xy : S × S => ResidualListBool obs sigma interfaces xy.1 xy.2)
        hPos with
      ⟨xy, _hIn, hTrue⟩
    exact ⟨xy.1, xy.2,
      residual_of_residualList obs sigma hEnumLeft
        (residualList_of_bool_true obs sigma interfaces xy.1 xy.2 hTrue)⟩
  · intro hNonempty
    rcases hNonempty with ⟨x, y, hRes⟩
    have hPair : InList (x, y) (pairLists states states) :=
      inList_pairLists_of_inList (hStates x) (hStates y)
    have hResListed : ResidualList obs sigma interfaces x y :=
      residualList_of_residual obs sigma hEnumRight hRes
    have hBoolTrue :
        ResidualListBool obs sigma interfaces (x, y).1 (x, y).2 = true :=
      bool_true_of_residualList obs sigma interfaces x y hResListed
    unfold rho
    exact countListBool_pos_of_inList_true
      (pairLists states states)
      (fun xy : S × S => ResidualListBool obs sigma interfaces xy.1 xy.2)
      (x, y) hPair hBoolTrue

/--
Residual monotonicity: adding interfaces can only remove residual distinctions.

If `I ⊆ K`, then anything lost by the larger family `K` was already lost by `I`.
-/
theorem residual_mono
    (obs : J → S → V) (sigma : S → Y) {I K : Subfamily J}
    (hIK : Subfamily.Subset I K) :
    ∀ x y : S, Residual obs sigma K x y → Residual obs sigma I x y := by
  intro x y hRes
  exact ⟨hRes.1, fun j hjI => hRes.2 j (hIK hjI)⟩

/--
Numerical residual monotonicity for explicitly enumerated subfamilies.

If `I ⊆ K`, then the residual counted for `K` is bounded by the residual counted
for `I`: adding interfaces can only remove residual distinctions.
-/
theorem rho_mono_of_subfamily_subset
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfacesI interfacesK : List J) (I K : Subfamily J)
    (hIK : Subfamily.Subset I K)
    (hEnumKLeft : ∀ j : J, K j → InList j interfacesK)
    (hEnumIRight : ∀ j : J, InList j interfacesI → I j) :
    rho states obs sigma interfacesK ≤ rho states obs sigma interfacesI := by
  unfold rho
  exact countListBool_le_of_true_imp
    (pairLists states states)
    (fun xy : S × S => ResidualListBool obs sigma interfacesK xy.1 xy.2)
    (fun xy : S × S => ResidualListBool obs sigma interfacesI xy.1 xy.2)
    (fun xy _hIn hKBool => by
      have hKList : ResidualList obs sigma interfacesK xy.1 xy.2 :=
        residualList_of_bool_true obs sigma interfacesK xy.1 xy.2 hKBool
      have hKRes : Residual obs sigma K xy.1 xy.2 :=
        residual_of_residualList obs sigma hEnumKLeft hKList
      have hIRes : Residual obs sigma I xy.1 xy.2 :=
        residual_mono obs sigma hIK xy.1 xy.2 hKRes
      have hIList : ResidualList obs sigma interfacesI xy.1 xy.2 :=
        residualList_of_residual obs sigma hEnumIRight hIRes
      exact bool_true_of_residualList obs sigma interfacesI xy.1 xy.2 hIList)

/--
Residual contraction caused by passing from one explicit interface list to an extended one.

This is deliberately numerical: it is the amount by which the residual count decreases.
-/
def deltaGain
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces interfacesPlus : List J) : Nat :=
  rho states obs sigma interfaces - rho states obs sigma interfacesPlus

/-- The defining equation for `deltaGain`. -/
theorem deltaGain_eq_rho_sub
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces interfacesPlus : List J) :
    deltaGain states obs sigma interfaces interfacesPlus =
      rho states obs sigma interfaces - rho states obs sigma interfacesPlus := by
  rfl

/--
Numerical characterization of local usefulness.

Under exhaustive states and two-sided enumerations of `I` and `insert I j0`, an interface is locally
useful exactly when inserting it strictly decreases `rho`.
-/
theorem locallyUsefulInterface_iff_rho_insert_lt_of_exhaustive_states
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (j0 : J)
    (interfacesI interfacesInsert : List J)
    (hStates : ∀ s : S, InList s states)
    (hEnumILeft : ∀ j : J, I j → InList j interfacesI)
    (hEnumIRight : ∀ j : J, InList j interfacesI → I j)
    (hEnumInsertLeft :
      ∀ j : J, Subfamily.Insert I j0 j → InList j interfacesInsert)
    (hEnumInsertRight :
      ∀ j : J, InList j interfacesInsert → Subfamily.Insert I j0 j) :
    LocallyUsefulInterface obs sigma I j0 ↔
      rho states obs sigma interfacesInsert < rho states obs sigma interfacesI := by
  let b : S × S → Bool :=
    fun xy => ResidualListBool obs sigma interfacesInsert xy.1 xy.2
  let c : S × S → Bool :=
    fun xy => ResidualListBool obs sigma interfacesI xy.1 xy.2
  have hImp : ∀ xy : S × S, InList xy (pairLists states states) → b xy = true → c xy = true := by
    intro xy _hIn hInsertBool
    have hInsertList : ResidualList obs sigma interfacesInsert xy.1 xy.2 :=
      residualList_of_bool_true obs sigma interfacesInsert xy.1 xy.2 hInsertBool
    have hInsertRes : Residual obs sigma (Subfamily.Insert I j0) xy.1 xy.2 :=
      residual_of_residualList obs sigma hEnumInsertLeft hInsertList
    have hIRes : Residual obs sigma I xy.1 xy.2 :=
      residual_mono obs sigma (Subfamily.subset_insert I j0) xy.1 xy.2 hInsertRes
    have hIList : ResidualList obs sigma interfacesI xy.1 xy.2 :=
      residualList_of_residual obs sigma hEnumIRight hIRes
    exact bool_true_of_residualList obs sigma interfacesI xy.1 xy.2 hIList
  constructor
  · intro hUseful
    rcases (locallyUsefulInterface_iff_exists_residual_not_insert
        obs sigma I j0).mp hUseful with
      ⟨x, y, hResI, hNotInsert⟩
    have hPair : InList (x, y) (pairLists states states) :=
      inList_pairLists_of_inList (hStates x) (hStates y)
    have hIList : ResidualList obs sigma interfacesI x y :=
      residualList_of_residual obs sigma hEnumIRight hResI
    have hCTrue : c (x, y) = true :=
      bool_true_of_residualList obs sigma interfacesI x y hIList
    have hBFalse : b (x, y) = false := by
      cases hb : b (x, y) with
      | false =>
          rfl
      | true =>
          have hInsertList : ResidualList obs sigma interfacesInsert x y :=
            residualList_of_bool_true obs sigma interfacesInsert x y hb
          have hInsertRes : Residual obs sigma (Subfamily.Insert I j0) x y :=
            residual_of_residualList obs sigma hEnumInsertLeft hInsertList
          exact False.elim (hNotInsert hInsertRes)
    unfold rho
    exact countListBool_lt_of_exists_false_true
      (pairLists states states) b c hImp ⟨(x, y), hPair, hBFalse, hCTrue⟩
  · intro hLt
    unfold rho at hLt
    rcases exists_false_true_of_countListBool_lt
        (pairLists states states) b c hImp hLt with
      ⟨xy, _hIn, hBFalse, hCTrue⟩
    have hIList : ResidualList obs sigma interfacesI xy.1 xy.2 :=
      residualList_of_bool_true obs sigma interfacesI xy.1 xy.2 hCTrue
    have hIRes : Residual obs sigma I xy.1 xy.2 :=
      residual_of_residualList obs sigma hEnumILeft hIList
    have hNotInsert : ¬ Residual obs sigma (Subfamily.Insert I j0) xy.1 xy.2 := by
      intro hInsertRes
      have hInsertList : ResidualList obs sigma interfacesInsert xy.1 xy.2 :=
        residualList_of_residual obs sigma hEnumInsertRight hInsertRes
      have hBTrue : b xy = true :=
        bool_true_of_residualList obs sigma interfacesInsert xy.1 xy.2 hInsertList
      rw [hBFalse] at hBTrue
      cases hBTrue
    exact (locallyUsefulInterface_iff_exists_residual_not_insert
      obs sigma I j0).mpr ⟨xy.1, xy.2, hIRes, hNotInsert⟩

/-- Closure is exactly emptiness of the residual common to the subfamily. -/
theorem closed_iff_residual_empty
    [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) :
    Closed obs sigma I ↔ ResidualEmpty obs sigma I := by
  constructor
  · intro hClosed x y hRes
    exact hRes.1 (hClosed x y hRes.2)
  · intro hEmpty x y hJoint
    by_cases hEq : sigma x = sigma y
    · exact hEq
    · exact False.elim (hEmpty x y ⟨hEq, hJoint⟩)

/--
An interface is structurally essential inside a closing coalition when removing it leaves an
explicit residual witness.
-/
def EssentialInClosure
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (j : J) : Prop :=
  I j ∧ Closed obs sigma I ∧ ResidualNonempty obs sigma (Subfamily.Remove I j)

/--
An interface is structurally redundant inside a closing coalition when removing it preserves
closure.
-/
def RedundantInClosure
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (j : J) : Prop :=
  I j ∧ Closed obs sigma I ∧ Closed obs sigma (Subfamily.Remove I j)

/-- Essentiality is equivalent to closedness plus an explicit residual after ablation. -/
theorem essentialInClosure_iff_closed_and_remove_residual
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (j : J) :
    EssentialInClosure obs sigma I j ↔
      I j ∧ Closed obs sigma I ∧
        ∃ x y : S, Residual obs sigma (Subfamily.Remove I j) x y := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Redundancy is equivalent to closedness plus empty residual after ablation. -/
theorem redundantInClosure_iff_closed_and_remove_residual_empty
    [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (j : J) :
    RedundantInClosure obs sigma I j ↔
      I j ∧ Closed obs sigma I ∧
        ResidualEmpty obs sigma (Subfamily.Remove I j) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, (closed_iff_residual_empty obs sigma (Subfamily.Remove I j)).mp h.2.2⟩
  · intro h
    exact ⟨h.1, h.2.1, (closed_iff_residual_empty obs sigma (Subfamily.Remove I j)).mpr h.2.2⟩

/--
Numerical form of structural essentiality: after ablating `j`, the residual count is positive.
-/
theorem essentialInClosure_iff_closed_and_rho_remove_pos_of_exhaustive_states
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (j : J) (interfacesRemove : List J)
    (hStates : ∀ s : S, InList s states)
    (hEnumRemoveLeft :
      ∀ k : J, Subfamily.Remove I j k → InList k interfacesRemove)
    (hEnumRemoveRight :
      ∀ k : J, InList k interfacesRemove → Subfamily.Remove I j k) :
    EssentialInClosure obs sigma I j ↔
      I j ∧ Closed obs sigma I ∧
        0 < rho states obs sigma interfacesRemove := by
  constructor
  · intro hEss
    have hNonempty : ResidualNonempty obs sigma (Subfamily.Remove I j) := hEss.2.2
    have hPos : 0 < rho states obs sigma interfacesRemove :=
      (rho_pos_iff_residualNonempty_of_exhaustive_states
        states obs sigma interfacesRemove (Subfamily.Remove I j)
        hStates hEnumRemoveLeft hEnumRemoveRight).mpr hNonempty
    exact ⟨hEss.1, hEss.2.1, hPos⟩
  · intro h
    have hNonempty : ResidualNonempty obs sigma (Subfamily.Remove I j) :=
      (rho_pos_iff_residualNonempty_of_exhaustive_states
        states obs sigma interfacesRemove (Subfamily.Remove I j)
        hStates hEnumRemoveLeft hEnumRemoveRight).mp h.2.2
    exact ⟨h.1, h.2.1, hNonempty⟩

/--
Numerical form of structural redundancy: after ablating `j`, the residual count remains zero.
-/
theorem redundantInClosure_iff_closed_and_rho_remove_zero_of_exhaustive_states
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (j : J) (interfacesRemove : List J)
    (hStates : ∀ s : S, InList s states)
    (hEnumRemoveLeft :
      ∀ k : J, Subfamily.Remove I j k → InList k interfacesRemove)
    (hEnumRemoveRight :
      ∀ k : J, InList k interfacesRemove → Subfamily.Remove I j k) :
    RedundantInClosure obs sigma I j ↔
      I j ∧ Closed obs sigma I ∧
        rho states obs sigma interfacesRemove = 0 := by
  constructor
  · intro hRed
    have hEmpty : ResidualEmpty obs sigma (Subfamily.Remove I j) :=
      (closed_iff_residual_empty obs sigma (Subfamily.Remove I j)).mp hRed.2.2
    have hZero : rho states obs sigma interfacesRemove = 0 :=
      (rho_eq_zero_iff_residualEmpty_of_exhaustive_states
        states obs sigma interfacesRemove (Subfamily.Remove I j)
        hStates hEnumRemoveLeft hEnumRemoveRight).mpr hEmpty
    exact ⟨hRed.1, hRed.2.1, hZero⟩
  · intro h
    have hEmpty : ResidualEmpty obs sigma (Subfamily.Remove I j) :=
      (rho_eq_zero_iff_residualEmpty_of_exhaustive_states
        states obs sigma interfacesRemove (Subfamily.Remove I j)
        hStates hEnumRemoveLeft hEnumRemoveRight).mp h.2.2
    exact ⟨h.1, h.2.1, (closed_iff_residual_empty obs sigma (Subfamily.Remove I j)).mpr hEmpty⟩

/-- Irreducible closure: `I` closes, but every proper subfamily leaves a residual. -/
def IrreducibleClosure (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) : Prop :=
  Closed obs sigma I ∧
    ∀ K : Subfamily J, Subfamily.Proper K I → ¬ Closed obs sigma K

/--
Witness-style irreducible closure avoids nonconstructive extraction from negated closure:
`I` closes and every proper subfamily has an explicit residual witness.
-/
def IrreducibleClosureW (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) : Prop :=
  Closed obs sigma I ∧
    ∀ K : Subfamily J, Subfamily.Proper K I → ResidualNonempty obs sigma K

/-- Witness-style irreducible closure has the exact residual normal form. -/
theorem irreducibleClosureW_iff_residual_empty_and_proper_residual_nonempty
    [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) :
    IrreducibleClosureW obs sigma I ↔
      ResidualEmpty obs sigma I ∧
        ∀ K : Subfamily J, Subfamily.Proper K I → ResidualNonempty obs sigma K := by
  constructor
  · intro h
    exact ⟨(closed_iff_residual_empty obs sigma I).mp h.1, h.2⟩
  · intro h
    exact ⟨(closed_iff_residual_empty obs sigma I).mpr h.1, h.2⟩

/-- Witness-style irreducibility implies the negated-closure form. -/
theorem irreducibleClosure_of_irreducibleClosureW
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) :
    IrreducibleClosureW obs sigma I → IrreducibleClosure obs sigma I := by
  intro h
  refine ⟨h.1, ?_⟩
  intro K hProper hClosedK
  rcases h.2 K hProper with ⟨x, y, hRes⟩
  exact hRes.1 (hClosedK x y hRes.2)

/--
Numerical irreducible closure over explicit enumerations.

`interfacesOf K` is the chosen finite list presentation for each subfamily `K`.
The main interface has zero residual count, while every proper subfamily has a positive
residual count.
-/
def IrreducibleClosureRho
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (interfacesOf : Subfamily J → List J) : Prop :=
  rho states obs sigma (interfacesOf I) = 0 ∧
    ∀ K : Subfamily J, Subfamily.Proper K I →
      0 < rho states obs sigma (interfacesOf K)

/--
With exhaustive states and two-sided enumerations for every subfamily, witness-style
irreducible closure is exactly the numerical `rho` certificate.
-/
theorem irreducibleClosureW_iff_irreducibleClosureRho_of_exhaustive_states
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (interfacesOf : Subfamily J → List J)
    (hStates : ∀ s : S, InList s states)
    (hEnumLeft : ∀ K : Subfamily J, ∀ j : J, K j → InList j (interfacesOf K))
    (hEnumRight : ∀ K : Subfamily J, ∀ j : J, InList j (interfacesOf K) → K j) :
    IrreducibleClosureW obs sigma I ↔
      IrreducibleClosureRho states obs sigma I interfacesOf := by
  constructor
  · intro hIrr
    refine ⟨?_, ?_⟩
    · have hEmpty : ResidualEmpty obs sigma I :=
        (closed_iff_residual_empty obs sigma I).mp hIrr.1
      exact (rho_eq_zero_iff_residualEmpty_of_exhaustive_states
        states obs sigma (interfacesOf I) I hStates
        (hEnumLeft I) (hEnumRight I)).mpr hEmpty
    · intro K hProper
      exact (rho_pos_iff_residualNonempty_of_exhaustive_states
        states obs sigma (interfacesOf K) K hStates
        (hEnumLeft K) (hEnumRight K)).mpr (hIrr.2 K hProper)
  · intro hRho
    refine ⟨?_, ?_⟩
    · have hEmpty : ResidualEmpty obs sigma I :=
        (rho_eq_zero_iff_residualEmpty_of_exhaustive_states
          states obs sigma (interfacesOf I) I hStates
          (hEnumLeft I) (hEnumRight I)).mp hRho.1
      exact (closed_iff_residual_empty obs sigma I).mpr hEmpty
    · intro K hProper
      exact (rho_pos_iff_residualNonempty_of_exhaustive_states
        states obs sigma (interfacesOf K) K hStates
        (hEnumLeft K) (hEnumRight K)).mp (hRho.2 K hProper)

/-!
## Dynamic multi-interface profile

The dynamic layer is stated over an already chosen joint observation `jointObs`. A subfamily is
represented by a readout of the same underlying state. This keeps the first n-interface theorem
independent from any particular encoding of products or heterogeneous interfaces.
-/

/--
A subfamily readout predicts the joint dynamic truth on the joint fiber.

This generalizes the binary `LeftObsPredictsJointStep` / `RightObsPredictsJointStep` pattern:
the truth being predicted is still the compatibility truth for the joint observation, but the
allowed information is a subfamily readout.
-/
def SubfamilyPredictsStep
    {P : Type p} [HistoryGraph P]
    {S V : Type w} {W : Type y}
    (sem : Semantics P S) (jointObs : S → V) (targetJoint : P → V)
    {h k : P} (step : HistoryGraph.Path h k)
    (readout : S → W) : Prop :=
  ∃ pred : W → Prop,
    ∀ x : FiberPt (P := P) jointObs targetJoint h,
      Compatible (P := P) sem jointObs targetJoint step x ↔ pred (readout x.1)

/--
A refining-lift mediator descends to a subfamily readout if its finite supplement can be read
from that subfamily readout alone.
-/
def DynamicMediatorDescendsSubfamily
    {P : Type p} [HistoryGraph P]
    {S V : Type w} {W : Type y}
    (sem : Semantics P S) (jointObs : S → V) (targetJoint : P → V)
    {h k : P} (step : HistoryGraph.Path h k) {n : Nat}
    (readout : S → W)
    (L : RefiningLiftData (P := P) sem jointObs targetJoint h step n) : Prop :=
  ∃ readoutK : W → Fin n, ∀ x, (L.extObs x).2 = readoutK (readout x.1)

/--
If the finite supplement of a refining lift descends to a subfamily readout, then the
joint dynamic truth is predictable from that readout.
-/
theorem subfamilyPredictsStep_of_dynamicMediatorDescendsSubfamily
    {P : Type p} [HistoryGraph P]
    {S V : Type w} {W : Type y}
    (sem : Semantics P S) (jointObs : S → V) (targetJoint : P → V)
    {h k : P} (step : HistoryGraph.Path h k) {n : Nat}
    (readout : S → W)
    (L : RefiningLiftData (P := P) sem jointObs targetJoint h step n) :
    DynamicMediatorDescendsSubfamily (P := P) sem jointObs targetJoint step readout L →
      SubfamilyPredictsStep (P := P) sem jointObs targetJoint step readout := by
  rintro ⟨readoutK, hDesc⟩
  let pred : W → Prop := fun w => L.predFin (readoutK w)
  refine ⟨pred, ?_⟩
  intro x
  have hEq : (L.extObs x).2 = readoutK (readout x.1) := hDesc x
  simpa [pred, hEq] using (L.factors x)

/-- If the joint truth is not predictable from a subfamily readout, no lift mediator descends to it. -/
theorem not_dynamicMediatorDescendsSubfamily_of_not_subfamilyPredictsStep
    {P : Type p} [HistoryGraph P]
    {S V : Type w} {W : Type y}
    (sem : Semantics P S) (jointObs : S → V) (targetJoint : P → V)
    {h k : P} (step : HistoryGraph.Path h k) {n : Nat}
    (readout : S → W)
    (L : RefiningLiftData (P := P) sem jointObs targetJoint h step n) :
    ¬ SubfamilyPredictsStep (P := P) sem jointObs targetJoint step readout →
      ¬ DynamicMediatorDescendsSubfamily (P := P) sem jointObs targetJoint step readout L := by
  intro hNoPredict hDesc
  exact hNoPredict
    (subfamilyPredictsStep_of_dynamicMediatorDescendsSubfamily
      (P := P) sem jointObs targetJoint step readout L hDesc)

/--
The n-interface dynamic mediation profile:

* the joint dynamic truth separates the joint fiber;
* the joint truth has exact finite compatibility dimension `n`;
* every proper subfamily of `I` fails to predict that joint truth from its readout.
-/
def FamilyIrreducibleMediationProfile
    {P : Type p} [HistoryGraph P]
    {S V : Type w} {J : Type u} {W : Subfamily J → Type y}
    (sem : Semantics P S) (jointObs : S → V) (targetJoint : P → V)
    (I : Subfamily J) (readoutOf : (K : Subfamily J) → S → W K)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) : Prop :=
  StepSeparatesFiber (P := P) sem jointObs targetJoint step ∧
    CompatDimEq (P := P) sem jointObs targetJoint step n ∧
      ∀ K : Subfamily J, Subfamily.Proper K I →
        ¬ SubfamilyPredictsStep (P := P) sem jointObs targetJoint step (readoutOf K)

/-- A dynamic family profile yields a refining lift at the certified finite dimension. -/
theorem refiningLift_of_familyIrreducibleMediationProfile
    {P : Type p} [HistoryGraph P]
    {S V : Type w} {J : Type u} {W : Subfamily J → Type y}
    (sem : Semantics P S) (jointObs : S → V) (targetJoint : P → V)
    (I : Subfamily J) (readoutOf : (K : Subfamily J) → S → W K)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) :
    FamilyIrreducibleMediationProfile (P := P) sem jointObs targetJoint I readoutOf step n →
      RefiningLift (P := P) sem jointObs targetJoint h step n := by
  intro hProf
  exact refiningLift_of_compatDimEq (P := P) sem jointObs targetJoint step n hProf.2.1

/-- A dynamic family profile excludes refining lifts with any smaller finite supplement. -/
theorem no_smaller_refiningLift_of_familyIrreducibleMediationProfile
    {P : Type p} [HistoryGraph P]
    {S V : Type w} {J : Type u} {W : Subfamily J → Type y}
    (sem : Semantics P S) (jointObs : S → V) (targetJoint : P → V)
    (I : Subfamily J) (readoutOf : (K : Subfamily J) → S → W K)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) :
    FamilyIrreducibleMediationProfile (P := P) sem jointObs targetJoint I readoutOf step n →
      ∀ m : Nat, m < n → ¬ RefiningLift (P := P) sem jointObs targetJoint h step m := by
  intro hProf
  exact no_smaller_refiningLift_of_compatDimEq
    (P := P) sem jointObs targetJoint step n hProf.2.1

/--
In a dynamic family profile, the finite supplement of any refining lift at the certified
dimension cannot descend to any proper subfamily readout.
-/
theorem not_dynamicMediatorDescendsSubfamily_of_familyIrreducibleMediationProfile
    {P : Type p} [HistoryGraph P]
    {S V : Type w} {J : Type u} {W : Subfamily J → Type y}
    (sem : Semantics P S) (jointObs : S → V) (targetJoint : P → V)
    (I : Subfamily J) (readoutOf : (K : Subfamily J) → S → W K)
    {h k : P} (step : HistoryGraph.Path h k) {n : Nat}
    (hProf : FamilyIrreducibleMediationProfile
      (P := P) sem jointObs targetJoint I readoutOf step n)
    (K : Subfamily J) (hProper : Subfamily.Proper K I)
    (L : RefiningLiftData (P := P) sem jointObs targetJoint h step n) :
    ¬ DynamicMediatorDescendsSubfamily
      (P := P) sem jointObs targetJoint step (readoutOf K) L := by
  exact not_dynamicMediatorDescendsSubfamily_of_not_subfamilyPredictsStep
    (P := P) sem jointObs targetJoint step (readoutOf K) L (hProf.2.2 K hProper)

/--
End-to-end wrapper for the dynamic minimal-access-coalition profile.

It packages the three operational consequences of `FamilyIrreducibleMediationProfile`:

* a refining lift exists at the certified finite dimension `n`;
* no smaller finite supplement can refine the joint dynamic truth;
* any concrete lift at dimension `n` fails to descend to every proper subfamily readout.
-/
theorem endToEnd_minimalAccessCoalition
    {P : Type p} [HistoryGraph P]
    {S V : Type w} {J : Type u} {W : Subfamily J → Type y}
    (sem : Semantics P S) (jointObs : S → V) (targetJoint : P → V)
    (I : Subfamily J) (readoutOf : (K : Subfamily J) → S → W K)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) :
    FamilyIrreducibleMediationProfile (P := P) sem jointObs targetJoint I readoutOf step n →
      RefiningLift (P := P) sem jointObs targetJoint h step n
        ∧ (∀ m : Nat, m < n → ¬ RefiningLift (P := P) sem jointObs targetJoint h step m)
        ∧ (∀ L : RefiningLiftData (P := P) sem jointObs targetJoint h step n,
            ∀ K : Subfamily J, Subfamily.Proper K I →
              ¬ DynamicMediatorDescendsSubfamily
                (P := P) sem jointObs targetJoint step (readoutOf K) L) := by
  intro hProf
  refine ⟨?_, ?_, ?_⟩
  · exact refiningLift_of_familyIrreducibleMediationProfile
      (P := P) sem jointObs targetJoint I readoutOf step n hProf
  · exact no_smaller_refiningLift_of_familyIrreducibleMediationProfile
      (P := P) sem jointObs targetJoint I readoutOf step n hProf
  · intro L K hProper
    exact not_dynamicMediatorDescendsSubfamily_of_familyIrreducibleMediationProfile
      (P := P) sem jointObs targetJoint I readoutOf step hProf K hProper L

/-- A finite mediator readout descends to the subfamily `K`. -/
def MediatorDescendsSubfamily
    (obs : J → S → V) (K : Subfamily J)
    {n : Nat} (mediator : S → Fin n) : Prop :=
  ∃ readoutK : S → Fin n,
    (∀ x y : S, JointSame obs K x y → readoutK x = readoutK y) ∧
      ∀ x : S, mediator x = readoutK x

/-- A mediator is irreducible over `I` if it descends to no proper subfamily. -/
def IrreducibleMediator
    (obs : J → S → V) (I : Subfamily J)
    {n : Nat} (mediator : S → Fin n) : Prop :=
  ∀ K : Subfamily J, Subfamily.Proper K I → ¬ MediatorDescendsSubfamily obs K mediator

end MultiInterface
end Standalone
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.Standalone.HistoryGraph
#print axioms PrimitiveHolonomy.Standalone.Semantics
#print axioms PrimitiveHolonomy.Standalone.FiberPt
#print axioms PrimitiveHolonomy.Standalone.Compatible
#print axioms PrimitiveHolonomy.Standalone.StepSeparatesFiber
#print axioms PrimitiveHolonomy.Standalone.RefiningLiftData
#print axioms PrimitiveHolonomy.Standalone.RefiningLift
#print axioms PrimitiveHolonomy.Standalone.CompatDimEq
#print axioms PrimitiveHolonomy.Standalone.refiningLift_of_compatDimEq
#print axioms PrimitiveHolonomy.Standalone.no_smaller_refiningLift_of_compatDimEq
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.countList
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.countList_eq_zero_of_allFalse
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.countListBool_le_of_true_imp
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.countListBool_lt_of_exists_false_true
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.exists_false_true_of_countListBool_lt
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.InterfaceSeparates
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.lossIncidence
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.separationIncidence
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.lossIncidence_pos_iff_exists_loss
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.separationIncidence_pos_iff_exists_interfaceSeparates
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.residualList_iff_requiredDistinction_and_all_loss
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.LocallyUsefulInterface
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.LocallyRedundantInterface
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.SameLossProfileOn
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.LossProfileSeparated
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.Subfamily.Remove
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.Subfamily.remove_subset
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.residual_remove_iff_required_and_other_losses
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.residual_insert_iff_residual_and_loss
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.locallyUsefulInterface_iff_exists_residual_not_insert
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.locallyRedundantInterface_iff_insert_residual_iff
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.sameLossProfileOn_refl
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.rho
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.rho_eq_zero_of_allFalse_residualPairs
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.rho_eq_zero_of_residualEmpty_of_interface_enumeration
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.rho_eq_zero_iff_residualEmpty_of_exhaustive_states
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.rho_pos_iff_residualNonempty_of_exhaustive_states
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.residual_mono
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.rho_mono_of_subfamily_subset
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.deltaGain
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.deltaGain_eq_rho_sub
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.locallyUsefulInterface_iff_rho_insert_lt_of_exhaustive_states
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.closed_iff_residual_empty
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.EssentialInClosure
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.RedundantInClosure
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.essentialInClosure_iff_closed_and_remove_residual
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.redundantInClosure_iff_closed_and_remove_residual_empty
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.essentialInClosure_iff_closed_and_rho_remove_pos_of_exhaustive_states
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.redundantInClosure_iff_closed_and_rho_remove_zero_of_exhaustive_states
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.irreducibleClosureW_iff_residual_empty_and_proper_residual_nonempty
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.irreducibleClosure_of_irreducibleClosureW
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.IrreducibleClosureRho
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.irreducibleClosureW_iff_irreducibleClosureRho_of_exhaustive_states
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.SubfamilyPredictsStep
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.DynamicMediatorDescendsSubfamily
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.subfamilyPredictsStep_of_dynamicMediatorDescendsSubfamily
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.not_dynamicMediatorDescendsSubfamily_of_not_subfamilyPredictsStep
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.FamilyIrreducibleMediationProfile
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.refiningLift_of_familyIrreducibleMediationProfile
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.no_smaller_refiningLift_of_familyIrreducibleMediationProfile
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.not_dynamicMediatorDescendsSubfamily_of_familyIrreducibleMediationProfile
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.endToEnd_minimalAccessCoalition
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.MediatorDescendsSubfamily
#print axioms PrimitiveHolonomy.Standalone.MultiInterface.IrreducibleMediator
/- AXIOM_AUDIT_END -/
