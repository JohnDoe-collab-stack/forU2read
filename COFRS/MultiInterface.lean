import COFRS.Foundations

/-!
# Multi-interface closure

Constructive first layer for the multi-interface program.

This file deliberately starts before heterogeneous products and before finite cardinal arithmetic.
It formalizes the kernel that survives constructively:

* a family of homogeneous interfaces;
* joint indistinguishability for a subfamily;
* residual target distinctions;
* closure as "constant on joint fibers";
* irreducible closure under all proper subfamilies;
* mediator descent to a subfamily.

No quotient, no `Classical`, no `propext`.
-/

namespace PrimitiveHolonomy

universe u v w z

namespace MultiInterface

variable {J : Type u} {S : Type v} {V : Type w} {Y : Type w}

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
def countListD {A : Type u} (xs : List A) (P : A → Prop)
    (decP : ∀ x, Decidable (P x)) : Nat :=
  match xs with
  | [] => 0
  | x :: xs =>
      match decP x with
      | isTrue _ => Nat.succ (countListD xs P decP)
      | isFalse _ => countListD xs P decP

/-- Constructive count over an explicit finite list. -/
def countList {A : Type u} (xs : List A) (P : A → Prop) [∀ x, Decidable (P x)] : Nat :=
  countListD xs P (fun _ => inferInstance)

/-- Structural "all entries fail `P`", avoiding membership elimination. -/
inductive AllFalse {A : Type u} (P : A → Prop) : List A → Prop
  | nil : AllFalse P []
  | cons {a : A} {xs : List A} : ¬ P a → AllFalse P xs → AllFalse P (a :: xs)

theorem countListD_eq_zero_of_allFalse
    {A : Type u} (xs : List A) (P : A → Prop) (decP : ∀ x, Decidable (P x)) :
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
    {A : Type u} (xs : List A) (P : A → Prop) [∀ x, Decidable (P x)] :
    AllFalse P xs → countList xs P = 0 := by
  exact countListD_eq_zero_of_allFalse xs P (fun _ => inferInstance)

/--
Type-valued membership in an explicit list.

This is intentionally not `List.Mem`: it lets the finite bridge stay quotient-free and avoid
propositional extensionality in audited declarations.
-/
inductive InList {A : Type z} (a : A) : List A → Prop
  | head {xs : List A} : InList a (a :: xs)
  | tail {b : A} {xs : List A} : InList a xs → InList a (b :: xs)

theorem allFalse_not_of_inList
    {A : Type u} {P : A → Prop} {a : A} {xs : List A} :
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
def countListBool {A : Type u} : List A → (A → Bool) → Nat
  | [], _b => 0
  | a :: xs, b =>
      match b a with
      | true => Nat.succ (countListBool xs b)
      | false => countListBool xs b

/-- Structural statement that a boolean predicate is false on every listed element. -/
inductive AllFalseBool {A : Type u} (b : A → Bool) : List A → Prop
  | nil : AllFalseBool b []
  | cons {a : A} {xs : List A} :
      b a = false → AllFalseBool b xs → AllFalseBool b (a :: xs)

theorem countListBool_eq_zero_of_allFalseBool
    {A : Type u} (xs : List A) (b : A → Bool) :
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
    {A : Type u} {b : A → Bool} {a : A} {xs : List A} :
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

def inList_append_left
    {A : Type u} {a : A} {xs ys : List A} :
    InList a xs → InList a (xs ++ ys)
  | InList.head => InList.head
  | InList.tail hTail => InList.tail (inList_append_left hTail)

def inList_append_right
    {A : Type u} {a : A} (xs : List A) {ys : List A} :
    InList a ys → InList a (xs ++ ys) :=
  match xs with
  | [] => fun h => h
  | _ :: xs => fun h => InList.tail (inList_append_right xs h)

theorem allFalse_append
    {A : Type u} {P : A → Prop} {xs ys : List A} :
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

/-- Two states are indistinguishable by every interface in `I`. -/
def JointSame (obs : J → S → V) (I : Subfamily J) (x y : S) : Prop :=
  ∀ j : J, I j → obs j x = obs j y

/-- Target distinction required by `sigma`. -/
def RequiredDistinction (sigma : S → Y) (x y : S) : Prop :=
  sigma x ≠ sigma y

/-- Distinctions required by `sigma` but lost by interface `j`. -/
def Loss (obs : J → S → V) (sigma : S → Y) (j : J) (x y : S) : Prop :=
  RequiredDistinction sigma x y ∧ obs j x = obs j y

/--
Residual common to a subfamily `I`: a required distinction that every interface in `I` loses.

For `I = ∅`, this reduces to all required distinctions, because the universal condition is vacuous.
-/
def Residual (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (x y : S) : Prop :=
  RequiredDistinction sigma x y ∧ JointSame obs I x y

/-- A subfamily has empty residual: no required target distinction is still jointly lost. -/
def ResidualEmpty (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) : Prop :=
  ∀ x y : S, ¬ Residual obs sigma I x y

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
Residual monotonicity: adding interfaces can only remove residual distinctions.

If `I ⊆ K`, then anything lost by the larger family `K` was already lost by `I`.
-/
theorem residual_mono
    (obs : J → S → V) (sigma : S → Y) {I K : Subfamily J}
    (hIK : Subfamily.Subset I K) :
    ∀ x y : S, Residual obs sigma K x y → Residual obs sigma I x y := by
  intro x y hRes
  exact ⟨hRes.1, fun j hjI => hRes.2 j (hIK hjI)⟩

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

/-- Nonempty residual, as a constructive witness. -/
def ResidualNonempty (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) : Prop :=
  ∃ x y : S, Residual obs sigma I x y

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

/-- A finite mediator readout descends to the subfamily `K`. -/
def MediatorDescendsSubfamily
    (obs : J → S → V) (K : Subfamily J)
    {n : Nat} (mediator : S → Fin n) : Prop :=
  ∃ rhoK : S → Fin n,
    (∀ x y : S, JointSame obs K x y → rhoK x = rhoK y) ∧
      ∀ x : S, mediator x = rhoK x

/-- A mediator is irreducible over `I` if it descends to no proper subfamily. -/
def IrreducibleMediator
    (obs : J → S → V) (I : Subfamily J)
    {n : Nat} (mediator : S → Fin n) : Prop :=
  ∀ K : Subfamily J, Subfamily.Proper K I → ¬ MediatorDescendsSubfamily obs K mediator

end MultiInterface

end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.MultiInterface.countList
#print axioms PrimitiveHolonomy.MultiInterface.countList_eq_zero_of_allFalse
#print axioms PrimitiveHolonomy.MultiInterface.rho
#print axioms PrimitiveHolonomy.MultiInterface.rho_eq_zero_of_allFalse_residualPairs
#print axioms PrimitiveHolonomy.MultiInterface.rho_eq_zero_of_residualEmpty_of_interface_enumeration
#print axioms PrimitiveHolonomy.MultiInterface.residual_mono
#print axioms PrimitiveHolonomy.MultiInterface.closed_iff_residual_empty
#print axioms PrimitiveHolonomy.MultiInterface.irreducibleClosureW_iff_residual_empty_and_proper_residual_nonempty
#print axioms PrimitiveHolonomy.MultiInterface.irreducibleClosure_of_irreducibleClosureW
#print axioms PrimitiveHolonomy.MultiInterface.MediatorDescendsSubfamily
#print axioms PrimitiveHolonomy.MultiInterface.IrreducibleMediator
/- AXIOM_AUDIT_END -/
