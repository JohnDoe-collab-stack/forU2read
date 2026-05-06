import COFRS.MultiInterface

/-!
# Multi-interface finite layer

Explicit-list finite layer for the modular multi-interface program.

This file re-exposes the constructive finite counting and `rho` bridge from the audited kernel,
without changing the historical file.

No quotient, no `Classical`, no `propext`.
-/

namespace PrimitiveHolonomy
namespace MultiInterfaceModular

universe u v w a

abbrev Subfamily (J : Type u) : Type u :=
  PrimitiveHolonomy.MultiInterface.Subfamily J

abbrev ResidualEmpty {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) : Prop :=
  PrimitiveHolonomy.MultiInterface.ResidualEmpty obs sigma I

abbrev ResidualNonempty {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) : Prop :=
  PrimitiveHolonomy.MultiInterface.ResidualNonempty obs sigma I

namespace Subfamily

abbrev Subset {J : Type u} (K I : Subfamily J) : Prop :=
  PrimitiveHolonomy.MultiInterface.Subfamily.Subset K I

end Subfamily

abbrev InList {A : Type a} (a : A) (xs : List A) : Prop :=
  PrimitiveHolonomy.MultiInterface.InList a xs

abbrev AllFalse {A : Type a} (P : A → Prop) (xs : List A) : Prop :=
  PrimitiveHolonomy.MultiInterface.AllFalse P xs

abbrev AllFalseBool {A : Type a} (b : A → Bool) (xs : List A) : Prop :=
  PrimitiveHolonomy.MultiInterface.AllFalseBool b xs

abbrev countListBool {A : Type a} (xs : List A) (b : A → Bool) : Nat :=
  PrimitiveHolonomy.MultiInterface.countListBool xs b

abbrev pairWith {S : Type v} (x : S) (ys : List S) : List (S × S) :=
  PrimitiveHolonomy.MultiInterface.pairWith x ys

abbrev pairLists {S : Type v} (rows cols : List S) : List (S × S) :=
  PrimitiveHolonomy.MultiInterface.pairLists rows cols

abbrev JointSameList {J : Type u} {S : Type v} {V : Type w}
    (obs : J → S → V) (interfaces : List J) (x y : S) : Prop :=
  PrimitiveHolonomy.MultiInterface.JointSameList obs interfaces x y

abbrev ResidualList {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (x y : S) : Prop :=
  PrimitiveHolonomy.MultiInterface.ResidualList obs sigma interfaces x y

abbrev JointSameListBool {J : Type u} {S : Type v} {V : Type w}
    [DecidableEq V]
    (obs : J → S → V) (interfaces : List J) (x y : S) : Bool :=
  PrimitiveHolonomy.MultiInterface.JointSameListBool obs interfaces x y

abbrev ResidualListBool {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (x y : S) : Bool :=
  PrimitiveHolonomy.MultiInterface.ResidualListBool obs sigma interfaces x y

abbrev rho {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) : Nat :=
  PrimitiveHolonomy.MultiInterface.rho states obs sigma interfaces

theorem rho_eq_zero_iff_residualEmpty_of_exhaustive_states
    {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (I : Subfamily J)
    (hStates : ∀ s : S, InList s states)
    (hEnumLeft : ∀ j : J, I j → InList j interfaces)
    (hEnumRight : ∀ j : J, InList j interfaces → I j) :
    rho states obs sigma interfaces = 0 ↔ ResidualEmpty obs sigma I :=
  PrimitiveHolonomy.MultiInterface.rho_eq_zero_iff_residualEmpty_of_exhaustive_states
    states obs sigma interfaces I hStates hEnumLeft hEnumRight

theorem rho_pos_iff_residualNonempty_of_exhaustive_states
    {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (I : Subfamily J)
    (hStates : ∀ s : S, InList s states)
    (hEnumLeft : ∀ j : J, I j → InList j interfaces)
    (hEnumRight : ∀ j : J, InList j interfaces → I j) :
    0 < rho states obs sigma interfaces ↔ ResidualNonempty obs sigma I :=
  PrimitiveHolonomy.MultiInterface.rho_pos_iff_residualNonempty_of_exhaustive_states
    states obs sigma interfaces I hStates hEnumLeft hEnumRight

theorem rho_mono_of_subfamily_subset
    {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfacesI interfacesK : List J) (I K : Subfamily J)
    (hIK : Subfamily.Subset I K)
    (hEnumKLeft : ∀ j : J, K j → InList j interfacesK)
    (hEnumIRight : ∀ j : J, InList j interfacesI → I j) :
    rho states obs sigma interfacesK ≤ rho states obs sigma interfacesI :=
  PrimitiveHolonomy.MultiInterface.rho_mono_of_subfamily_subset
    states obs sigma interfacesI interfacesK I K hIK hEnumKLeft hEnumIRight

end MultiInterfaceModular
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.MultiInterfaceModular.InList
#print axioms PrimitiveHolonomy.MultiInterfaceModular.AllFalse
#print axioms PrimitiveHolonomy.MultiInterfaceModular.countListBool
#print axioms PrimitiveHolonomy.MultiInterfaceModular.ResidualListBool
#print axioms PrimitiveHolonomy.MultiInterfaceModular.rho
#print axioms PrimitiveHolonomy.MultiInterfaceModular.rho_eq_zero_iff_residualEmpty_of_exhaustive_states
#print axioms PrimitiveHolonomy.MultiInterfaceModular.rho_pos_iff_residualNonempty_of_exhaustive_states
#print axioms PrimitiveHolonomy.MultiInterfaceModular.rho_mono_of_subfamily_subset
/- AXIOM_AUDIT_END -/
