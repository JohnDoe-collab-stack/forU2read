import COFRS.MultiInterface

/-!
# Multi-interface incidence layer

Incidence and local-gain layer for the modular multi-interface program.

No quotient, no `Classical`, no `propext`.
-/

namespace PrimitiveHolonomy
namespace MultiInterfaceModular

universe u v w a

abbrev Subfamily (J : Type u) : Type u :=
  PrimitiveHolonomy.MultiInterface.Subfamily J

namespace Subfamily

abbrev Insert {J : Type u} (I : Subfamily J) (j0 : J) : Subfamily J :=
  PrimitiveHolonomy.MultiInterface.Subfamily.Insert I j0

end Subfamily

abbrev InList {A : Type a} (a : A) (xs : List A) : Prop :=
  PrimitiveHolonomy.MultiInterface.InList a xs

abbrev Loss {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (j : J) (x y : S) : Prop :=
  PrimitiveHolonomy.MultiInterface.Loss obs sigma j x y

abbrev InterfaceSeparates {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (j : J) (x y : S) : Prop :=
  PrimitiveHolonomy.MultiInterface.InterfaceSeparates obs sigma j x y

abbrev rho {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) : Nat :=
  PrimitiveHolonomy.MultiInterface.rho states obs sigma interfaces

abbrev LossBool {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y) (j : J) (x y : S) : Bool :=
  PrimitiveHolonomy.MultiInterface.LossBool obs sigma j x y

abbrev InterfaceSeparatesBool {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y) (j : J) (x y : S) : Bool :=
  PrimitiveHolonomy.MultiInterface.InterfaceSeparatesBool obs sigma j x y

abbrev lossIncidence {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (x y : S) : Nat :=
  PrimitiveHolonomy.MultiInterface.lossIncidence obs sigma interfaces x y

abbrev separationIncidence {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (x y : S) : Nat :=
  PrimitiveHolonomy.MultiInterface.separationIncidence obs sigma interfaces x y

abbrev LocallyUsefulInterface {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (j : J) : Prop :=
  PrimitiveHolonomy.MultiInterface.LocallyUsefulInterface obs sigma I j

abbrev LocallyRedundantInterface {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (j : J) : Prop :=
  PrimitiveHolonomy.MultiInterface.LocallyRedundantInterface obs sigma I j

abbrev SameLossProfileOn {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (j k : J) : Prop :=
  PrimitiveHolonomy.MultiInterface.SameLossProfileOn obs sigma I j k

abbrev LossProfileSeparated {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (j k : J) : Prop :=
  PrimitiveHolonomy.MultiInterface.LossProfileSeparated obs sigma I j k

abbrev deltaGain {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces interfacesPlus : List J) : Nat :=
  PrimitiveHolonomy.MultiInterface.deltaGain states obs sigma interfaces interfacesPlus

theorem lossIncidence_pos_iff_exists_loss
    {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (x y : S) :
    0 < lossIncidence obs sigma interfaces x y ↔
      ∃ j : J, InList j interfaces ∧ Loss obs sigma j x y :=
  PrimitiveHolonomy.MultiInterface.lossIncidence_pos_iff_exists_loss
    obs sigma interfaces x y

theorem separationIncidence_pos_iff_exists_interfaceSeparates
    {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    [DecidableEq V] [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) (x y : S) :
    0 < separationIncidence obs sigma interfaces x y ↔
      ∃ j : J, InList j interfaces ∧ InterfaceSeparates obs sigma j x y :=
  PrimitiveHolonomy.MultiInterface.separationIncidence_pos_iff_exists_interfaceSeparates
    obs sigma interfaces x y

theorem locallyUsefulInterface_iff_rho_insert_lt_of_exhaustive_states
    {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
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
      rho states obs sigma interfacesInsert < rho states obs sigma interfacesI :=
  PrimitiveHolonomy.MultiInterface.locallyUsefulInterface_iff_rho_insert_lt_of_exhaustive_states
    states obs sigma I j0 interfacesI interfacesInsert hStates hEnumILeft
    hEnumIRight hEnumInsertLeft hEnumInsertRight

end MultiInterfaceModular
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.MultiInterfaceModular.LossBool
#print axioms PrimitiveHolonomy.MultiInterfaceModular.InterfaceSeparatesBool
#print axioms PrimitiveHolonomy.MultiInterfaceModular.lossIncidence
#print axioms PrimitiveHolonomy.MultiInterfaceModular.separationIncidence
#print axioms PrimitiveHolonomy.MultiInterfaceModular.LocallyUsefulInterface
#print axioms PrimitiveHolonomy.MultiInterfaceModular.LocallyRedundantInterface
#print axioms PrimitiveHolonomy.MultiInterfaceModular.SameLossProfileOn
#print axioms PrimitiveHolonomy.MultiInterfaceModular.LossProfileSeparated
#print axioms PrimitiveHolonomy.MultiInterfaceModular.deltaGain
#print axioms PrimitiveHolonomy.MultiInterfaceModular.lossIncidence_pos_iff_exists_loss
#print axioms PrimitiveHolonomy.MultiInterfaceModular.separationIncidence_pos_iff_exists_interfaceSeparates
#print axioms PrimitiveHolonomy.MultiInterfaceModular.locallyUsefulInterface_iff_rho_insert_lt_of_exhaustive_states
/- AXIOM_AUDIT_END -/
