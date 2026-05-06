import COFRS.MultiInterface

/-!
# Multi-interface closure layer

Closure, essentiality, redundancy, and irreducibility layer.

No quotient, no `Classical`, no `propext`.
-/

namespace PrimitiveHolonomy
namespace MultiInterfaceModular

universe u v w a

abbrev Subfamily (J : Type u) : Type u :=
  PrimitiveHolonomy.MultiInterface.Subfamily J

namespace Subfamily

abbrev Proper {J : Type u} (K I : Subfamily J) : Prop :=
  PrimitiveHolonomy.MultiInterface.Subfamily.Proper K I

end Subfamily

abbrev InList {A : Type a} (a : A) (xs : List A) : Prop :=
  PrimitiveHolonomy.MultiInterface.InList a xs

abbrev ResidualEmpty {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) : Prop :=
  PrimitiveHolonomy.MultiInterface.ResidualEmpty obs sigma I

abbrev ResidualNonempty {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) : Prop :=
  PrimitiveHolonomy.MultiInterface.ResidualNonempty obs sigma I

abbrev Closed {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) : Prop :=
  PrimitiveHolonomy.MultiInterface.Closed obs sigma I

abbrev rho {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (interfaces : List J) : Nat :=
  PrimitiveHolonomy.MultiInterface.rho states obs sigma interfaces

abbrev EssentialInClosure {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (j : J) : Prop :=
  PrimitiveHolonomy.MultiInterface.EssentialInClosure obs sigma I j

abbrev RedundantInClosure {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (j : J) : Prop :=
  PrimitiveHolonomy.MultiInterface.RedundantInClosure obs sigma I j

abbrev IrreducibleClosure {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) : Prop :=
  PrimitiveHolonomy.MultiInterface.IrreducibleClosure obs sigma I

abbrev IrreducibleClosureW {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) : Prop :=
  PrimitiveHolonomy.MultiInterface.IrreducibleClosureW obs sigma I

abbrev IrreducibleClosureRho {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (interfacesOf : Subfamily J → List J) : Prop :=
  PrimitiveHolonomy.MultiInterface.IrreducibleClosureRho states obs sigma I interfacesOf

theorem irreducibleClosureW_iff_residual_empty_and_proper_residual_nonempty
    {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) :
    IrreducibleClosureW obs sigma I ↔
      ResidualEmpty obs sigma I ∧
        ∀ K : Subfamily J, Subfamily.Proper K I → ResidualNonempty obs sigma K :=
  PrimitiveHolonomy.MultiInterface.irreducibleClosureW_iff_residual_empty_and_proper_residual_nonempty
    obs sigma I

theorem irreducibleClosure_of_irreducibleClosureW
    {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) :
    IrreducibleClosureW obs sigma I → IrreducibleClosure obs sigma I :=
  PrimitiveHolonomy.MultiInterface.irreducibleClosure_of_irreducibleClosureW obs sigma I

theorem irreducibleClosureW_iff_irreducibleClosureRho_of_exhaustive_states
    {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    [DecidableEq V] [DecidableEq Y]
    (states : List S) (obs : J → S → V) (sigma : S → Y)
    (I : Subfamily J) (interfacesOf : Subfamily J → List J)
    (hStates : ∀ s : S, InList s states)
    (hEnumLeft : ∀ K : Subfamily J, ∀ j : J, K j → InList j (interfacesOf K))
    (hEnumRight : ∀ K : Subfamily J, ∀ j : J, InList j (interfacesOf K) → K j) :
    IrreducibleClosureW obs sigma I ↔
      IrreducibleClosureRho states obs sigma I interfacesOf :=
  PrimitiveHolonomy.MultiInterface.irreducibleClosureW_iff_irreducibleClosureRho_of_exhaustive_states
    states obs sigma I interfacesOf hStates hEnumLeft hEnumRight

end MultiInterfaceModular
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.MultiInterfaceModular.EssentialInClosure
#print axioms PrimitiveHolonomy.MultiInterfaceModular.RedundantInClosure
#print axioms PrimitiveHolonomy.MultiInterfaceModular.IrreducibleClosure
#print axioms PrimitiveHolonomy.MultiInterfaceModular.IrreducibleClosureW
#print axioms PrimitiveHolonomy.MultiInterfaceModular.IrreducibleClosureRho
#print axioms PrimitiveHolonomy.MultiInterfaceModular.irreducibleClosureW_iff_residual_empty_and_proper_residual_nonempty
#print axioms PrimitiveHolonomy.MultiInterfaceModular.irreducibleClosure_of_irreducibleClosureW
#print axioms PrimitiveHolonomy.MultiInterfaceModular.irreducibleClosureW_iff_irreducibleClosureRho_of_exhaustive_states
/- AXIOM_AUDIT_END -/
