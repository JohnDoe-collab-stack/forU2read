import COFRS.MultiInterface

/-!
# Multi-interface mediation layer

Finite mediator descent and irreducibility layer.

No quotient, no `Classical`, no `propext`.
-/

namespace PrimitiveHolonomy
namespace MultiInterfaceModular

universe u v w

abbrev Subfamily (J : Type u) : Type u :=
  PrimitiveHolonomy.MultiInterface.Subfamily J

namespace Subfamily

abbrev Proper {J : Type u} (K I : Subfamily J) : Prop :=
  PrimitiveHolonomy.MultiInterface.Subfamily.Proper K I

end Subfamily

abbrev MediatorDescendsSubfamily {J : Type u} {S : Type v} {V : Type w}
    (obs : J → S → V) (K : Subfamily J)
    {n : Nat} (mediator : S → Fin n) : Prop :=
  PrimitiveHolonomy.MultiInterface.MediatorDescendsSubfamily obs K mediator

abbrev IrreducibleMediator {J : Type u} {S : Type v} {V : Type w}
    (obs : J → S → V) (I : Subfamily J)
    {n : Nat} (mediator : S → Fin n) : Prop :=
  PrimitiveHolonomy.MultiInterface.IrreducibleMediator obs I mediator

end MultiInterfaceModular
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.MultiInterfaceModular.MediatorDescendsSubfamily
#print axioms PrimitiveHolonomy.MultiInterfaceModular.IrreducibleMediator
/- AXIOM_AUDIT_END -/
