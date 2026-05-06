import COFRS.MultiInterface

/-!
# Multi-interface modular core

Isolated modular layer for the multi-interface program.

This file does not modify `COFRS/MultiInterface.lean`. It exposes the core proposition-level
interface of the already-audited kernel under a modular namespace, so the larger algebra can be
split without changing the historical file.

No quotient, no `Classical`, no `propext`.
-/

namespace PrimitiveHolonomy
namespace MultiInterfaceModular

universe u v w

abbrev Subfamily (J : Type u) : Type u :=
  PrimitiveHolonomy.MultiInterface.Subfamily J

namespace Subfamily

abbrev Subset {J : Type u} (K I : Subfamily J) : Prop :=
  PrimitiveHolonomy.MultiInterface.Subfamily.Subset K I

abbrev Proper {J : Type u} (K I : Subfamily J) : Prop :=
  PrimitiveHolonomy.MultiInterface.Subfamily.Proper K I

abbrev Insert {J : Type u} (I : Subfamily J) (j0 : J) : Subfamily J :=
  PrimitiveHolonomy.MultiInterface.Subfamily.Insert I j0

abbrev Remove {J : Type u} (I : Subfamily J) (j0 : J) : Subfamily J :=
  PrimitiveHolonomy.MultiInterface.Subfamily.Remove I j0

theorem subset_insert {J : Type u} (I : Subfamily J) (j0 : J) :
    Subset I (Insert I j0) :=
  PrimitiveHolonomy.MultiInterface.Subfamily.subset_insert I j0

theorem remove_subset {J : Type u} (I : Subfamily J) (j0 : J) :
    Subset (Remove I j0) I :=
  PrimitiveHolonomy.MultiInterface.Subfamily.remove_subset I j0

end Subfamily

abbrev JointSame {J : Type u} {S : Type v} {V : Type w}
    (obs : J → S → V) (I : Subfamily J) (x y : S) : Prop :=
  PrimitiveHolonomy.MultiInterface.JointSame obs I x y

abbrev RequiredDistinction {S : Type v} {Y : Type w}
    (sigma : S → Y) (x y : S) : Prop :=
  PrimitiveHolonomy.MultiInterface.RequiredDistinction sigma x y

abbrev Loss {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (j : J) (x y : S) : Prop :=
  PrimitiveHolonomy.MultiInterface.Loss obs sigma j x y

abbrev InterfaceSeparates {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (j : J) (x y : S) : Prop :=
  PrimitiveHolonomy.MultiInterface.InterfaceSeparates obs sigma j x y

abbrev Residual {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) (x y : S) : Prop :=
  PrimitiveHolonomy.MultiInterface.Residual obs sigma I x y

abbrev ResidualEmpty {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) : Prop :=
  PrimitiveHolonomy.MultiInterface.ResidualEmpty obs sigma I

abbrev ResidualNonempty {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) : Prop :=
  PrimitiveHolonomy.MultiInterface.ResidualNonempty obs sigma I

abbrev Closed {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) : Prop :=
  PrimitiveHolonomy.MultiInterface.Closed obs sigma I

theorem residual_mono
    {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    (obs : J → S → V) (sigma : S → Y) {I K : Subfamily J}
    (hIK : Subfamily.Subset I K) :
    ∀ x y : S, Residual obs sigma K x y → Residual obs sigma I x y :=
  PrimitiveHolonomy.MultiInterface.residual_mono obs sigma hIK

theorem closed_iff_residual_empty
    {J : Type u} {S : Type v} {V : Type w} {Y : Type w}
    [DecidableEq Y]
    (obs : J → S → V) (sigma : S → Y) (I : Subfamily J) :
    Closed obs sigma I ↔ ResidualEmpty obs sigma I :=
  PrimitiveHolonomy.MultiInterface.closed_iff_residual_empty obs sigma I

end MultiInterfaceModular
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.MultiInterfaceModular.Subfamily
#print axioms PrimitiveHolonomy.MultiInterfaceModular.Subfamily.Subset
#print axioms PrimitiveHolonomy.MultiInterfaceModular.JointSame
#print axioms PrimitiveHolonomy.MultiInterfaceModular.RequiredDistinction
#print axioms PrimitiveHolonomy.MultiInterfaceModular.Loss
#print axioms PrimitiveHolonomy.MultiInterfaceModular.InterfaceSeparates
#print axioms PrimitiveHolonomy.MultiInterfaceModular.Residual
#print axioms PrimitiveHolonomy.MultiInterfaceModular.ResidualEmpty
#print axioms PrimitiveHolonomy.MultiInterfaceModular.ResidualNonempty
#print axioms PrimitiveHolonomy.MultiInterfaceModular.Closed
#print axioms PrimitiveHolonomy.MultiInterfaceModular.residual_mono
#print axioms PrimitiveHolonomy.MultiInterfaceModular.closed_iff_residual_empty
/- AXIOM_AUDIT_END -/
