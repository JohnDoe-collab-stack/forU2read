import COFRS.MultiInterface

/-!
# Multi-interface dynamic layer

Dynamic prediction, refining-lift, exact finite dimension, and non-descent layer.

No quotient, no `Classical`, no `propext`.
-/

namespace PrimitiveHolonomy
namespace MultiInterfaceModular

universe p u w y

abbrev Subfamily (J : Type u) : Type u :=
  PrimitiveHolonomy.MultiInterface.Subfamily J

namespace Subfamily

abbrev Proper {J : Type u} (K I : Subfamily J) : Prop :=
  PrimitiveHolonomy.MultiInterface.Subfamily.Proper K I

end Subfamily

abbrev SubfamilyPredictsStep
    {P : Type p} [HistoryGraph P]
    {S V : Type w} {W : Type y}
    (sem : Semantics P S) (jointObs : S → V) (targetJoint : P → V)
    {h k : P} (step : HistoryGraph.Path h k)
    (readout : S → W) : Prop :=
  PrimitiveHolonomy.MultiInterface.SubfamilyPredictsStep sem jointObs targetJoint step readout

abbrev DynamicMediatorDescendsSubfamily
    {P : Type p} [HistoryGraph P]
    {S V : Type w} {W : Type y}
    (sem : Semantics P S) (jointObs : S → V) (targetJoint : P → V)
    {h k : P} (step : HistoryGraph.Path h k) {n : Nat}
    (readout : S → W)
    (L : RefiningLiftData (P := P) sem jointObs targetJoint h step n) : Prop :=
  PrimitiveHolonomy.MultiInterface.DynamicMediatorDescendsSubfamily
    sem jointObs targetJoint step readout L

abbrev FamilyIrreducibleMediationProfile
    {P : Type p} [HistoryGraph P]
    {S V : Type w} {J : Type u} {W : Subfamily J → Type y}
    (sem : Semantics P S) (jointObs : S → V) (targetJoint : P → V)
    (I : Subfamily J) (readoutOf : (K : Subfamily J) → S → W K)
    {h k : P} (step : HistoryGraph.Path h k) (n : Nat) : Prop :=
  PrimitiveHolonomy.MultiInterface.FamilyIrreducibleMediationProfile
    sem jointObs targetJoint I readoutOf step n

theorem subfamilyPredictsStep_of_dynamicMediatorDescendsSubfamily
    {P : Type p} [HistoryGraph P]
    {S V : Type w} {W : Type y}
    (sem : Semantics P S) (jointObs : S → V) (targetJoint : P → V)
    {h k : P} (step : HistoryGraph.Path h k) {n : Nat}
    (readout : S → W)
    (L : RefiningLiftData (P := P) sem jointObs targetJoint h step n) :
    DynamicMediatorDescendsSubfamily (P := P) sem jointObs targetJoint step readout L →
      SubfamilyPredictsStep (P := P) sem jointObs targetJoint step readout :=
  PrimitiveHolonomy.MultiInterface.subfamilyPredictsStep_of_dynamicMediatorDescendsSubfamily
    sem jointObs targetJoint step readout L

theorem not_dynamicMediatorDescendsSubfamily_of_not_subfamilyPredictsStep
    {P : Type p} [HistoryGraph P]
    {S V : Type w} {W : Type y}
    (sem : Semantics P S) (jointObs : S → V) (targetJoint : P → V)
    {h k : P} (step : HistoryGraph.Path h k) {n : Nat}
    (readout : S → W)
    (L : RefiningLiftData (P := P) sem jointObs targetJoint h step n) :
    ¬ SubfamilyPredictsStep (P := P) sem jointObs targetJoint step readout →
      ¬ DynamicMediatorDescendsSubfamily (P := P) sem jointObs targetJoint step readout L :=
  PrimitiveHolonomy.MultiInterface.not_dynamicMediatorDescendsSubfamily_of_not_subfamilyPredictsStep
    sem jointObs targetJoint step readout L

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
                (P := P) sem jointObs targetJoint step (readoutOf K) L) :=
  PrimitiveHolonomy.MultiInterface.endToEnd_minimalAccessCoalition
    sem jointObs targetJoint I readoutOf step n

end MultiInterfaceModular
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.MultiInterfaceModular.SubfamilyPredictsStep
#print axioms PrimitiveHolonomy.MultiInterfaceModular.DynamicMediatorDescendsSubfamily
#print axioms PrimitiveHolonomy.MultiInterfaceModular.FamilyIrreducibleMediationProfile
#print axioms PrimitiveHolonomy.MultiInterfaceModular.subfamilyPredictsStep_of_dynamicMediatorDescendsSubfamily
#print axioms PrimitiveHolonomy.MultiInterfaceModular.not_dynamicMediatorDescendsSubfamily_of_not_subfamilyPredictsStep
#print axioms PrimitiveHolonomy.MultiInterfaceModular.endToEnd_minimalAccessCoalition
/- AXIOM_AUDIT_END -/
