/-!
# Self-contained multi-interface geometry

This file starts the geometric layer promised by
`Private_notes/MULTI_INTERFACE_GEOMETRY_PROGRAM.md`.

It is intentionally standalone: it imports no project file and no external module.

The purpose is not to redo the numerical finite algebra, but to isolate the
geometry that sits above it:

* abstract incidence systems,
* residuals as contravariant objects on coalitions,
* witness-style covering coalitions,
* local gluing of covers,
* incidence isomorphisms and preservation of residuals/covers,
* observation systems as concrete realizations of an abstract incidence system.

Constructive only.
-/

namespace PrimitiveHolonomy
namespace Standalone
namespace MultiInterfaceGeometry

universe u v w y

/-!
## Coalitions

A coalition is represented extensionally as a predicate `J → Prop`, but we never
turn pointwise equivalences into global set equalities. This keeps the file away
from forbidden extensionality and quotient machinery.
-/

/-- A subfamily / coalition of interfaces. -/
def Coalition (J : Type u) : Type u :=
  J → Prop

/-- Inclusion of coalitions. -/
def Coalition.Subset {J : Type u} (I K : Coalition J) : Prop :=
  ∀ j, I j → K j

/-- Strict inclusion of coalitions, kept witness-style. -/
def Coalition.Proper {J : Type u} (I K : Coalition J) : Prop :=
  Coalition.Subset I K ∧ ∃ j, K j ∧ ¬ I j

/-- Union of an indexed family of coalitions. -/
def Coalition.iUnion {T : Type u} {J : Type v} (I : T → Coalition J) : Coalition J :=
  fun j => ∃ t, I t j

/-- Direct witness that a member of a local coalition belongs to the union. -/
theorem Coalition.mem_iUnion {T : Type u} {J : Type v} (I : T → Coalition J)
    (t : T) (j : J) :
    I t j → Coalition.iUnion I j := by
  intro hj
  exact ⟨t, hj⟩

/-!
## Abstract incidence systems

The geometry starts here. We do not begin from concrete observations
`obs : J → X → V`; we begin from the relations that matter geometrically:

* which distinctions are required,
* which interfaces lose a distinction,
* which interfaces separate a distinction.

Concrete observation systems are added later as realizations.
-/

/-- Abstract incidence system for target-relative interface closure. -/
structure AbstractIncidenceSystem (D : Type u) (J : Type v) where
  Required : D → Prop
  Loss : J → D → Prop
  Separates : J → D → Prop
  separates_required : ∀ {j d}, Separates j d → Required d
  separates_not_loss : ∀ {j d}, Separates j d → ¬ Loss j d

namespace AbstractIncidenceSystem

variable {D : Type u} {J : Type v}
variable (A : AbstractIncidenceSystem D J)

/-- Incidence of loss: interfaces that lose a distinction. -/
def IncLoss (d : D) : Coalition J :=
  fun j => A.Required d ∧ A.Loss j d

/-- Incidence of separation: interfaces that separate a distinction. -/
def IncSep (d : D) : Coalition J :=
  fun j => A.Separates j d

/-- A distinction is residual for `I` when it is required and lost by every interface in `I`. -/
def Residual (I : Coalition J) (d : D) : Prop :=
  A.Required d ∧ ∀ j, I j → A.Loss j d

/-- Residual emptiness, stated without set equality. -/
def ResidualEmpty (I : Coalition J) : Prop :=
  ∀ d, A.Residual I d → False

/-- Residual non-emptiness, stated by an explicit witness. -/
def ResidualNonempty (I : Coalition J) : Prop :=
  ∃ d, A.Residual I d

/-- Witness-style covering: every required distinction is separated by some interface in `I`. -/
def CoveringCoalition (I : Coalition J) : Prop :=
  ∀ d, A.Required d → ∃ j, I j ∧ A.Separates j d

/-- A closed coalition is, geometrically, a covering coalition. -/
def Closed (I : Coalition J) : Prop :=
  A.CoveringCoalition I

/-- Minimal cover / irreducible closure, expressed by all proper subcoalitions failing to cover. -/
def MinimalCoveringCoalition (I : Coalition J) : Prop :=
  A.CoveringCoalition I ∧
    ∀ K, Coalition.Proper K I → ¬ A.CoveringCoalition K

/-- The incidence formula for residual distinctions. -/
theorem residual_iff_required_and_subset_incLoss (I : Coalition J) (d : D) :
    A.Residual I d ↔ A.Required d ∧ Coalition.Subset I (A.IncLoss d) := by
  constructor
  · intro h
    exact ⟨h.1, fun j hj => ⟨h.1, h.2 j hj⟩⟩
  · intro h
    exact ⟨h.1, fun j hj => (h.2 j hj).2⟩

/-- Residuals are contravariant on coalitions. -/
theorem residual_mono {I K : Coalition J} :
    Coalition.Subset I K → ∀ d, A.Residual K d → A.Residual I d := by
  intro hSub d hRes
  exact ⟨hRes.1, fun j hj => hRes.2 j (hSub j hj)⟩

/-- Residual restriction map along `I ⊆ K`. -/
def ResidualRestriction {I K : Coalition J}
    (hSub : Coalition.Subset I K) (d : D) :
    A.Residual K d → A.Residual I d :=
  fun hRes => A.residual_mono hSub d hRes

/--
The residual presheaf over the coalition order.

This is intentionally a small explicit structure rather than an imported categorical object:
it records the residual fiber above each coalition and the contravariant restriction map
along inclusions `I ⊆ K`.
-/
structure ResidualPresheaf where
  Obj : Coalition J → D → Prop
  restrict : ∀ {I K : Coalition J}, Coalition.Subset I K → ∀ d, Obj K d → Obj I d
  obj_iff_residual : ∀ I d, Obj I d ↔ A.Residual I d

/-- The canonical residual presheaf generated by an incidence system. -/
def residualPresheaf : A.ResidualPresheaf where
  Obj := A.Residual
  restrict := by
    intro I K hSub d hRes
    exact A.ResidualRestriction hSub d hRes
  obj_iff_residual := by
    intro I d
    rfl

/-- The canonical residual presheaf has the expected fibers. -/
theorem residualPresheaf_obj_iff (I : Coalition J) (d : D) :
    A.residualPresheaf.Obj I d ↔ A.Residual I d := by
  rfl

/-- The canonical residual presheaf restriction is residual monotonicity. -/
theorem residualPresheaf_restrict
    {I K : Coalition J} (hSub : Coalition.Subset I K) (d : D) :
    A.residualPresheaf.Obj K d → A.residualPresheaf.Obj I d := by
  exact A.residualPresheaf.restrict hSub d

/-- Residual emptiness is monotone with respect to adding interfaces. -/
theorem residualEmpty_mono {I K : Coalition J} :
    Coalition.Subset I K → A.ResidualEmpty I → A.ResidualEmpty K := by
  intro hSub hEmpty d hResK
  exact hEmpty d (A.residual_mono hSub d hResK)

/-- A covering coalition has empty residual. This direction is fully constructive. -/
theorem residualEmpty_of_coveringCoalition (I : Coalition J) :
    A.CoveringCoalition I → A.ResidualEmpty I := by
  intro hCover d hRes
  rcases hCover d hRes.1 with ⟨j, hjI, hjSep⟩
  exact A.separates_not_loss hjSep (hRes.2 j hjI)

/-- `Closed` is definitionally the witness-style covering condition. -/
theorem closed_iff_coveringCoalition (I : Coalition J) :
    A.Closed I ↔ A.CoveringCoalition I := by
  rfl

/-- Closed coalitions have empty residual. -/
theorem residualEmpty_of_closed (I : Coalition J) :
    A.Closed I → A.ResidualEmpty I := by
  intro hClosed
  exact A.residualEmpty_of_coveringCoalition I hClosed

/-- Covering is monotone with respect to adding interfaces. -/
theorem coveringCoalition_mono {I K : Coalition J} :
    Coalition.Subset I K → A.CoveringCoalition I → A.CoveringCoalition K := by
  intro hSub hCover d hd
  rcases hCover d hd with ⟨j, hjI, hjSep⟩
  exact ⟨j, hSub j hjI, hjSep⟩

/-- Closedness is monotone with respect to adding interfaces. -/
theorem closed_mono {I K : Coalition J} :
    Coalition.Subset I K → A.Closed I → A.Closed K := by
  intro hSub hClosed
  exact A.coveringCoalition_mono hSub hClosed

/-- Minimal covers are covers. -/
theorem coveringCoalition_of_minimalCoveringCoalition (I : Coalition J) :
    A.MinimalCoveringCoalition I → A.CoveringCoalition I := by
  intro h
  exact h.1

/-- Minimal covers are closed coalitions. -/
theorem closed_of_minimalCoveringCoalition (I : Coalition J) :
    A.MinimalCoveringCoalition I → A.Closed I := by
  intro h
  exact h.1

/-!
## Local gluing of covers

This is the first genuine geometric theorem: if local distinction domains cover
the required distinctions, and each local domain is covered by a local coalition,
then the union coalition covers globally.
-/

/-- A coalition covers a local domain of distinctions. -/
def LocalCoveringCoalition (Domain : D → Prop) (I : Coalition J) : Prop :=
  ∀ d, A.Required d → Domain d → ∃ j, I j ∧ A.Separates j d

/-- Local covers glue to a global cover. -/
theorem coveringCoalition_of_local_covers
    {T : Type w} (Domain : T → D → Prop) (I : T → Coalition J)
    (hDomainCover : ∀ d, A.Required d → ∃ t, Domain t d)
    (hLocal : ∀ t, A.LocalCoveringCoalition (Domain t) (I t)) :
    A.CoveringCoalition (Coalition.iUnion I) := by
  intro d hd
  rcases hDomainCover d hd with ⟨t, hdt⟩
  rcases hLocal t d hd hdt with ⟨j, hjI, hjSep⟩
  exact ⟨j, Coalition.mem_iUnion I t j hjI, hjSep⟩

/-!
## Incidence isomorphisms

The first robust external geometry is not a general observation morphism, but an
isomorphism of abstract incidence systems. This keeps the invariance theorem
small, explicit, and constructive.
-/

/-- Isomorphism of abstract incidence systems, with pointwise preservation/reflection. -/
structure IncidenceIso {D' : Type u} {J' : Type v}
    (B : AbstractIncidenceSystem D' J') where
  toD : D → D'
  invD : D' → D
  leftD : ∀ d, invD (toD d) = d
  rightD : ∀ d', toD (invD d') = d'
  toJ : J → J'
  invJ : J' → J
  leftJ : ∀ j, invJ (toJ j) = j
  rightJ : ∀ j', toJ (invJ j') = j'
  required_iff : ∀ d, A.Required d ↔ B.Required (toD d)
  loss_iff : ∀ j d, A.Loss j d ↔ B.Loss (toJ j) (toD d)
  separates_iff : ∀ j d, A.Separates j d ↔ B.Separates (toJ j) (toD d)

namespace IncidenceIso

variable {D' : Type u} {J' : Type v}
variable {B : AbstractIncidenceSystem D' J'}
variable (e : A.IncidenceIso B)

/-- Image of a coalition along an incidence isomorphism. -/
def mapCoalition (I : Coalition J) : Coalition J' :=
  fun j' => ∃ j, I j ∧ e.toJ j = j'

/-- Preimage of a coalition along an incidence isomorphism. -/
def preimageCoalition (I' : Coalition J') : Coalition J :=
  fun j => I' (e.toJ j)

/-- Interface map of an incidence isomorphism is injective. -/
theorem toJ_injective {j₁ j₂ : J} :
    e.toJ j₁ = e.toJ j₂ → j₁ = j₂ := by
  intro h
  calc
    j₁ = e.invJ (e.toJ j₁) := (e.leftJ j₁).symm
    _ = e.invJ (e.toJ j₂) := by rw [h]
    _ = j₂ := e.leftJ j₂

/-- Every member maps into the image coalition. -/
theorem mem_mapCoalition (I : Coalition J) (j : J) :
    I j → mapCoalition (A := A) (B := B) e I (e.toJ j) := by
  intro hj
  exact ⟨j, hj, rfl⟩

/-- Image of coalitions is monotone. -/
theorem mapCoalition_mono {I K : Coalition J} :
    Coalition.Subset I K →
      Coalition.Subset
        (mapCoalition (A := A) (B := B) e I)
        (mapCoalition (A := A) (B := B) e K) := by
  intro hSub j' hj'
  rcases hj' with ⟨j, hjI, hjEq⟩
  exact ⟨j, hSub j hjI, hjEq⟩

/-- Preimage of coalitions is monotone. -/
theorem preimageCoalition_mono {I' K' : Coalition J'} :
    Coalition.Subset I' K' →
      Coalition.Subset
        (preimageCoalition (A := A) (B := B) e I')
        (preimageCoalition (A := A) (B := B) e K') := by
  intro hSub j hj
  exact hSub (e.toJ j) hj

/-- A subcoalition of the image pulls back to a subcoalition of the original coalition. -/
theorem preimage_subset_of_subset_map {I : Coalition J} {K' : Coalition J'} :
    Coalition.Subset K' (mapCoalition (A := A) (B := B) e I) →
      Coalition.Subset (preimageCoalition (A := A) (B := B) e K') I := by
  intro hSub j hj
  have hMap : mapCoalition (A := A) (B := B) e I (e.toJ j) := hSub (e.toJ j) hj
  rcases hMap with ⟨i, hiI, hiEq⟩
  have hij : i = j := toJ_injective (A := A) (B := B) e hiEq
  cases hij
  exact hiI

/-- A proper subcoalition of an image pulls back to a proper subcoalition. -/
theorem preimage_proper_of_proper_map {I : Coalition J} {K' : Coalition J'} :
    Coalition.Proper K' (mapCoalition (A := A) (B := B) e I) →
      Coalition.Proper (preimageCoalition (A := A) (B := B) e K') I := by
  intro hProper
  refine ⟨preimage_subset_of_subset_map (A := A) (B := B) e hProper.1, ?_⟩
  rcases hProper.2 with ⟨j', hjMap, hjNotK⟩
  rcases hjMap with ⟨j, hjI, hjEq⟩
  refine ⟨j, hjI, ?_⟩
  intro hjPre
  apply hjNotK
  cases hjEq
  exact hjPre

/-- Proper subcoalitions map to proper subcoalitions. -/
theorem mapCoalition_proper {I K : Coalition J} :
    Coalition.Proper K I →
      Coalition.Proper
        (mapCoalition (A := A) (B := B) e K)
        (mapCoalition (A := A) (B := B) e I) := by
  intro hProper
  refine ⟨mapCoalition_mono (A := A) (B := B) e hProper.1, ?_⟩
  rcases hProper.2 with ⟨j, hjI, hjNotK⟩
  refine ⟨e.toJ j, mem_mapCoalition (A := A) (B := B) e I j hjI, ?_⟩
  intro hjMapK
  rcases hjMapK with ⟨i, hiK, hiEq⟩
  have hij : i = j := toJ_injective (A := A) (B := B) e hiEq
  cases hij
  exact hjNotK hiK

/-- Residuals are preserved and reflected by incidence isomorphisms. -/
theorem residual_iff_mapCoalition (I : Coalition J) (d : D) :
    A.Residual I d ↔ B.Residual (mapCoalition (A := A) (B := B) e I) (e.toD d) := by
  constructor
  · intro h
    refine ⟨(e.required_iff d).1 h.1, ?_⟩
    intro j' hj'
    rcases hj' with ⟨j, hjI, hjEq⟩
    have hLossA : A.Loss j d := h.2 j hjI
    have hLossB : B.Loss (e.toJ j) (e.toD d) := (e.loss_iff j d).1 hLossA
    cases hjEq
    exact hLossB
  · intro h
    refine ⟨(e.required_iff d).2 h.1, ?_⟩
    intro j hjI
    have hLossB : B.Loss (e.toJ j) (e.toD d) :=
      h.2 (e.toJ j) (mem_mapCoalition (A := A) (B := B) e I j hjI)
    exact (e.loss_iff j d).2 hLossB

/-- Covering coalitions are preserved by incidence isomorphisms. -/
theorem coveringCoalition_map (I : Coalition J) :
    A.CoveringCoalition I → B.CoveringCoalition (mapCoalition (A := A) (B := B) e I) := by
  intro hCover d' hd'
  let d : D := e.invD d'
  have hdTo : B.Required (e.toD d) := by
    unfold d
    rw [e.rightD d']
    exact hd'
  have hdA : A.Required d := (e.required_iff d).2 hdTo
  rcases hCover d hdA with ⟨j, hjI, hjSepA⟩
  have hjSepB : B.Separates (e.toJ j) (e.toD d) :=
    (e.separates_iff j d).1 hjSepA
  refine ⟨e.toJ j, mem_mapCoalition (A := A) (B := B) e I j hjI, ?_⟩
  simpa [d, e.rightD d'] using hjSepB

/-- Covering coalitions are reflected by incidence isomorphisms. -/
theorem coveringCoalition_of_map (I : Coalition J) :
    B.CoveringCoalition (mapCoalition (A := A) (B := B) e I) → A.CoveringCoalition I := by
  intro hCover d hd
  have hdB : B.Required (e.toD d) := (e.required_iff d).1 hd
  rcases hCover (e.toD d) hdB with ⟨j', hjMap, hjSepB⟩
  rcases hjMap with ⟨j, hjI, hjEq⟩
  cases hjEq
  have hjSepA : A.Separates j d := (e.separates_iff j d).2 hjSepB
  exact ⟨j, hjI, hjSepA⟩

/-- Covering is invariant under incidence isomorphism. -/
theorem coveringCoalition_iff_map (I : Coalition J) :
    A.CoveringCoalition I ↔ B.CoveringCoalition (mapCoalition (A := A) (B := B) e I) := by
  constructor
  · exact coveringCoalition_map (A := A) (B := B) e I
  · exact coveringCoalition_of_map (A := A) (B := B) e I

/-- Closedness is invariant under incidence isomorphism. -/
theorem closed_iff_map (I : Coalition J) :
    A.Closed I ↔ B.Closed (mapCoalition (A := A) (B := B) e I) := by
  exact coveringCoalition_iff_map (A := A) (B := B) e I

/-- A cover of a coalition in the target pulls back to a cover of the preimage coalition. -/
theorem coveringCoalition_preimage_of_covering {K' : Coalition J'} :
    B.CoveringCoalition K' →
      A.CoveringCoalition (preimageCoalition (A := A) (B := B) e K') := by
  intro hCover d hd
  have hdB : B.Required (e.toD d) := (e.required_iff d).1 hd
  rcases hCover (e.toD d) hdB with ⟨j', hjK, hjSepB⟩
  refine ⟨e.invJ j', ?_, ?_⟩
  · unfold preimageCoalition
    rw [e.rightJ j']
    exact hjK
  · have hjSepTo : B.Separates (e.toJ (e.invJ j')) (e.toD d) := by
      rw [e.rightJ j']
      exact hjSepB
    exact (e.separates_iff (e.invJ j') d).2 hjSepTo

/-- Minimal covers are preserved by incidence isomorphisms. -/
theorem minimalCoveringCoalition_map (I : Coalition J) :
    A.MinimalCoveringCoalition I →
      B.MinimalCoveringCoalition (mapCoalition (A := A) (B := B) e I) := by
  intro hMin
  refine ⟨coveringCoalition_map (A := A) (B := B) e I hMin.1, ?_⟩
  intro K' hProperK' hCoverK'
  have hPreProper :
      Coalition.Proper (preimageCoalition (A := A) (B := B) e K') I :=
    preimage_proper_of_proper_map (A := A) (B := B) e hProperK'
  have hPreCover :
      A.CoveringCoalition (preimageCoalition (A := A) (B := B) e K') :=
    coveringCoalition_preimage_of_covering (A := A) (B := B) e hCoverK'
  exact hMin.2 (preimageCoalition (A := A) (B := B) e K') hPreProper hPreCover

/-- Minimal covers are reflected by incidence isomorphisms. -/
theorem minimalCoveringCoalition_of_map (I : Coalition J) :
    B.MinimalCoveringCoalition (mapCoalition (A := A) (B := B) e I) →
      A.MinimalCoveringCoalition I := by
  intro hMin
  refine ⟨coveringCoalition_of_map (A := A) (B := B) e I hMin.1, ?_⟩
  intro K hProperK hCoverK
  have hMapProper :
      Coalition.Proper
        (mapCoalition (A := A) (B := B) e K)
        (mapCoalition (A := A) (B := B) e I) :=
    mapCoalition_proper (A := A) (B := B) e hProperK
  have hMapCover :
      B.CoveringCoalition (mapCoalition (A := A) (B := B) e K) :=
    coveringCoalition_map (A := A) (B := B) e K hCoverK
  exact hMin.2 (mapCoalition (A := A) (B := B) e K) hMapProper hMapCover

/-- Minimal covering is invariant under incidence isomorphism. -/
theorem minimalCoveringCoalition_iff_map (I : Coalition J) :
    A.MinimalCoveringCoalition I ↔
      B.MinimalCoveringCoalition (mapCoalition (A := A) (B := B) e I) := by
  constructor
  · exact minimalCoveringCoalition_map (A := A) (B := B) e I
  · exact minimalCoveringCoalition_of_map (A := A) (B := B) e I

end IncidenceIso

end AbstractIncidenceSystem

/-!
## Concrete observation systems

This layer is deliberately after the abstract incidence geometry. It shows that
ordinary observations realize the abstract system, but the geometric theorems do
not depend on the observation representation.
-/

/-- Homogeneous concrete observation system. -/
structure ObservationSystem (X : Type u) (J : Type v) (V : Type w) (Y : Type y) where
  sigma : X → Y
  obs : J → X → V

namespace ObservationSystem

variable {X : Type u} {J : Type v} {V : Type w} {Y : Type y}
variable (O : ObservationSystem X J V Y)

/-- Required pair distinction for a concrete observation system. -/
def RequiredPair (p : X × X) : Prop :=
  O.sigma p.1 ≠ O.sigma p.2

/-- Loss of a required pair distinction by a concrete interface. -/
def LossPair (j : J) (p : X × X) : Prop :=
  O.RequiredPair p ∧ O.obs j p.1 = O.obs j p.2

/-- Separation of a required pair distinction by a concrete interface. -/
def SeparatesPair (j : J) (p : X × X) : Prop :=
  O.RequiredPair p ∧ O.obs j p.1 ≠ O.obs j p.2

/-- Concrete observations realize an abstract incidence system on pairs of states. -/
def toAbstractIncidenceSystem : AbstractIncidenceSystem (X × X) J where
  Required := O.RequiredPair
  Loss := O.LossPair
  Separates := O.SeparatesPair
  separates_required := by
    intro j p h
    exact h.1
  separates_not_loss := by
    intro j p hSep hLoss
    exact hSep.2 hLoss.2

/-- Pointwise realization of an abstract incidence system by concrete observations. -/
structure RealizesIncidenceSystem (A : AbstractIncidenceSystem (X × X) J) : Prop where
  required_iff : ∀ p, A.Required p ↔ O.RequiredPair p
  loss_iff : ∀ j p, A.Loss j p ↔ O.LossPair j p
  separates_iff : ∀ j p, A.Separates j p ↔ O.SeparatesPair j p

/-- The canonical abstract incidence system is realized by its originating observation system. -/
theorem realizes_toAbstractIncidenceSystem :
    O.RealizesIncidenceSystem O.toAbstractIncidenceSystem := by
  exact
    { required_iff := by
        intro p
        rfl
      loss_iff := by
        intro j p
        rfl
      separates_iff := by
        intro j p
        rfl }

/-- Pointwise realization statement for required distinctions. -/
theorem realizes_required (p : X × X) :
    (O.toAbstractIncidenceSystem).Required p ↔ O.RequiredPair p := by
  rfl

/-- Pointwise realization statement for losses. -/
theorem realizes_loss (j : J) (p : X × X) :
    (O.toAbstractIncidenceSystem).Loss j p ↔ O.LossPair j p := by
  rfl

/-- Pointwise realization statement for separations. -/
theorem realizes_separates (j : J) (p : X × X) :
    (O.toAbstractIncidenceSystem).Separates j p ↔ O.SeparatesPair j p := by
  rfl

end ObservationSystem

end MultiInterfaceGeometry
end Standalone
end PrimitiveHolonomy

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.residual_mono
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.residualPresheaf
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.residualPresheaf_restrict
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.residualEmpty_mono
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.closed_mono
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.coveringCoalition_of_local_covers
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.IncidenceIso.residual_iff_mapCoalition
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.IncidenceIso.coveringCoalition_iff_map
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.IncidenceIso.closed_iff_map
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.IncidenceIso.minimalCoveringCoalition_iff_map
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.toAbstractIncidenceSystem
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.realizes_toAbstractIncidenceSystem
/- AXIOM_AUDIT_END -/
