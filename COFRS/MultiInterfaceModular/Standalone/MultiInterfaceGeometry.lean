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
* finite mediated cover extensions,
* observation systems as concrete realizations of an abstract incidence system.
* concrete state-readout mediators `X → Fin n`.

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

/-!
## Finite mediated covers

A mediator is represented as a new finite interface whose separation behavior is
controlled by a finite readout `Fin n`. At this abstract incidence level, the
mediator is not an oracle for the target: it is a finite profile with explicit
loss/separation data and a finite predicate readout.
-/

/-- A finite mediator profile over an abstract incidence system. -/
structure FiniteMediatorProfile (n : Nat) where
  code : D → Fin n
  pred : Fin n → Prop
  Loss : D → Prop
  Separates : D → Prop
  separates_iff : ∀ d, Separates d ↔ A.Required d ∧ pred (code d)
  separates_not_loss : ∀ {d}, Separates d → ¬ Loss d

/--
Parametric admissibility predicate for finite mediators.

At the abstract incidence level, admissibility cannot be fixed once and for all:
different concrete realizations may impose different allowed classes of mediators.
This parameter prevents confusing arbitrary finite cover extensions with legitimate
mediators.
-/
abbrev AdmissibleMediatorProfile (n : Nat) :=
  A.FiniteMediatorProfile n → Prop

namespace FiniteMediatorProfile

variable {n : Nat}
variable (M : A.FiniteMediatorProfile n)

/-- A mediator separation always targets a required distinction. -/
theorem separates_required {d : D} :
    M.Separates d → A.Required d := by
  intro h
  exact ((M.separates_iff d).1 h).1

end FiniteMediatorProfile

/-- Extend an incidence system with one finite mediator interface. -/
def extendWithMediator {n : Nat} (M : A.FiniteMediatorProfile n) :
    AbstractIncidenceSystem D (Option J) where
  Required := A.Required
  Loss := fun j d =>
    match j with
    | none => M.Loss d
    | some j0 => A.Loss j0 d
  Separates := fun j d =>
    match j with
    | none => M.Separates d
    | some j0 => A.Separates j0 d
  separates_required := by
    intro j d h
    cases j with
    | none =>
        exact ((M.separates_iff d).1 h).1
    | some j0 =>
        exact A.separates_required h
  separates_not_loss := by
    intro j d hSep hLoss
    cases j with
    | none =>
        exact M.separates_not_loss hSep hLoss
    | some j0 =>
        exact A.separates_not_loss hSep hLoss

/-- Lift a coalition without adding the mediator. -/
def liftCoalition (I : Coalition J) : Coalition (Option J) :=
  fun j =>
    match j with
    | none => False
    | some j0 => I j0

/-- Lift a coalition and include the mediator as an available interface. -/
def withMediatorCoalition (I : Coalition J) : Coalition (Option J) :=
  fun j =>
    match j with
    | none => True
    | some j0 => I j0

/-- A finite mediator turns `I` into a cover in the extended incidence system. -/
def MediatedCover {n : Nat} (I : Coalition J) (M : A.FiniteMediatorProfile n) : Prop :=
  (A.extendWithMediator M).CoveringCoalition (withMediatorCoalition I)

/--
Proper mediated cover: the original coalition does not cover directly, but covers
after the finite mediator is added.

This separates genuine mediation from the degenerate case where `I` was already
a cover and the mediator is irrelevant.
-/
def ProperMediatedCover {n : Nat} (I : Coalition J) (M : A.FiniteMediatorProfile n) : Prop :=
  ¬ A.CoveringCoalition I ∧ A.MediatedCover I M

/-- Existence of a finite cover extension of dimension `n`. -/
def FiniteCoverExtension (I : Coalition J) (n : Nat) : Prop :=
  ∃ M : A.FiniteMediatorProfile n, A.MediatedCover I M

/-- Existence of a genuine finite mediation of dimension `n`. -/
def ProperFiniteCoverExtension (I : Coalition J) (n : Nat) : Prop :=
  ∃ M : A.FiniteMediatorProfile n, A.ProperMediatedCover I M

/-- Exact minimal mediated cover dimension. -/
def MinimalMediatedCover (I : Coalition J) (n : Nat) : Prop :=
  A.FiniteCoverExtension I n ∧
    ∀ m : Nat, m < n → ¬ A.FiniteCoverExtension I m

/-- Exact minimal proper mediated cover dimension. -/
def ProperMinimalMediatedCover (I : Coalition J) (n : Nat) : Prop :=
  A.ProperFiniteCoverExtension I n ∧
    ∀ m : Nat, m < n → ¬ A.ProperFiniteCoverExtension I m

/-- Direct covers induce mediated covers for any finite mediator profile. -/
theorem mediatedCover_of_coveringCoalition {n : Nat} (I : Coalition J)
    (M : A.FiniteMediatorProfile n) :
    A.CoveringCoalition I → A.MediatedCover I M := by
  intro hCover d hd
  rcases hCover d hd with ⟨j, hjI, hjSep⟩
  exact ⟨some j, hjI, hjSep⟩

/--
Normal form for mediated cover.

Adding the mediator to `I` covers exactly when every required distinction is
separated either by the base coalition or by the mediator interface.
-/
theorem mediatedCover_iff_base_or_mediator {n : Nat}
    (I : Coalition J) (M : A.FiniteMediatorProfile n) :
    A.MediatedCover I M ↔
      ∀ d, A.Required d →
        (∃ j, I j ∧ A.Separates j d) ∨ M.Separates d := by
  constructor
  · intro hMed d hd
    rcases hMed d hd with ⟨j, hjI, hjSep⟩
    cases j with
    | none =>
        exact Or.inr hjSep
    | some j0 =>
        exact Or.inl ⟨j0, hjI, hjSep⟩
  · intro h d hd
    cases h d hd with
    | inl hBase =>
        rcases hBase with ⟨j, hjI, hjSep⟩
        exact ⟨some j, hjI, hjSep⟩
    | inr hMed =>
        exact ⟨none, True.intro, hMed⟩

/-- A mediated cover gives a finite cover extension. -/
theorem finiteCoverExtension_of_mediatedCover {n : Nat} (I : Coalition J)
    (M : A.FiniteMediatorProfile n) :
    A.MediatedCover I M → A.FiniteCoverExtension I n := by
  intro h
  exact ⟨M, h⟩

/--
If `I + M` covers, then the mediator separates every residual distinction left by `I`.

This is the geometric content of mediation: the new finite interface must act on
the residual defect of the base coalition.
-/
theorem mediator_separates_residual_of_mediatedCover {n : Nat}
    (I : Coalition J) (M : A.FiniteMediatorProfile n) :
    A.MediatedCover I M → ∀ d, A.Residual I d → M.Separates d := by
  intro hMed d hRes
  rcases hMed d hRes.1 with ⟨j, hjI, hjSep⟩
  cases j with
  | none =>
      exact hjSep
  | some j0 =>
      exact False.elim (A.separates_not_loss hjSep (hRes.2 j0 hjI))

/-- Proper mediated covers are mediated covers. -/
theorem mediatedCover_of_properMediatedCover {n : Nat} (I : Coalition J)
    (M : A.FiniteMediatorProfile n) :
    A.ProperMediatedCover I M → A.MediatedCover I M := by
  intro h
  exact h.2

/-- Proper mediated covers certify that the base coalition did not cover directly. -/
theorem not_coveringCoalition_of_properMediatedCover {n : Nat} (I : Coalition J)
    (M : A.FiniteMediatorProfile n) :
    A.ProperMediatedCover I M → ¬ A.CoveringCoalition I := by
  intro h
  exact h.1

/-- A proper mediated cover gives a proper finite cover extension. -/
theorem properFiniteCoverExtension_of_properMediatedCover {n : Nat} (I : Coalition J)
    (M : A.FiniteMediatorProfile n) :
    A.ProperMediatedCover I M → A.ProperFiniteCoverExtension I n := by
  intro h
  exact ⟨M, h⟩

/-- Proper finite cover extensions are finite cover extensions. -/
theorem finiteCoverExtension_of_properFiniteCoverExtension (I : Coalition J) (n : Nat) :
    A.ProperFiniteCoverExtension I n → A.FiniteCoverExtension I n := by
  intro h
  rcases h with ⟨M, hProper⟩
  exact ⟨M, hProper.2⟩

/-- Existence of an admissible finite cover extension of dimension `n`. -/
def AdmissibleFiniteCoverExtension
    (Admissible : {n : Nat} → A.FiniteMediatorProfile n → Prop)
    (I : Coalition J) (n : Nat) : Prop :=
  ∃ M : A.FiniteMediatorProfile n, Admissible M ∧ A.MediatedCover I M

/-- Existence of a genuine admissible finite mediation of dimension `n`. -/
def ProperAdmissibleFiniteCoverExtension
    (Admissible : {n : Nat} → A.FiniteMediatorProfile n → Prop)
    (I : Coalition J) (n : Nat) : Prop :=
  ∃ M : A.FiniteMediatorProfile n, Admissible M ∧ A.ProperMediatedCover I M

/-- Exact minimal admissible mediated cover dimension. -/
def MinimalAdmissibleMediatedCover
    (Admissible : {n : Nat} → A.FiniteMediatorProfile n → Prop)
    (I : Coalition J) (n : Nat) : Prop :=
  A.AdmissibleFiniteCoverExtension Admissible I n ∧
    ∀ m : Nat, m < n → ¬ A.AdmissibleFiniteCoverExtension Admissible I m

/-- Exact minimal proper admissible mediated cover dimension. -/
def ProperMinimalAdmissibleMediatedCover
    (Admissible : {n : Nat} → A.FiniteMediatorProfile n → Prop)
    (I : Coalition J) (n : Nat) : Prop :=
  A.ProperAdmissibleFiniteCoverExtension Admissible I n ∧
    ∀ m : Nat, m < n → ¬ A.ProperAdmissibleFiniteCoverExtension Admissible I m

/-- Admissible finite cover extensions are finite cover extensions. -/
theorem finiteCoverExtension_of_admissibleFiniteCoverExtension
    (Admissible : {n : Nat} → A.FiniteMediatorProfile n → Prop)
    (I : Coalition J) (n : Nat) :
    A.AdmissibleFiniteCoverExtension Admissible I n → A.FiniteCoverExtension I n := by
  intro h
  rcases h with ⟨M, _hAdm, hMed⟩
  exact ⟨M, hMed⟩

/-- Proper admissible finite cover extensions are proper finite cover extensions. -/
theorem properFiniteCoverExtension_of_properAdmissibleFiniteCoverExtension
    (Admissible : {n : Nat} → A.FiniteMediatorProfile n → Prop)
    (I : Coalition J) (n : Nat) :
    A.ProperAdmissibleFiniteCoverExtension Admissible I n →
      A.ProperFiniteCoverExtension I n := by
  intro h
  rcases h with ⟨M, _hAdm, hProper⟩
  exact ⟨M, hProper⟩

/-- Minimal admissible mediated cover implies admissible existence at that dimension. -/
theorem admissibleFiniteCoverExtension_of_minimalAdmissibleMediatedCover
    (Admissible : {n : Nat} → A.FiniteMediatorProfile n → Prop)
    (I : Coalition J) (n : Nat) :
    A.MinimalAdmissibleMediatedCover Admissible I n →
      A.AdmissibleFiniteCoverExtension Admissible I n := by
  intro h
  exact h.1

/-- Minimal admissible mediated cover excludes smaller admissible extensions. -/
theorem no_smaller_admissibleFiniteCoverExtension_of_minimalAdmissibleMediatedCover
    (Admissible : {n : Nat} → A.FiniteMediatorProfile n → Prop)
    (I : Coalition J) (n : Nat) :
    A.MinimalAdmissibleMediatedCover Admissible I n →
      ∀ m : Nat, m < n → ¬ A.AdmissibleFiniteCoverExtension Admissible I m := by
  intro h
  exact h.2

/-- Proper minimal admissible mediated cover implies proper admissible existence. -/
theorem properAdmissibleFiniteCoverExtension_of_properMinimalAdmissibleMediatedCover
    (Admissible : {n : Nat} → A.FiniteMediatorProfile n → Prop)
    (I : Coalition J) (n : Nat) :
    A.ProperMinimalAdmissibleMediatedCover Admissible I n →
      A.ProperAdmissibleFiniteCoverExtension Admissible I n := by
  intro h
  exact h.1

/-- Proper minimal admissible mediated cover excludes smaller proper admissible extensions. -/
theorem no_smaller_properAdmissibleFiniteCoverExtension_of_properMinimalAdmissibleMediatedCover
    (Admissible : {n : Nat} → A.FiniteMediatorProfile n → Prop)
    (I : Coalition J) (n : Nat) :
    A.ProperMinimalAdmissibleMediatedCover Admissible I n →
      ∀ m : Nat, m < n → ¬ A.ProperAdmissibleFiniteCoverExtension Admissible I m := by
  intro h
  exact h.2

/-- Minimal mediated cover implies existence at the stated dimension. -/
theorem finiteCoverExtension_of_minimalMediatedCover (I : Coalition J) (n : Nat) :
    A.MinimalMediatedCover I n → A.FiniteCoverExtension I n := by
  intro h
  exact h.1

/-- Minimal mediated cover excludes smaller finite cover extensions. -/
theorem no_smaller_finiteCoverExtension_of_minimalMediatedCover
    (I : Coalition J) (n : Nat) :
    A.MinimalMediatedCover I n →
      ∀ m : Nat, m < n → ¬ A.FiniteCoverExtension I m := by
  intro h
  exact h.2

/-- Proper minimal mediated cover implies proper existence at the stated dimension. -/
theorem properFiniteCoverExtension_of_properMinimalMediatedCover
    (I : Coalition J) (n : Nat) :
    A.ProperMinimalMediatedCover I n → A.ProperFiniteCoverExtension I n := by
  intro h
  exact h.1

/-- Proper minimal mediated cover excludes smaller proper finite cover extensions. -/
theorem no_smaller_properFiniteCoverExtension_of_properMinimalMediatedCover
    (I : Coalition J) (n : Nat) :
    A.ProperMinimalMediatedCover I n →
      ∀ m : Nat, m < n → ¬ A.ProperFiniteCoverExtension I m := by
  intro h
  exact h.2

/-- Proper minimal mediated covers yield ordinary finite cover extensions. -/
theorem finiteCoverExtension_of_properMinimalMediatedCover (I : Coalition J) (n : Nat) :
    A.ProperMinimalMediatedCover I n → A.FiniteCoverExtension I n := by
  intro h
  exact A.finiteCoverExtension_of_properFiniteCoverExtension I n h.1

/--
The mediator descends to a subcoalition if every distinction it separates is
already separated by that subcoalition.

This is the abstract incidence analogue of non-descent: we cannot talk about
factorization of concrete observations here, so we talk about factorization of
the mediator's separation power.
-/
def MediatorDescendsTo {n : Nat} (K : Coalition J) (M : A.FiniteMediatorProfile n) : Prop :=
  ∀ d, A.Required d → M.Separates d → ∃ j, K j ∧ A.Separates j d

/-- Descent targeted to the residual left by a base coalition `I`. -/
def MediatorDescendsToOnResidual {n : Nat}
    (I K : Coalition J) (M : A.FiniteMediatorProfile n) : Prop :=
  ∀ d, A.Residual I d → M.Separates d → ∃ j, K j ∧ A.Separates j d

/-- A mediator is non-descending over `I` if it descends to no proper subcoalition of `I`. -/
def NonDescent {n : Nat} (I : Coalition J) (M : A.FiniteMediatorProfile n) : Prop :=
  ∀ K, Coalition.Proper K I → ¬ A.MediatorDescendsTo K M

/-- Residual-targeted non-descent over `I`. -/
def NonDescentOnResidual {n : Nat} (I : Coalition J) (M : A.FiniteMediatorProfile n) : Prop :=
  ∀ K, Coalition.Proper K I → ¬ A.MediatorDescendsToOnResidual I K M

/-- A mediated cover with non-descent to proper subcoalitions. -/
def IrreducibleMediatedCover {n : Nat} (I : Coalition J) (M : A.FiniteMediatorProfile n) :
    Prop :=
  A.MediatedCover I M ∧ A.NonDescent I M

/-- A proper mediated cover with residual-targeted non-descent. -/
def ProperIrreducibleMediatedCover {n : Nat} (I : Coalition J) (M : A.FiniteMediatorProfile n) :
    Prop :=
  A.ProperMediatedCover I M ∧ A.NonDescentOnResidual I M

/-- Irreducible mediated covers are mediated covers. -/
theorem mediatedCover_of_irreducibleMediatedCover {n : Nat} (I : Coalition J)
    (M : A.FiniteMediatorProfile n) :
    A.IrreducibleMediatedCover I M → A.MediatedCover I M := by
  intro h
  exact h.1

/-- Irreducible mediated covers have non-descent. -/
theorem nonDescent_of_irreducibleMediatedCover {n : Nat} (I : Coalition J)
    (M : A.FiniteMediatorProfile n) :
    A.IrreducibleMediatedCover I M → A.NonDescent I M := by
  intro h
  exact h.2

/-- Proper irreducible mediated covers are proper mediated covers. -/
theorem properMediatedCover_of_properIrreducibleMediatedCover {n : Nat}
    (I : Coalition J) (M : A.FiniteMediatorProfile n) :
    A.ProperIrreducibleMediatedCover I M → A.ProperMediatedCover I M := by
  intro h
  exact h.1

/-- Proper irreducible mediated covers have residual-targeted non-descent. -/
theorem nonDescentOnResidual_of_properIrreducibleMediatedCover {n : Nat}
    (I : Coalition J) (M : A.FiniteMediatorProfile n) :
    A.ProperIrreducibleMediatedCover I M → A.NonDescentOnResidual I M := by
  intro h
  exact h.2

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

/-!
## Concrete state-readout mediators

The abstract mediator layer allows arbitrary finite incidence profiles. The
concrete observation layer adds the stricter admissible object: a finite readout
of states, `readout : X → Fin n`, whose action on distinctions is induced by
the two endpoint values of the pair.

This is the non-oracle layer: the mediator reads states, not distinctions.
-/

/-- Loss of a required pair distinction by a finite state readout. -/
def StateReadoutLoss {n : Nat} (readout : X → Fin n) (p : X × X) : Prop :=
  O.RequiredPair p ∧ readout p.1 = readout p.2

/-- Separation of a required pair distinction by a finite state readout. -/
def StateReadoutSeparates {n : Nat} (readout : X → Fin n) (p : X × X) : Prop :=
  O.RequiredPair p ∧ readout p.1 ≠ readout p.2

/-- A state-readout separation always targets a required pair distinction. -/
theorem stateReadoutSeparates_required {n : Nat}
    (readout : X → Fin n) {p : X × X} :
    O.StateReadoutSeparates readout p → O.RequiredPair p := by
  intro h
  exact h.1

/-- A state readout cannot both separate and lose the same pair distinction. -/
theorem stateReadoutSeparates_not_loss {n : Nat}
    (readout : X → Fin n) {p : X × X} :
    O.StateReadoutSeparates readout p → ¬ O.StateReadoutLoss readout p := by
  intro hSep hLoss
  exact hSep.2 hLoss.2

/-- Extend a concrete observation incidence system with one finite state readout. -/
def extendWithStateReadout {n : Nat} (readout : X → Fin n) :
    AbstractIncidenceSystem (X × X) (Option J) where
  Required := O.RequiredPair
  Loss := fun j p =>
    match j with
    | none => O.StateReadoutLoss readout p
    | some j0 => O.LossPair j0 p
  Separates := fun j p =>
    match j with
    | none => O.StateReadoutSeparates readout p
    | some j0 => O.SeparatesPair j0 p
  separates_required := by
    intro j p h
    cases j with
    | none =>
        exact h.1
    | some _j0 =>
        exact h.1
  separates_not_loss := by
    intro j p hSep hLoss
    cases j with
    | none =>
        exact O.stateReadoutSeparates_not_loss readout hSep hLoss
    | some _j0 =>
        exact hSep.2 hLoss.2

/-- Lift a base coalition and include the concrete state-readout mediator. -/
def withStateReadoutCoalition (I : Coalition J) : Coalition (Option J) :=
  fun j =>
    match j with
    | none => True
    | some j0 => I j0

/-- A concrete finite readout turns `I` into a cover in the extended observation system. -/
def StateReadoutMediatedCover {n : Nat}
    (I : Coalition J) (readout : X → Fin n) : Prop :=
  (O.extendWithStateReadout readout).CoveringCoalition (withStateReadoutCoalition I)

/--
Normal form for concrete state-readout mediated cover.

Every required pair distinction is separated either by the base coalition or by
the finite state readout.
-/
theorem stateReadoutMediatedCover_iff_base_or_readout {n : Nat}
    (I : Coalition J) (readout : X → Fin n) :
    O.StateReadoutMediatedCover I readout ↔
      ∀ p, O.RequiredPair p →
        (∃ j, I j ∧ O.SeparatesPair j p) ∨ O.StateReadoutSeparates readout p := by
  constructor
  · intro hMed p hp
    rcases hMed p hp with ⟨j, hjI, hjSep⟩
    cases j with
    | none =>
        exact Or.inr hjSep
    | some j0 =>
        exact Or.inl ⟨j0, hjI, hjSep⟩
  · intro h p hp
    cases h p hp with
    | inl hBase =>
        rcases hBase with ⟨j, hjI, hjSep⟩
        exact ⟨some j, hjI, hjSep⟩
    | inr hReadout =>
        exact ⟨none, True.intro, hReadout⟩

/-- Proper concrete mediated cover: `I` fails directly but succeeds with the readout. -/
def ProperStateReadoutMediatedCover {n : Nat}
    (I : Coalition J) (readout : X → Fin n) : Prop :=
  ¬ (O.toAbstractIncidenceSystem).CoveringCoalition I ∧
    O.StateReadoutMediatedCover I readout

/-- Existence of a concrete state-readout cover extension of dimension `n`. -/
def StateReadoutCoverExtension (I : Coalition J) (n : Nat) : Prop :=
  ∃ readout : X → Fin n, O.StateReadoutMediatedCover I readout

/-- Existence of a genuine concrete state-readout mediation of dimension `n`. -/
def ProperStateReadoutCoverExtension (I : Coalition J) (n : Nat) : Prop :=
  ∃ readout : X → Fin n, O.ProperStateReadoutMediatedCover I readout

/-- Exact minimal concrete state-readout mediated cover dimension. -/
def MinimalStateReadoutMediatedCover (I : Coalition J) (n : Nat) : Prop :=
  O.StateReadoutCoverExtension I n ∧
    ∀ m : Nat, m < n → ¬ O.StateReadoutCoverExtension I m

/-- Exact minimal proper concrete state-readout mediated cover dimension. -/
def ProperMinimalStateReadoutMediatedCover (I : Coalition J) (n : Nat) : Prop :=
  O.ProperStateReadoutCoverExtension I n ∧
    ∀ m : Nat, m < n → ¬ O.ProperStateReadoutCoverExtension I m

/--
If `I + readout` covers, then the readout separates every residual distinction
left by `I`.
-/
theorem stateReadout_separates_residual_of_mediatedCover {n : Nat}
    (I : Coalition J) (readout : X → Fin n) :
    O.StateReadoutMediatedCover I readout →
      ∀ p, (O.toAbstractIncidenceSystem).Residual I p →
        O.StateReadoutSeparates readout p := by
  intro hMed p hRes
  rcases hMed p hRes.1 with ⟨j, hjI, hjSep⟩
  cases j with
  | none =>
      exact hjSep
  | some j0 =>
      exact False.elim ((O.toAbstractIncidenceSystem).separates_not_loss hjSep (hRes.2 j0 hjI))

/-- Proper concrete mediated covers are concrete mediated covers. -/
theorem stateReadoutMediatedCover_of_properStateReadoutMediatedCover {n : Nat}
    (I : Coalition J) (readout : X → Fin n) :
    O.ProperStateReadoutMediatedCover I readout →
      O.StateReadoutMediatedCover I readout := by
  intro h
  exact h.2

/-- Proper concrete mediated covers certify that the base coalition fails directly. -/
theorem not_coveringCoalition_of_properStateReadoutMediatedCover {n : Nat}
    (I : Coalition J) (readout : X → Fin n) :
    O.ProperStateReadoutMediatedCover I readout →
      ¬ (O.toAbstractIncidenceSystem).CoveringCoalition I := by
  intro h
  exact h.1

/-- Minimal concrete state-readout cover implies existence at that dimension. -/
theorem stateReadoutCoverExtension_of_minimalStateReadoutMediatedCover
    (I : Coalition J) (n : Nat) :
    O.MinimalStateReadoutMediatedCover I n →
      O.StateReadoutCoverExtension I n := by
  intro h
  exact h.1

/-- Minimal concrete state-readout cover excludes smaller concrete readouts. -/
theorem no_smaller_stateReadoutCoverExtension_of_minimalStateReadoutMediatedCover
    (I : Coalition J) (n : Nat) :
    O.MinimalStateReadoutMediatedCover I n →
      ∀ m : Nat, m < n → ¬ O.StateReadoutCoverExtension I m := by
  intro h
  exact h.2

/-- Proper minimal concrete state-readout cover implies proper existence. -/
theorem properStateReadoutCoverExtension_of_properMinimalStateReadoutMediatedCover
    (I : Coalition J) (n : Nat) :
    O.ProperMinimalStateReadoutMediatedCover I n →
      O.ProperStateReadoutCoverExtension I n := by
  intro h
  exact h.1

/-- Proper minimal concrete state-readout cover excludes smaller proper readout mediations. -/
theorem no_smaller_properStateReadoutCoverExtension_of_properMinimalStateReadoutMediatedCover
    (I : Coalition J) (n : Nat) :
    O.ProperMinimalStateReadoutMediatedCover I n →
      ∀ m : Nat, m < n → ¬ O.ProperStateReadoutCoverExtension I m := by
  intro h
  exact h.2

/--
A concrete readout realizes an abstract finite mediator profile when that
profile has exactly the same loss and separation behavior on state pairs.
-/
def StateReadoutRealizesMediatorProfile {n : Nat}
    (readout : X → Fin n)
    (M : (O.toAbstractIncidenceSystem).FiniteMediatorProfile n) : Prop :=
  (∀ p, M.Loss p ↔ O.StateReadoutLoss readout p) ∧
    ∀ p, M.Separates p ↔ O.StateReadoutSeparates readout p

/-- Admissibility predicate: the abstract finite profile is induced by a state readout. -/
def StateReadoutAdmissibleMediatorProfile {n : Nat}
    (M : (O.toAbstractIncidenceSystem).FiniteMediatorProfile n) : Prop :=
  ∃ readout : X → Fin n, O.StateReadoutRealizesMediatorProfile readout M

/-- The canonical admissibility predicate for abstract profiles realized by state readouts. -/
def StateReadoutAdmissible {n : Nat}
    (M : (O.toAbstractIncidenceSystem).FiniteMediatorProfile n) : Prop :=
  O.StateReadoutAdmissibleMediatorProfile M

/-- State-readout admissible mediated covers are admissible abstract finite cover extensions. -/
theorem admissibleFiniteCoverExtension_of_stateReadoutAdmissible_mediatedCover
    {n : Nat} (I : Coalition J)
    (M : (O.toAbstractIncidenceSystem).FiniteMediatorProfile n) :
    O.StateReadoutAdmissibleMediatorProfile M →
      (O.toAbstractIncidenceSystem).MediatedCover I M →
        (O.toAbstractIncidenceSystem).AdmissibleFiniteCoverExtension
          O.StateReadoutAdmissible I n := by
  intro hAdm hMed
  exact ⟨M, hAdm, hMed⟩

/--
State-readout admissible proper mediated covers are admissible abstract proper
finite cover extensions.
-/
theorem properAdmissibleFiniteCoverExtension_of_stateReadoutAdmissible_properMediatedCover
    {n : Nat} (I : Coalition J)
    (M : (O.toAbstractIncidenceSystem).FiniteMediatorProfile n) :
    O.StateReadoutAdmissibleMediatorProfile M →
      (O.toAbstractIncidenceSystem).ProperMediatedCover I M →
        (O.toAbstractIncidenceSystem).ProperAdmissibleFiniteCoverExtension
          O.StateReadoutAdmissible I n := by
  intro hAdm hProper
  exact ⟨M, hAdm, hProper⟩

/--
Residual-targeted descent for a concrete state readout: every residual distinction
separated by the readout is already separated by a subcoalition.
-/
def StateReadoutDescendsToOnResidual {n : Nat}
    (I K : Coalition J) (readout : X → Fin n) : Prop :=
  ∀ p, (O.toAbstractIncidenceSystem).Residual I p →
    O.StateReadoutSeparates readout p →
      ∃ j, K j ∧ O.SeparatesPair j p

/-- Concrete readout non-descent over residuals of `I`. -/
def NonDescentStateReadoutOnResidual {n : Nat}
    (I : Coalition J) (readout : X → Fin n) : Prop :=
  ∀ K, Coalition.Proper K I → ¬ O.StateReadoutDescendsToOnResidual I K readout

/-- Proper concrete mediated cover with residual-targeted non-descent. -/
def ProperIrreducibleStateReadoutMediatedCover {n : Nat}
    (I : Coalition J) (readout : X → Fin n) : Prop :=
  O.ProperStateReadoutMediatedCover I readout ∧
    O.NonDescentStateReadoutOnResidual I readout

/-- Proper irreducible concrete readout covers are proper concrete mediated covers. -/
theorem properStateReadoutMediatedCover_of_properIrreducibleStateReadoutMediatedCover
    {n : Nat} (I : Coalition J) (readout : X → Fin n) :
    O.ProperIrreducibleStateReadoutMediatedCover I readout →
      O.ProperStateReadoutMediatedCover I readout := by
  intro h
  exact h.1

/-- Proper irreducible concrete readout covers have residual-targeted non-descent. -/
theorem nonDescentStateReadoutOnResidual_of_properIrreducibleStateReadoutMediatedCover
    {n : Nat} (I : Coalition J) (readout : X → Fin n) :
    O.ProperIrreducibleStateReadoutMediatedCover I readout →
      O.NonDescentStateReadoutOnResidual I readout := by
  intro h
  exact h.2

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
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.extendWithMediator
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.MediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.ProperMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.mediatedCover_iff_base_or_mediator
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.mediator_separates_residual_of_mediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.MinimalMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.ProperMinimalMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.AdmissibleFiniteCoverExtension
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.ProperAdmissibleFiniteCoverExtension
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.MinimalAdmissibleMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.ProperMinimalAdmissibleMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.no_smaller_finiteCoverExtension_of_minimalMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.no_smaller_properFiniteCoverExtension_of_properMinimalMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.no_smaller_admissibleFiniteCoverExtension_of_minimalAdmissibleMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.no_smaller_properAdmissibleFiniteCoverExtension_of_properMinimalAdmissibleMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.IrreducibleMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.ProperIrreducibleMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.nonDescent_of_irreducibleMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.AbstractIncidenceSystem.nonDescentOnResidual_of_properIrreducibleMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.toAbstractIncidenceSystem
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.realizes_toAbstractIncidenceSystem
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.extendWithStateReadout
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.StateReadoutMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.stateReadoutMediatedCover_iff_base_or_readout
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.ProperStateReadoutMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.MinimalStateReadoutMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.ProperMinimalStateReadoutMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.stateReadout_separates_residual_of_mediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.no_smaller_stateReadoutCoverExtension_of_minimalStateReadoutMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.no_smaller_properStateReadoutCoverExtension_of_properMinimalStateReadoutMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.StateReadoutRealizesMediatorProfile
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.StateReadoutAdmissibleMediatorProfile
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.StateReadoutAdmissible
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.admissibleFiniteCoverExtension_of_stateReadoutAdmissible_mediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.properAdmissibleFiniteCoverExtension_of_stateReadoutAdmissible_properMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.StateReadoutDescendsToOnResidual
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.ProperIrreducibleStateReadoutMediatedCover
#print axioms PrimitiveHolonomy.Standalone.MultiInterfaceGeometry.ObservationSystem.nonDescentStateReadoutOnResidual_of_properIrreducibleStateReadoutMediatedCover
/- AXIOM_AUDIT_END -/
