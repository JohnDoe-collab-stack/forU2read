import COFRS.Examples.ReferentialInduction

namespace PrimitiveHolonomy
namespace Examples

/-!
# Disciplined chains: cycle terminality + step relation (constructive)

This file provides the project-level one-step relation `Leadsto` together with a compact notion
of terminality by `Closes ∨ Cycle`.

Per request, all material about global termination via ranks or well-foundedness is commented out
in this file. Nothing here relies on `Classical`, `propext`, `Quot.sound`, or axioms.
-/

open PrimitiveHolonomy.Relation

namespace DisciplinedChainsGlobal

/-- Compose two reflexive-transitive chains. -/
theorem rt_append {α : Type _} {r : α → α → Prop} {a b c : α} :
    ReflTransGen r a b → ReflTransGen r b c → ReflTransGen r a c := by
  intro hab hbc
  induction hbc with
  | refl =>
      exact hab
  | tail hbc' hstep ih =>
      exact ReflTransGen.tail ih hstep

end DisciplinedChainsGlobal

/-!
## Commented out: global termination via rank or well-foundedness

Per request, the generic termination theorems and their assumptions are disabled here.
They can be restored from git history if needed.
-/

/- section Generic

universe u
variable {α : Type u}

abbrev NextOrClose (Active : α → Prop) (Closes : α → Prop) (step : α → α → Prop) : Prop :=
  ∀ a : α, Active a → Closes a ∨ ∃ b : α, Active b ∧ step a b

theorem terminates_of_rankNat
    (Active : α → Prop) (Closes : α → Prop) (step : α → α → Prop)
    (rank : α → Nat)
    (nextOrClose : NextOrClose Active Closes step)
    (rank_decreases : ∀ {a b : α}, step a b → rank b < rank a) :
    ∀ a : α, Active a → ∃ b : α, (ReflTransGen step a b) ∧ (Closes b) := by
  ...

theorem terminates_of_wellFounded
    (Active : α → Prop) (Closes : α → Prop) (step : α → α → Prop)
    (nextOrClose : NextOrClose Active Closes step)
    (wfSucc : WellFounded (fun b a : α => step a b)) :
    ∀ a : α, Active a → ∃ b : α, (ReflTransGen step a b) ∧ (Closes b) := by
  ...

theorem terminates_of_rankFin
    (Active : α → Prop) (Closes : α → Prop) (step : α → α → Prop)
    {n : Nat} (rankFin : α → Fin n)
    (nextOrClose : NextOrClose Active Closes step)
    (rankFin_decreases : ∀ {a b : α}, step a b → (rankFin b).val < (rankFin a).val) :
    ∀ a : α, Active a → ∃ b : α, (ReflTransGen step a b) ∧ (Closes b) := by
  ...

end Generic -/

/-!
## Integration helper for `ReferentialProblem`

The three generic termination lemmas above work for an arbitrary type `α`.
This section instantiates them with the project’s notion of “disciplined stage transition with repair”
from `COFRS/Examples/ReferentialInduction.lean`.

This is still parametric: you provide `Active`, and whichever global termination hypothesis you want.
-/

section Referential

open DisciplinedChainsGlobal

/-- One-step relation induced by a disciplined transition together with its forced next repair. -/
def Leadsto (R R' : ReferentialProblem) : Prop :=
  ∃ K : DisciplinedStageTransitionWithRepair,
    K.J.toStageTransition.I.R = R ∧ K.Rnext' = R'

/-!
### Optional terminal notion: `Closes ∨ Cycle`

If your framework treats “cycle” (e.g. periodic audit) as an acceptable terminal closure,
you can use `Terminal R := R.Closes ∨ Cycle R` as the `Closes` predicate in the generic lemmas.

This file only defines the terminal predicate; it does not provide global termination theorems.
-/

abbrev Terminal (Cycle : ReferentialProblem → Prop) (R : ReferentialProblem) : Prop :=
  R.Closes ∨ Cycle R

/-!
The global termination wrappers for `Leadsto` are commented out per request.
-/

/- theorem terminates_referential_of_rankNat
    (Active : ReferentialProblem → Prop)
    (rank : ReferentialProblem → Nat)
    (nextOrClose : NextOrClose Active ReferentialProblem.Closes Leadsto)
    (rank_decreases : ∀ {R R' : ReferentialProblem}, Leadsto R R' → rank R' < rank R) :
    ∀ R0 : ReferentialProblem, Active R0 →
      ∃ RT : ReferentialProblem, (ReflTransGen Leadsto R0 RT) ∧ RT.Closes := by
  ...

theorem terminates_referential_of_wellFounded
    (Active : ReferentialProblem → Prop)
    (nextOrClose : NextOrClose Active ReferentialProblem.Closes Leadsto)
    (wfSucc : WellFounded (fun R' R : ReferentialProblem => Leadsto R R')) :
    ∀ R0 : ReferentialProblem, Active R0 →
      ∃ RT : ReferentialProblem, (ReflTransGen Leadsto R0 RT) ∧ RT.Closes := by
  ...

theorem terminates_referential_of_rankFin
    (Active : ReferentialProblem → Prop)
    {n : Nat} (rankFin : ReferentialProblem → Fin n)
    (nextOrClose : NextOrClose Active ReferentialProblem.Closes Leadsto)
    (rankFin_decreases :
      ∀ {R R' : ReferentialProblem}, Leadsto R R' → (rankFin R').val < (rankFin R).val) :
    ∀ R0 : ReferentialProblem, Active R0 →
      ∃ RT : ReferentialProblem, (ReflTransGen Leadsto R0 RT) ∧ RT.Closes := by
  ...

theorem terminates_referential_of_rankNat_terminal
    (Active : ReferentialProblem → Prop)
    (Cycle : ReferentialProblem → Prop)
    (rank : ReferentialProblem → Nat)
    (nextOrTerminal : NextOrClose Active (Terminal Cycle) Leadsto)
    (rank_decreases : ∀ {R R' : ReferentialProblem}, Leadsto R R' → rank R' < rank R) :
    ∀ R0 : ReferentialProblem, Active R0 →
      ∃ RT : ReferentialProblem, (ReflTransGen Leadsto R0 RT) ∧ Terminal Cycle RT := by
  ...

theorem terminates_referential_of_wellFounded_terminal
    (Active : ReferentialProblem → Prop)
    (Cycle : ReferentialProblem → Prop)
    (nextOrTerminal : NextOrClose Active (Terminal Cycle) Leadsto)
    (wfSucc : WellFounded (fun R' R : ReferentialProblem => Leadsto R R')) :
    ∀ R0 : ReferentialProblem, Active R0 →
      ∃ RT : ReferentialProblem, (ReflTransGen Leadsto R0 RT) ∧ Terminal Cycle RT := by
  ...

theorem terminates_referential_of_rankFin_terminal
    (Active : ReferentialProblem → Prop)
    (Cycle : ReferentialProblem → Prop)
    {n : Nat} (rankFin : ReferentialProblem → Fin n)
    (nextOrTerminal : NextOrClose Active (Terminal Cycle) Leadsto)
    (rankFin_decreases :
      ∀ {R R' : ReferentialProblem}, Leadsto R R' → (rankFin R').val < (rankFin R).val) :
    ∀ R0 : ReferentialProblem, Active R0 →
      ∃ RT : ReferentialProblem, (ReflTransGen Leadsto R0 RT) ∧ Terminal Cycle RT := by
  ... -/

end Referential

/- AXIOM_AUDIT_BEGIN -/
#print axioms PrimitiveHolonomy.Examples.DisciplinedChainsGlobal.rt_append
#print axioms PrimitiveHolonomy.Examples.Leadsto
#print axioms PrimitiveHolonomy.Examples.Terminal
/- AXIOM_AUDIT_END -/

end Examples
end PrimitiveHolonomy
