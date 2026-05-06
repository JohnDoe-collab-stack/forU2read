# Plan de modularisation Lean — algèbre multi-interface

Statut : plan de travail. Aucun fichier Lean n’est modifié par ce document.

But : transformer `COFRS/MultiInterface.lean` en noyau stable, puis répartir l’algèbre multi-interface
dans des modules spécialisés, sans perdre la contrainte centrale du projet :

```text
constructif
+ sans axiome
+ sans Classical
+ sans propext
+ sans Quot.sound
```

## 1. Décision architecturale

Réponse nette :

```text
ne pas écrire toute l’algèbre dans un seul fichier Lean.
```

`COFRS/MultiInterface.lean` doit rester le socle constructif audité. L’algèbre complète doit être
décomposée en couches, chacune avec un rôle précis.

Pourquoi :

- un fichier unique devient difficile à auditer ;
- les preuves constructives deviennent plus fragiles quand tout est mélangé ;
- les dépendances entre calcul fini, incidence, médiation et dynamique doivent rester visibles ;
- les futurs exemples ne doivent pas polluer le noyau abstrait ;
- la généralisation hétérogène doit arriver après stabilisation de la version homogène.

## 2. Principe directeur

La structure mathématique doit rester :

```text
distinctions requises
→ pertes d’interface
→ incidence des pertes
→ résidu commun
→ fermeture
→ irréductibilité
→ médiation minimale
→ non-descente
```

Le découpage Lean doit suivre exactement cette chaîne.

Le noyau actuel contient déjà trop de rôles à la fois :

- listes finies ;
- booléens calculables ;
- residual propositionnel ;
- `rho` numérique ;
- gain local ;
- essentialité / redondance ;
- profil dynamique ;
- non-descente du médiateur.

Ce n’est pas faux, mais ce n’est pas le bon format final.

## 3. Arborescence cible

Arborescence recommandée :

```text
COFRS/MultiInterface.lean
COFRS/MultiInterface/Core.lean
COFRS/MultiInterface/Finite.lean
COFRS/MultiInterface/Incidence.lean
COFRS/MultiInterface/Closure.lean
COFRS/MultiInterface/Mediation.lean
COFRS/MultiInterface/Dynamics.lean
COFRS/MultiInterface/Examples.lean
```

Rôle de chaque fichier :

```text
Core.lean
  définitions propositionnelles minimales :
  Subfamily, Subset, Proper, Insert, Remove,
  JointSame, RequiredDistinction, Loss, Residual, ResidualEmpty, Closed.

Finite.lean
  listes explicites, InList, AllFalse, countListBool,
  pairLists, ResidualListBool, rho,
  ponts entre rho calculable et ResidualEmpty.

Incidence.lean
  LossBool, InterfaceSeparatesBool,
  lossIncidence, separationIncidence,
  SameLossProfileOn, LossProfileSeparated,
  local usefulness, local redundancy, deltaGain.

Closure.lean
  residual_mono, rho_mono,
  closed_iff_residual_empty,
  EssentialInClosure, RedundantInClosure,
  IrreducibleClosure, IrreducibleClosureW,
  IrreducibleClosureRho.

Mediation.lean
  MediatorDescendsSubfamily,
  IrreducibleMediator,
  minimal finite mediator schemas,
  non-descente vers sous-familles strictes.

Dynamics.lean
  SubfamilyPredictsStep,
  DynamicMediatorDescendsSubfamily,
  FamilyIrreducibleMediationProfile,
  endToEnd_minimalAccessCoalition.

Examples.lean
  exemples finis séparés :
  XOR direct,
  XOR médié,
  petits témoins multi-interface.
```

Le fichier `COFRS/MultiInterface.lean` devient alors un fichier façade :

```lean
import COFRS.MultiInterface.Core
import COFRS.MultiInterface.Finite
import COFRS.MultiInterface.Incidence
import COFRS.MultiInterface.Closure
import COFRS.MultiInterface.Mediation
import COFRS.MultiInterface.Dynamics
```

Il ne doit contenir presque aucune preuve.

## 4. Ordre de migration

La migration doit être progressive. Ne pas tout déplacer d’un coup.

### Phase 1 — stabiliser le noyau

Créer :

```text
COFRS/MultiInterface/Core.lean
```

Y déplacer uniquement :

```text
Subfamily
Subset
Proper
Insert
Remove
JointSame
RequiredDistinction
Loss
InterfaceSeparates
Residual
ResidualEmpty
ResidualNonempty
Closed
residual_mono
closed_iff_residual_empty
```

Critère de succès :

```text
lake env lean COFRS/MultiInterface/Core.lean
```

et audit propre.

### Phase 2 — isoler le calcul fini

Créer :

```text
COFRS/MultiInterface/Finite.lean
```

Y déplacer :

```text
sumList
countListD
countList
AllFalse
InList
countListBool
AllFalseBool
pairWith
pairLists
JointSameList
ResidualList
JointSameListBool
ResidualListBool
rho
rho_eq_zero_iff_residualEmpty_of_exhaustive_states
rho_pos_iff_residualNonempty_of_exhaustive_states
rho_mono_of_subfamily_subset
```

Critère de succès :

```text
rho = projection calculable du residual propositionnel
```

sans quotient et sans `Fintype` global.

### Phase 3 — extraire l’incidence

Créer :

```text
COFRS/MultiInterface/Incidence.lean
```

Y déplacer :

```text
LossBool
InterfaceSeparatesBool
lossIncidence
separationIncidence
LocallyUsefulInterface
LocallyRedundantInterface
SameLossProfileOn
LossProfileSeparated
deltaGain
locallyUsefulInterface_iff_rho_insert_lt_of_exhaustive_states
```

Objectif :

```text
montrer que l’information pertinente est l’incidence des pertes,
et que rho n’en est qu’une projection numérique.
```

### Phase 4 — extraire fermeture et irréductibilité

Créer :

```text
COFRS/MultiInterface/Closure.lean
```

Y déplacer :

```text
EssentialInClosure
RedundantInClosure
essentialInClosure_iff_closed_and_remove_residual
redundantInClosure_iff_closed_and_remove_residual_empty
essentialInClosure_iff_closed_and_rho_remove_pos_of_exhaustive_states
redundantInClosure_iff_closed_and_rho_remove_zero_of_exhaustive_states
IrreducibleClosure
IrreducibleClosureW
IrreducibleClosureRho
irreducibleClosureW_iff_residual_empty_and_proper_residual_nonempty
irreducibleClosure_of_irreducibleClosureW
irreducibleClosureW_iff_irreducibleClosureRho_of_exhaustive_states
```

Objectif :

```text
fermeture = residual vide
irréductibilité = residual vide + residual non vide pour toute sous-famille stricte
```

### Phase 5 — isoler médiation et dynamique

Créer :

```text
COFRS/MultiInterface/Mediation.lean
COFRS/MultiInterface/Dynamics.lean
```

Dans `Mediation.lean` :

```text
MediatorDescendsSubfamily
IrreducibleMediator
```

Dans `Dynamics.lean` :

```text
SubfamilyPredictsStep
DynamicMediatorDescendsSubfamily
subfamilyPredictsStep_of_dynamicMediatorDescendsSubfamily
not_dynamicMediatorDescendsSubfamily_of_not_subfamilyPredictsStep
FamilyIrreducibleMediationProfile
refiningLift_of_familyIrreducibleMediationProfile
no_smaller_refiningLift_of_familyIrreducibleMediationProfile
not_dynamicMediatorDescendsSubfamily_of_familyIrreducibleMediationProfile
endToEnd_minimalAccessCoalition
```

Objectif :

```text
connecter l’algèbre finie des pertes à la non-descente dynamique,
sans mélanger les preuves de listes avec les théorèmes de compatibilité.
```

## 5. Règles d’audit

Chaque fichier Lean nouveau doit finir par un unique bloc :

```lean
/- AXIOM_AUDIT_BEGIN -/
#print axioms ...
/- AXIOM_AUDIT_END -/
```

Les audits doivent rester courts. Chaque fichier doit auditer ses déclarations principales, pas toute
la bibliothèque.

Interdits absolus :

```text
Classical
Classical.*
open Classical
propext
Quot.sound
axiom
```

Si un déplacement introduit une dépendance interdite, il faut reculer et garder le lemme dans une forme
plus faible mais constructive.

## 6. Ce qu’il ne faut pas faire

Ne pas commencer par :

```text
interfaces hétérogènes complètes
produits quotients
cardinalités de quotients
ensembles extensionalisés
preuves par extensionalité propositionnelle
```

Pourquoi :

```text
ces objets attirent immédiatement Classical/propext/Quot.sound.
```

La bonne discipline est :

```text
relations propositionnelles
+ listes explicites
+ booléens calculables
+ témoins constructifs
```

## 7. Version hétérogène : plus tard

La version actuelle est homogène :

```lean
obs : J → S → V
```

La version finale hétérogène sera :

```lean
obs : ∀ j : J, S → V j
Joint_I : S → (∀ j, I j → V j)
```

Mais elle ne doit venir qu’après stabilisation de :

```text
Core
Finite
Incidence
Closure
Mediation
Dynamics
```

Objectif de cette phase future :

```text
changer le type des observations sans changer l’algèbre des preuves.
```

## 8. Résultat attendu

À la fin, l’architecture doit permettre de dire :

```text
le noyau abstrait est dans Core ;
le calcul explicite de rho est dans Finite ;
l’objet structurel d’incidence est dans Incidence ;
la fermeture minimale est dans Closure ;
la médiation et la non-descente sont dans Mediation/Dynamics ;
les exemples sont séparés.
```

Ce découpage rendra le résultat plus publiable, plus auditable et plus extensible.

Formule finale :

```text
un seul noyau,
plusieurs couches,
zéro axiome.
```
