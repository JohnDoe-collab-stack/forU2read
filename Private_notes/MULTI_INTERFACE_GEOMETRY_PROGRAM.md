# Programme géométrique multi-interface

Statut : plan de formalisation. Aucun résultat Lean nouveau n’est affirmé ici.

But : passer de l’algèbre autonome déjà formalisée à une géométrie complète des fermetures par
interfaces.

Point de départ :

```text
algèbre = distinctions, pertes, incidence, résidu, fermeture, irréductibilité, médiation
géométrie = morphismes, restrictions, préfaisceaux, couvertures, recollement, invariance
```

Formule centrale :

```text
la cardinalité est une décatégorification de l’incidence ;
la fermeture est une condition de couverture ;
la géométrie commence quand les résidus se transportent fonctoriellement.
```

## 1. Ce que nous avons déjà

Le fichier autonome :

```text
Standalone/MultiInterfaceSelfContained.lean
```

donne déjà le noyau algébrique :

```text
J                      famille d’interfaces
I ⊆ J                  coalition / sous-famille
R_σ                    distinctions requises par la cible
L_j                    distinctions perdues par l’interface j
Res(I)                 résidu commun de la coalition I
ρ(I)                   cardinal du résidu
Closed(I,σ)            fermeture de la cible par I
IrreducibleClosed(I)   fermeture minimale
Mediator               supplément fini
NonDescent             médiateur non réductible aux sous-familles strictes
```

Donc le niveau actuel est :

```text
algèbre des coalitions minimales d’accès.
```

Ce n’est pas encore une géométrie complète parce qu’il manque :

```text
morphismes
fonctorialité
restriction
couvertures
recollement
invariance par changement de présentation
```

## 2. Objet géométrique de base

Il y a deux niveaux à séparer.

### 2.1 Système observationnel concret

Une instance observationnelle de fermeture est un système :

```text
𝓢 = (X, σ, J, obs)
```

avec :

```text
X       espace fini d’états
σ       cible / vérité / signature
J       espace fini d’interfaces
obs_j   observation de l’interface j
```

À partir de ce système, l’algèbre construit :

```text
R_σ
L_j
IncLoss_σ / IncSep_σ
Res_σ(I)
ρ_σ(I)
Closed_σ(I)
```

### 2.2 Système abstrait d’incidence

Mais la géométrie ne doit pas dépendre immédiatement de la forme concrète des observations. Le bon objet
intermédiaire est :

```text
AbstractIncidenceSystem
```

avec :

```text
D                 type / domaine des distinctions
J                 type des interfaces
Required(d)       la distinction d est requise par la cible
Loss(j,d)         l’interface j perd la distinction d
Separates(j,d)    l’interface j sépare la distinction d
```

et une loi de cohérence locale :

```text
Separates(j,d)  ↔  Required(d) ∧ ¬ Loss(j,d)
```

Dans une version strictement constructive, cette loi peut être remplacée par deux implications et une
donnée booléenne décidable :

```text
LossBool(j,d) : Bool
SeparatesBool(j,d) : Bool
```

afin d’éviter de transformer inutilement des négations propositionnelles en témoins existentiels.

Le système observationnel concret réalise alors le système abstrait :

```text
D = X × X
Required(x,y)  := σ(x) ≠ σ(y)
Loss(j,x,y)    := obs_j(x) = obs_j(y) ∧ σ(x) ≠ σ(y)
Separates(j,x,y) := σ(x) ≠ σ(y) ∧ obs_j(x) ≠ obs_j(y)
```

Cette séparation est essentielle :

```text
géométrie abstraite d’abord ;
réalisation observationnelle ensuite.
```

Elle évite de faire dépendre les morphismes, les couvertures et les médiateurs de détails de typage
comme `obs : J → X → V` ou `obs : ∀ j, X → V j`.

La géométrie doit étudier deux niveaux distincts :

```text
géométrie interne  : coalitions, résidus, couvertures dans un système fixé ;
géométrie externe  : transport de ces objets entre systèmes compatibles.
```

Le premier niveau donne une géométrie des ouverts informationnels. Le second donne les morphismes et les
invariants.

## 3. Poset des coalitions

Les coalitions forment un poset :

```text
Coal(J) := 𝒫(J)
```

avec ordre :

```text
I ≤ K  ⇔  I ⊆ K.
```

Interprétation :

```text
K possède au moins autant d’accès que I.
```

Théorème algébrique déjà présent :

```text
I ⊆ K → Res(K) ⊆ Res(I)
```

Lecture géométrique :

```text
Res est contravariant sur Coal(J).
```

Donc la première géométrisation est :

```text
Res_σ : Coal(J)ᵒᵖ → Subsets(R_σ)
```

avec :

```text
I ↦ Res_σ(I)
```

et pour `I ⊆ K` :

```text
Res_σ(K) ↪ Res_σ(I).
```

## 4. Résidu comme préfaisceau

Le vrai objet géométrique n’est pas seulement :

```text
ρ(I)
```

mais le préfaisceau :

```text
Res_σ : Coal(J)ᵒᵖ → Set
```

où :

```text
Res_σ(I) = distinctions encore perdues par toutes les interfaces de I.
```

La restriction le long de `I ⊆ K` est l’inclusion :

```text
res_{K,I} : Res_σ(K) → Res_σ(I)
```

parce que toute distinction encore perdue par `K` était déjà perdue par `I`.

La cardinalisation :

```text
ρ(I) = #Res_σ(I)
```

est alors une décatégorification :

```text
Res_σ(I)  ↦  #Res_σ(I).
```

Formule :

```text
ρ = # ∘ Res.
```

## 5. Incidence abstraite comme objet premier

Pour éviter toute ambiguïté, il faut distinguer deux incidences duales.

Incidence de perte :

```text
IncLoss_σ : R_σ → 𝒫(J)
IncLoss_σ(d) := { j ∈ J | d ∈ L_j }.
```

Elle dit, pour chaque distinction requise, quelles interfaces la perdent.

Incidence de séparation :

```text
IncSep_σ : R_σ → 𝒫(J)
IncSep_σ(d) := { j ∈ J | d ∉ L_j }.
```

Elle dit, pour chaque distinction requise, quelles interfaces la séparent.

Les deux sont complémentaires sur `J` :

```text
j ∈ IncSep_σ(d)  ⇔  j ∉ IncLoss_σ(d).
```

La version Lean constructive ne doit pas utiliser cette complémentarité comme égalité extensionnelle de
sets. Elle doit la garder comme équivalence pointwise ou comme fonction booléenne décidable.

Dans le système abstrait, on ne part pas de `obs`. On part directement de :

```text
Required : D → Prop
Loss     : J → D → Prop
Separates: J → D → Prop
```

Les observations concrètes deviennent seulement une réalisation particulière de ces trois relations.

Cette abstraction est décisive pour les médiateurs : un médiateur `M : X → Fin n` n’a pas nécessairement
le même type de sortie qu’une interface ordinaire. Mais dans la géométrie abstraite, il suffit de savoir
quelles distinctions il perd ou sépare.

Donc la bonne généralisation est :

```text
interfaces = objets porteurs d’un profil Loss/Separates sur D
```

et non :

```text
interfaces = observations homogènes obligatoirement du même type V.
```

Le résidu se récupère par :

```text
d ∈ Res(I)
⇔
∀ j ∈ I, j ∈ IncLoss_σ(d).
```

Donc :

```text
Res(I) = { d ∈ R_σ | I ⊆ IncLoss_σ(d) }.
```

Cette formule est fondamentale : elle montre que `Res` est dérivé de `IncLoss`.

La fermeture se lit plus proprement par l’incidence de séparation :

```text
Closed(I,σ)
⇔
∀ d ∈ R_σ, ∃ j ∈ I, j ∈ IncSep_σ(d).
```

Autrement dit : toute distinction requise est séparée par au moins une interface de la coalition.

Lecture géométrique :

```text
IncLoss_σ / IncSep_σ
```

sont deux correspondances entre :

```text
distinctions requises ↔ interfaces.
```

La géométrie doit donc garder l’incidence comme objet structurel, puis seulement ensuite prendre :

```text
Res
ρ
Closed
```

comme invariants dérivés.

## 6. Fermeture comme couverture

Une coalition ferme lorsque :

```text
Res(I) = ∅.
```

Avec la formule d’incidence :

```text
Res(I) = { d | I ⊆ IncLoss(d) }.
```

Donc :

```text
Closed(I,σ)
⇔
∀ d ∈ R_σ, ¬ (I ⊆ IncLoss_σ(d)).
```

Attention constructive importante :

```text
¬ (∀ j ∈ I, j perd d)
```

ne doit pas être remplacé silencieusement par :

```text
∃ j ∈ I, j sépare d
```

sans hypothèse finie/décidable explicite. Dans le régime fini du projet, cette conversion est légitime
par énumération constructive de `I`, mais elle doit être prouvée comme lemme séparé.

La bonne définition géométrique de couverture est donc directement witness-style :

```text
CoveringCoalition(I,σ) :=
  ∀ d, RequiredDistinction_σ(d) →
    ∃ j, j ∈ I ∧ InterfaceSeparates(j,d).
```

Puis on prouve, en régime fini/décidable :

```text
Closed(I,σ) ↔ CoveringCoalition(I,σ).
```

Cela évite de faire dépendre la formalisation d’une égalité extensionnelle d’ensembles ou d’un passage
non constructif de `¬∀` à `∃¬`.

En notation mathématique compacte, cela correspond à :

```text
I couvre R_σ par les accessibilités Acc_j.
```

où :

```text
Acc_j := R_σ \ L_j.
```

Donc :

```text
Closed(I,σ)
⇔
R_σ = ⋃_{j∈I} Acc_j.
```

Mais dans Lean, cette égalité doit être remplacée par deux inclusions pointwise, ou par la forme
witness-style ci-dessus.

Formule géométrique :

```text
fermeture = couverture du site des distinctions requises.
```

## 7. Topologie de fermeture

On peut définir une structure de couverture sur les distinctions requises.

Une famille d’interfaces `I` est couvrante si :

```text
∀ d ∈ R_σ, ∃ j ∈ I, d ∈ Acc_j.
```

Les axiomes attendus :

1. **Monotonie des couvertures**

```text
I couvre et I ⊆ K  →  K couvre.
```

2. **Stabilité par remplacement plus informatif**

Si chaque interface `j` d’une couverture est remplacée par une coalition `K_j` telle que toute
distinction séparée par `j` est séparée par au moins une interface de `K_j`, alors l’union des `K_j`
couvre encore.

3. **Base de couvertures minimales**

Les fermetures irréductibles sont les couvertures minimales :

```text
IrreducibleClosed(I)
⇔
I couvre R_σ
et
∀ K ⊂ I, K ne couvre pas R_σ.
```

Ce n’est pas encore une topologie de Grothendieck complète. Pour obtenir une vraie topologie de
Grothendieck, il faudra préciser :

```text
objets du site,
flèches de restriction,
pullbacks / changements de base,
stabilité des couvertures par pullback,
transitivité des couvertures.
```

Le statut rigoureux actuel est donc :

```text
pré-topologie finie de fermeture
```

ou :

```text
coverage finie sur les coalitions.
```

La graine correcte reste :

```text
coalitions couvrantes = familles qui ferment la cible.
```

## 8. Recollement

Le recollement doit répondre à la question :

```text
si des coalitions ferment localement des sous-domaines de distinctions,
quand leur union ferme-t-elle globalement ?
```

Soit une décomposition finie :

```text
R_σ = D₁ ∪ ... ∪ Dₙ.
```

Supposons :

```text
I₁ couvre D₁
...
Iₙ couvre Dₙ.
```

Alors :

```text
I₁ ∪ ... ∪ Iₙ couvre R_σ.
```

Version résiduelle locale :

```text
Res_D(I) := D ∩ Res(I)
```

Alors le recollement s’écrit :

```text
Res_{D₁}(I₁)=∅
...
Res_{Dₙ}(Iₙ)=∅
→
Res_{R_σ}(I₁∪...∪Iₙ)=∅.
```

Ce théorème serait le premier vrai théorème de recollement.

Preuve attendue :

```text
prendre d ∈ R_σ ;
choisir t tel que d ∈ D_t ;
utiliser Res_{D_t}(I_t)=∅ pour obtenir une interface de I_t qui sépare d ;
conclure que cette interface appartient à I₁∪...∪Iₙ.
```

En Lean, il faut éviter l’égalité d’union générale comme primitive. La version constructive doit utiliser
une énumération des domaines `D_t` et un témoin :

```text
∀ d, Required(d) → ∃ t, d ∈ D_t.
```

## 9. Morphismes de systèmes d’incidence

Pour avoir une géométrie, il faut dire quand deux systèmes sont reliés.

La première couche doit porter sur les systèmes abstraits d’incidence, pas sur les systèmes
observationnels complets.

Un système abstrait est :

```text
𝓘 = (D, J, Required, Loss, Separates).
```

Un morphisme simple :

```text
𝓘 → 𝓘'
```

devrait comporter :

```text
f_D : D → D'
f_J : J → J'
```

avec préservation des relations :

```text
Required(d) → Required'(f_D d)
Loss(j,d) → Loss'(f_J j, f_D d)
Separates(j,d) → Separates'(f_J j, f_D d)
```

Un isomorphisme d’incidence demande des bijections explicites :

```text
e_D : D ≃ D'
e_J : J ≃ J'
```

et des équivalences pointwise :

```text
Required(d) ↔ Required'(e_D d)
Loss(j,d) ↔ Loss'(e_J j, e_D d)
Separates(j,d) ↔ Separates'(e_J j, e_D d)
```

C’est cette couche qui doit porter les premiers théorèmes d’invariance :

```text
IncidenceIso
→ preserves Res
→ preserves CoveringCoalition
→ preserves MinimalCoveringCoalition
→ preserves ρ
```

Ensuite seulement, on relie les systèmes observationnels aux systèmes d’incidence abstraits.

Un morphisme entre systèmes :

```text
𝓢 = (X, σ, J, obs)
𝓢' = (X', σ', J', obs')
```

On fixe d’abord une convention simple pour la version homogène :

```text
f_X : X' → X
f_J : J → J'
```

avec les mêmes types de valeurs, ou des cartes de valeurs explicites si les observations sont typées
différemment.

La direction choisie signifie :

```text
un état de 𝓢' se projette vers un état de 𝓢 ;
une interface de 𝓢 est réalisée par une interface de 𝓢'.
```

Conditions de compatibilité strictes :

```text
σ'(x') = σ(f_X x')
```

et, pour chaque `j : J` :

```text
obs'_{f_J(j)}(x') = obs_j(f_X x').
```

Alors les distinctions et pertes se tirent en arrière :

```text
si σ(f_X x') ≠ σ(f_X y'),
alors σ'(x') ≠ σ'(y')
```

et :

```text
si obs_j(f_X x') = obs_j(f_X y'),
alors obs'_{f_J(j)}(x') = obs'_{f_J(j)}(y').
```

Avec les égalités strictes ci-dessus, ces implications sont immédiates par réécriture constructive.

Pour les isomorphismes, on demande des bijections explicites :

```text
e_X : X ≃ X'
e_J : J ≃ J'
```

avec commutation de `σ` et des observations. Alors l’incidence est transportée sans perte.

Le fichier Lean doit donc commencer par :

```text
AbstractIncidenceSystem
IncidenceIso
```

et non par les morphismes observationnels généraux. C’est le chemin le plus sûr pour prouver l’invariance
sans importer de machinery lourde.

## 10. Invariance

Une fois les morphismes définis, il faut prouver que les constructions sont invariantes ou monotones.

Théorèmes à viser :

```text
morphisme qui préserve les pertes
→ transport de Res
```

```text
morphisme qui reflète les pertes
→ reflet de Closed
```

```text
isomorphisme de systèmes d’incidence
→ préservation exacte de Res, ρ, Closed, IrreducibleClosed
```

Théorème central pour les isomorphismes :

```text
IncLoss_σ ≅ IncLoss_σ'
→
∀ I, ρ_σ(I) = ρ_σ'(I')
et
Closed_σ(I) ↔ Closed_σ'(I').
```

Cela transforme `ρ` et `Closed` en invariants géométriques.

La version la plus constructive ne doit pas affirmer d’abord une égalité globale d’incidences. Elle doit
fournir des équivalences pointwise :

```text
Required(d) ↔ Required'(e_D d)
Loss(j,d) ↔ Loss'(e_J j, e_D d)
Residual(I,d) ↔ Residual'(e_J[I], e_D d)
Covering(I) ↔ Covering'(e_J[I])
```

Puis seulement dériver :

```text
rho(I) = rho'(e_J[I])
```

par transport explicite des listes finies de distinctions.

## 11. Médiation géométrique

Dans l’algèbre actuelle, un médiateur est :

```text
M : X → Fin n.
```

Géométriquement, il ajoute une nouvelle interface finie. Il faut distinguer deux régimes :

```text
fermeture directe :        Closed(I,σ)
fermeture médiée :         ¬ Closed(I,σ) mais ∃ M : X → Fin n, Closed(I ∪ {M},σ)
```

Donc la famille médiée est :

```text
I_M := I ∪ {M}.
```

La médiation ferme lorsque :

```text
Closed(I_M,σ).
```

La minimalité dit, pour une classe autorisée de médiateurs :

```text
n minimal tel qu’il existe M : X → Fin n avec Closed(I_M,σ).
```

La classe autorisée est indispensable. Sans elle, on peut tricher en laissant `M` encoder directement
`σ`. Pour rester aligné avec la théorie, `M` doit être :

```text
un supplément fini construit comme raffinement admissible de la fibre / dynamique ;
pas une oracle externe arbitraire de la vérité cible.
```

Dans la couche dynamique déjà formalisée, cette admissibilité est capturée par :

```text
RefiningLiftData
CompatDimEq
NonDescent
```

La non-descente dit :

```text
M ne factorise par aucune sous-famille stricte K ⊂ I.
```

Lecture géométrique :

```text
un médiateur est une extension finie du site d’interfaces
qui transforme une famille non couvrante en famille couvrante.
```

Donc :

```text
médiation = compactification finie du défaut de couverture.
```

Formulation précise :

```text
un médiateur minimal n’est pas une nouvelle mesure numérique ;
c’est une extension finie dont les fibres résolvent exactement le résidu commun,
avec une borne inférieure contre toute extension strictement plus petite.
```

## 12. Géométrie dynamique

La couche dynamique ajoute :

```text
Compatible
StepSeparatesFiber
RefiningLiftData
CompatDimEq
FamilyIrreducibleMediationProfile
```

La lecture géométrique :

```text
la vérité dynamique définit une cible σ_step sur une fibre ;
les interfaces définissent un site d’accès ;
le médiateur minimal est une extension finie qui couvre la vérité dynamique.
```

Le théorème `endToEnd_minimalAccessCoalition` devient :

```text
si le profil dynamique est irréductible,
alors :
1. un relèvement fini existe ;
2. aucun relèvement plus petit n’existe ;
3. le médiateur ne descend vers aucune sous-famille stricte.
```

Formulation géométrique :

```text
un profil dynamique irréductible produit une couverture médiée minimale
du site de compatibilité.
```

Traduction exacte :

```text
Compatible(..., step, x)
```

joue le rôle de vérité cible locale sur une fibre.

```text
SubfamilyPredictsStep(I, step)
```

joue le rôle de fermeture directe par la coalition `I`.

```text
DynamicMediatorDescendsSubfamily(K, L)
```

joue le rôle de descente géométrique du supplément vers une sous-coalition.

Le résultat dynamique ne dit donc pas seulement “un latent existe”. Il dit :

```text
un supplément fini ferme ;
aucun supplément plus petit ne suffit ;
ce supplément ne descend pas vers les sous-familles strictes interdites.
```

## 13. Objets Lean à formaliser

Nouveaux objets cibles :

```lean
AbstractIncidenceSystem
ObservationSystem
RealizesIncidenceSystem
CoalitionPoset
ResidualPresheaf
IncidenceMorphism
IncidenceIso
CoveringCoalition
MinimalCoveringCoalition
ResidualRestriction
ClosureCover
MediatedCover
FiniteCoverExtension
```

Théorèmes cibles :

```lean
observationSystem_realizes_incidenceSystem
residual_presheaf_mono
closed_iff_coveringCoalition
coveringCoalition_mono
coveringCoalition_of_local_covers
irreducibleClosed_iff_minimalCoveringCoalition
incidence_determines_residual
incidenceIso_preserves_rho
incidenceIso_preserves_closed
mediator_as_finite_cover_extension
irreducibleMediator_as_nonDescent_cover_extension
```

## 14. Ordre de formalisation

Ne pas commencer par les morphismes généraux. Le chemin robuste :

### Phase A — système abstrait d’incidence

Formaliser :

```text
AbstractIncidenceSystem
Required
Loss
Separates
Residual
CoveringCoalition
```

Objectif :

```text
faire toute la géométrie sans dépendre encore de obs : J → X → V.
```

### Phase B — réalisation observationnelle

Formaliser :

```text
ObservationSystem
RealizesIncidenceSystem
```

avec :

```text
D = X × X
Required(x,y) := σ(x) ≠ σ(y)
Loss(j,x,y) := Required(x,y) ∧ obs_j(x)=obs_j(y)
Separates(j,x,y) := Required(x,y) ∧ obs_j(x)≠obs_j(y)
```

Objectif :

```text
prouver que l’algèbre abstraite recouvre bien les systèmes concrets.
```

### Phase C — préfaisceau sur coalitions

Formaliser :

```text
Coalition order
Res(K) ⊆ Res(I) si I ⊆ K
ResidualRestriction
ResidualPresheaf
```

### Phase D — fermeture comme couverture

Formaliser :

```text
Acc_j
CoveringCoalition(I) := ∀ d, Required(d) → ∃ j ∈ I, Separates(j,d)
Closed(I,σ) ↔ CoveringCoalition(I)
```

Dans Lean constructif, éviter l’égalité d’ensembles si elle attire `propext`; utiliser une forme
pointwise :

```text
∀ d, Required(d) → ∃ j ∈ I, Separates(j,d)
```

### Phase E — incidence détermine residual

Formaliser :

```text
d ∈ Res(I) ↔ I ⊆ IncLoss(d)
```

Puis :

```text
CoveringCoalition(I) ↔ ∀ d, Required(d) → ∃ j ∈ I, j ∈ IncSep(d)
```

Le lien avec :

```text
¬ I ⊆ IncLoss(d)
```

est un lemme dérivé, prouvé seulement sous énumération finie/décidable.

### Phase F — minimales

Formaliser :

```text
IrreducibleClosed(I) ↔ MinimalCoveringCoalition(I)
```

### Phase G — recollement local

Formaliser avant les morphismes :

```text
LocalResidual(D,I) := D ∩ Res(I)
```

Puis :

```text
si les D_t couvrent R_σ
et chaque I_t couvre D_t
alors ⋃ I_t couvre R_σ.
```

C’est la première vraie propriété géométrique de recollement.

### Phase H — isomorphismes d’incidence

Commencer par les isomorphismes de systèmes d’incidence finis, pas les morphismes observationnels
généraux.

```text
IncidenceIso
→ preserves Res
→ preserves rho
→ preserves Closed
```

### Phase I — médiation géométrique

Formaliser :

```text
FiniteCoverExtension
MediatedCover
MinimalMediatedCover
NonDescent
```

## 15. Règles constructives

Pour rester compatible avec les règles Lean du projet :

```text
pas de Classical
pas de propext
pas de Quot.sound
pas d’axiom
pas de quotient de paires
pas d’égalité extensionnelle de sets si elle peut être évitée
```

Préférer :

```text
relations pointwise
listes explicites
témoins de membership
équivalences propositionnelles locales
formes witness-style
```

En particulier :

```text
Set equality
```

doit être remplacée par :

```text
∀ d, d ∈ A ↔ d ∈ B
```

ou par deux inclusions explicites.

Mais même :

```text
∀ d, d ∈ A ↔ d ∈ B
```

peut attirer des extensionalités si on le transforme en égalité. La règle sûre est :

```text
ne jamais transformer une équivalence pointwise en égalité globale
si ce n’est pas strictement nécessaire.
```

## 16. Critère de réussite

On pourra dire que la géométrie est complète lorsque les niveaux suivants seront formalisés :

```text
1. algèbre autonome des résidus ;
2. système abstrait d’incidence ;
3. réalisation observationnelle du système abstrait ;
4. Res comme préfaisceau contravariant ;
5. fermeture comme couverture ;
6. irréductibilité comme couverture minimale ;
7. incidence comme générateur de Res ;
8. recollement de couvertures locales ;
9. morphismes/isomorphismes de systèmes d’incidence ;
10. invariance de ρ, Closed, IrreducibleClosed ;
11. médiation comme extension finie de couverture ;
12. non-descente comme irréductibilité géométrique du supplément.
```

Formule finale :

```text
algèbre d’accès
→ préfaisceau des résidus
→ topologie de fermeture
→ géométrie des médiateurs minimaux.
```

## 17. Résumé

Nous avons déjà :

```text
le calcul interne des fermetures.
```

Il faut maintenant ajouter :

```text
la géométrie des changements de point de vue.
```

La phrase directrice :

```text
Une interface n’est pas seulement une observation ;
c’est un ouvert informationnel.

Une coalition n’est pas seulement un ensemble d’observations ;
c’est une famille couvrante potentielle.

Un médiateur n’est pas seulement un latent ;
c’est une extension finie qui ferme un défaut de couverture.
```

Ce document est donc le plan pour passer de :

```text
minimal access coalitions
```

à :

```text
geometry of informational closure.
```
