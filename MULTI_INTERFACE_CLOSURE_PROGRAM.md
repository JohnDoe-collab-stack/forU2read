# Programme multi-interface : fermeture, residual, mediation

Statut : note de travail theorique. Aucun resultat experimental nouveau n'est affirme ici.

Etat actuel apres formalisation Lean :

```text
la piece formelle centrale existe maintenant dans COFRS/MultiInterface.lean ;
ce qui reste avant de parler de theorie complete est surtout :
  1. l'audit empirique multi-interface ;
  2. la version heterogene des interfaces.
```

Le fichier Lean couvre deja la chaine statique, structurelle et dynamique :

```text
residual / rho / incidence / fermeture / coalitions minimales
-> utilite locale / redondance locale / essentialite par ablation
-> prediction par sous-famille / descente du mediateur / end-to-end dynamique
```

But : etudier serieusement si la decouverte actuelle peut etre generalisee a un nombre arbitraire
d'interfaces, et preciser ce qu'il faut prouver, mesurer, puis formaliser.

Phrase centrale :

> Le vrai objet n-interface est l'incidence des distinctions perdues ; la fermeture est l'annulation
> du residual commun ; l'irreductibilite est la minimalite de la sous-famille qui annule ce residual.

## 1. Point de depart dans le projet

Le projet contient deja trois morceaux compatibles.

1. Couche Lean binaire.
   `COFRS/Synthesis.lean` definit la jonction de deux interfaces :

   - `obsAB obsA obsB : S -> VA x VB`
   - `targetAB targetA targetB : P -> VA x VB`
   - `LeftObsPredictsJointStep`
   - `RightObsPredictsJointStep`
   - `MediatorDescendsLeft`
   - `MediatorDescendsRight`
   - `JointIrreducibleMediationProfile`

   Cette couche dit deja : le couple d'interfaces peut fermer une prediction dynamique alors
   qu'aucune projection gauche/droite ne suffit.

2. Couche algebre finie exacte.
   `Empirical/aslmt/algebra_kernel/algebra_core.py` formalise :

   - les partitions finies,
   - les distinctions requises par une signature `sigma`,
   - les confusions d'une interface,
   - la perte `L_j = R_sigma cap C_j`,
   - le residual commun `cap_j L_j`,
   - le scalaire `rho`,
   - le gain marginal `delta_gain`.

3. Couche notes privees.
   `Private_notes/distinction_arithmetic_refined.md` contient deja l'idee n-interface :

   - `rho_sigma(A_1, ..., A_n) = #(L_A1 cap ... cap L_An)`,
   - fermeture si le residual est vide,
   - necessite de garder une incidence d'ordre superieur, pas seulement un scalaire.

La question n'est donc pas "peut-on imaginer plusieurs interfaces ?", mais :

> quelle definition n-interface conserve exactement le no-go binaire, le residual fini, et la mediation dynamique ?

## 2. Definition abstraite n-interface

Soit un espace d'etats `S`, une famille finie d'interfaces indexee par `J`, et une signature cible
`sigma : S -> Y` ou bien une propriete dynamique `step`.

Pour chaque interface `j : J`, on a une observation :

```text
obs_j : S -> V_j
```

Pour une sous-famille `I subset J`, l'observation jointe est :

```text
Joint_I(s) = (obs_j(s))_{j in I}
```

Dans Lean, la version constructive la plus simple n'est pas de commencer par un produit heterogene.
On peut commencer par une famille homogene :

```text
obs : J -> S -> V
Joint_I(s) : forall j, I j -> V
```

La version heterogene `V_j` peut venir ensuite, via une fonction dependante :

```text
Joint_I(s) : forall j, I j -> V j
```

Cela evite de choisir arbitrairement une liste ou un encodage de tuples, et reste compatible avec une
formalisation constructive.

## 3. Fermeture par sous-famille

Une sous-famille `I` ferme la signature `sigma` si la cible factorise par l'observation jointe.

```text
Closed(I, sigma) :=
  exists pred,
    forall s, sigma s = pred (Joint_I s)
```

Pour une propriete propositionnelle dynamique :

```text
PredictsStep(I, step) :=
  exists pred,
    forall x in fiber,
      Compatible(..., step, x) <-> pred (Joint_I x)
```

Dans le cas binaire, `I = {A, B}` redonne le role de `obsAB`. Les projections strictes `I = {A}` et
`I = {B}` redonnent `LeftObsPredictsJointStep` et `RightObsPredictsJointStep`.

## 4. Residual fini et critere exact

Dans un univers fini `X = {0, ..., n-1}`, une signature `sigma` impose un ensemble de distinctions :

```text
R_sigma = { {x,y} | sigma(x) != sigma(y) }
```

Chaque interface `j` a des confusions :

```text
C_j = { {x,y} | obs_j(x) = obs_j(y) }
```

La perte de l'interface `j` relativement a `sigma` est :

```text
L_j = R_sigma cap C_j
```

Le residual d'une sous-famille `I` est :

```text
L_res(I) = cap_{j in I} L_j
```

Avec la convention :

```text
L_res(empty) = R_sigma
```

Cette convention est obligatoire. Sans elle, le residual de depart serait ambigu : avant toute interface,
toutes les distinctions requises par `sigma` sont encore a couvrir.

Le scalaire :

```text
rho_sigma(I) = #L_res(I)
```

Critere central :

```text
Closed(I, sigma)  <->  L_res(I) = empty
```

Interpretation : une famille d'interfaces ferme la cible exactement quand aucune distinction requise
par `sigma` n'est perdue par toutes les interfaces de la famille.

## 5. Pourquoi le scalaire rho ne suffit pas

`rho_sigma(I)` mesure la taille du trou residuel commun, mais il ne dit pas quelles interfaces causent
quelles pertes, ni quelles combinaisons les corrigent.

Il faut donc conserver une structure d'incidence, par exemple :

```text
Incidence_sigma(U) = R_sigma cap cap_{j in U} L_j
```

ou une table par distinction :

```text
d in R_sigma |-> { j : J | d in L_j }
```

Cette incidence permet de distinguer :

- une interface inutile,
- une interface redondante,
- une interface complementaire,
- une interface indispensable seulement dans une coalition,
- une famille minimale qui ferme `sigma`.

Conclusion : pour n interfaces, le vrai objet est l'incidence des pertes. `rho` est une projection utile,
mais pas une description complete.

Formule courte :

```text
multi-interface = incidence des pertes
```

et non :

```text
multi-interface = simple scalaire rho
```

## 5bis. Non-redondance et diagonalisation entre interfaces

L'ajout d'interfaces n'a d'interet scientifique que si les nouvelles interfaces ne sont pas redondantes.
Une interface qui repete les memes confusions qu'une autre ne change ni le residual, ni la fermeture,
ni la mediation.

Pour une sous-famille deja choisie `I`, une nouvelle interface `j` est redondante relativement a `I` si :

```text
L_res(I union {j}) = L_res(I)
```

Equivalentement, son gain marginal est nul :

```text
delta_gain(I, j) = 0
```

Elle est utile seulement si elle retire au moins une distinction encore residuelle :

```text
delta_gain(I, j) > 0
```

Mais il faut distinguer deux niveaux.

1. Non-redondance locale.
   `j` apporte quelque chose apres la famille courante `I`.

2. Non-redondance structurelle.
   `j` couvre une zone de distinctions que les autres interfaces couvrent mal, et reste visible dans
   les ablations de sous-familles.

La diagonalisation est exactement cette exigence structurelle. Elle consiste a organiser les interfaces
pour que leurs pertes ne soient pas alignees sur les memes distinctions requises.

On peut representer cela par une matrice d'incidence :

```text
D(d,j) = 1  si la distinction d est perdue par l'interface j
D(d,j) = 0  si l'interface j separe la distinction d
```

Le residual d'une famille `I` est alors l'ensemble des lignes `d` telles que :

```text
forall j in I, D(d,j) = 1
```

Fermer la cible revient a ne laisser aucune ligne entierement perdue. Diagonaliser les interfaces revient
a eviter que les colonnes de `D` soient identiques ou trop correlees sur `R_sigma`.

Donc le principe n-interface correct n'est pas :

```text
ajouter beaucoup d'interfaces
```

mais :

```text
ajouter des interfaces dont les noyaux/confusions sont suffisamment transverses
```

Formule conceptuelle :

```text
interfaces utiles = noyaux de confusion transverses sur R_sigma
```

Dans les audits, cela impose de mesurer au minimum :

- les gains marginaux `delta_gain(I,j)`,
- les intersections de pertes `L_i cap L_j`,
- les intersections d'ordre superieur `cap_{j in U} L_j`,
- les sous-familles minimales qui ferment,
- les interfaces qui deviennent inutiles apres ablation ou remplacement.

Une interface n'est donc pas valide parce qu'elle existe ; elle est valide parce qu'elle diagonalise une
partie du residual que les autres interfaces ne diagonalisaient pas.

## 6. Irreductibilite n-interface

Une famille `I` est irreductible pour `sigma` si elle ferme la cible, et aucune sous-famille stricte ne
la ferme :

```text
IrreducibleClosure(I, sigma) :=
  Closed(I, sigma)
  and
  forall K subset I,
    K != I -> not Closed(K, sigma)
```

Version residuale finie equivalente :

```text
L_res(I) = empty
and
forall K proper subset I, L_res(K) != empty
```

Cette definition generalise exactement le phenomene binaire :

```text
Closed({A,B}) and not Closed({A}) and not Closed({B})
```

## 7. Mediation n-interface

La mediation ajoute une observation etendue :

```text
extObs : FiberPt(...) -> V_joint x Fin n
```

Pour deux interfaces, le projet teste si le mediateur descend vers la gauche ou la droite.

Pour n interfaces, la bonne generalisation est :

```text
MediatorDescendsTo(K) :=
  exists rhoK,
    forall x,
      mediator(x) = rhoK(Joint_K x)
```

ou, plus proche du fichier actuel :

```text
forall x, (L.extObs x).2 = rhoK (Joint_K x)
```

Une mediation est irreductible sur `I` si elle ne descend vers aucune sous-famille stricte pertinente :

```text
IrreducibleMediator(I) :=
  forall K proper subset I,
    not MediatorDescendsTo(K)
```

Selon l'usage, il faut separer deux notions :

1. Fermeture directe : `Closed(I, sigma)`.
2. Fermeture apres mediation : il existe une extension de dimension `n` qui rend la prediction stable.

Ces deux notions ne doivent pas etre confondues. Une famille peut reduire fortement le residual sans
le fermer directement ; la mediation mesure alors la taille et la structure de ce qui reste.

## 8. Capacite apres interfaces

Pour une sous-famille `I`, on peut definir une capacite residuelle :

```text
Cap(I) = plus petit n tel que CompatDimLe(Joint_I, step, n)
```

Si le projet evite les minimums non constructifs, on peut travailler avec une relation :

```text
CompatDimLeForFamily(I, n)
```

puis prouver seulement les implications utiles :

- si `I subset K`, alors ajouter des interfaces ne doit pas empirer la capacite ;
- si `Closed(I, step)`, alors la capacite residuelle attendue est minimale ;
- si `rho_sigma(I) > 0`, alors une obstruction finie reste visible dans le residual.

## 9. Theoremes a viser

### Theoremes finis exacts

1. Monotonie du residual.

```text
I subset K -> L_res(K) subset L_res(I)
```

2. Monotonie de `rho`.

```text
I subset K -> rho(K) <= rho(I)
```

3. Fermeture exacte.

```text
Closed(I, sigma) <-> rho(I) = 0
```

4. Gain marginal.

```text
delta_gain(I, j) = #(L_res(I) \ L_j)
```

Definition explicite :

```text
delta_gain(I,j)
  = rho(I) - rho(I union {j})
  = #(L_res(I) \ L_j)
```

La premiere forme mesure la contraction du residual. La seconde forme dit quelles distinctions encore
residuelles sont separees par la nouvelle interface `j`.

5. Irreductibilite minimale.

```text
IrreducibleClosure(I, sigma)
<->
rho(I) = 0 and forall K proper subset I, rho(K) > 0
```

Nom Lean cible :

```lean
familyIrreducibleClosure_iff_residual_zero_and_proper_residual_pos
```

Enonce cible :

```lean
IrreducibleClosure I sigma
↔
rho sigma I = 0 ∧
  ∀ K, K ⊂ I → rho sigma K > 0
```

### Theoremes dynamiques

1. Specialisation de `Closed(I, step)` a `Compatible`.
2. Generalisation de `JointIrreducibleMediationProfile`.
3. Non-descente vers toute sous-famille stricte.
4. Lien entre residual fini et obstruction dynamique quand la dynamique est discretisee.

Noms Lean cibles :

```lean
familyIrreducibleMediationProfile_of_sep_and_dim
```

Enonce vise :

```lean
FamilyStepSeparates ... I step
∧ CompatDimEq ... (JointObs obs I) step n
→ FamilyIrreducibleMediationProfile ... I step n
```

```lean
not_mediatorDescendsSubfamily_of_familyIrreducibleProfile
```

Enonce vise :

```lean
K ⊂ I →
¬ MediatorDescendsSubfamily K L
```

## 10. Plan Lean constructif

Ne pas commencer par la version la plus generale. Le chemin le plus sur est :

### Phase A : famille homogene finie avec `Finset J`

Ajouter un fichier Lean separe, par exemple :

```text
COFRS/MultiInterface.lean
```

Hypotheses finies de depart :

```lean
[DecidableEq J]
[DecidableEq S]
[Fintype J]
[Fintype S]
[DecidableEq Y]
```

Elles correspondent au regime exact ou les distinctions, les pertes, les residuals et `rho` sont des
objets finis calculables.

Definitions candidates :

```lean
def JointObs (obs : J → S → V) (I : Finset J) ...

def Residual sigma obs I

def rho sigma obs I

def SubfamilyPredictsStep ...

def MediatorDescendsSubfamily ...

def FamilyIrreducibleMediationProfile ...
```

Cette phase doit privilegier `Finset J` plutot que seulement `I : J -> Prop`, parce que les sous-familles,
les inclusions strictes, les ablations et les calculs de residual sont plus naturels et plus auditables
sur des ensembles finis explicites.

La forme propositionnelle `I : J -> Prop` reste utile conceptuellement, mais elle n'est pas le meilleur
point de depart pour la phase finie.

### Phase B : specialisation finie

Ajouter ensuite les hypotheses finies necessaires :

```text
J finite
S finite
```

Puis relier les definitions aux distinctions :

```text
RequiredDistinctions
Confusions
Loss
Residual
rho
```

Le point delicat est de rester constructif. Il faut eviter toute preuve qui appelle `Classical`,
`propext`, `Quot.sound`, ou un axiome caché.

### Phase C : version heterogene

Une fois la phase homogene stable, passer a :

```lean
obs : ∀ j : J, S → V j
JointObs : S → (∀ j, j ∈ I → V j)
```

Cela donnera la vraie version "autant d'interfaces de types differents qu'on veut".

## 11. Plan empirique sans casser la tracabilite

Les scripts historiques ne doivent pas etre modifies. Toute variante doit etre un nouveau fichier.

Experiences a construire dans un nouveau script :

```text
compatdim_multiview_audit_v1.py
```

ou similaire.

Audits a produire :

1. Verifier `rho(I)` pour toutes les sous-familles quand `|J|` est petit.
2. Verifier les familles minimales de fermeture.
3. Mesurer les gains marginaux et comparer au greedy.
4. Distinguer les cas :
   - redondance,
   - complementarite,
   - synergie stricte,
   - interface inutile,
   - residual irreductible.
5. Pour de grands `|J|`, echantillonner les sous-familles mais garder les petites exhaustives.

Toute execution scientifique doit utiliser une copie figee timestamp+hash, et les sorties doivent
reprendre exactement le meme suffixe.

## 12. Positionnement scientifique

Le programme ne doit pas etre presente comme une invention de la selection de capteurs. Cette litterature
existe deja :

```text
sensor selection
active sensing
submodular information gain
minimal or sparse sensor subsets
POMDP active perception
```

Par exemple, Zhang et Ji, "Sensor Selection for Active Information Fusion" (AAAI 2005), cherchent des
sous-ensembles de capteurs avec un bon compromis entre gain d'information et cout, en exploitant la
synergie entre capteurs pour reduire la recherche combinatoire.

La difference centrale est ailleurs. Ici, le critere vise n'est pas seulement informationnel, statistique
ou economique. Il est logique et structural :

```text
fermeture exacte
+ residual de distinctions
+ irreductibilite de toutes les sous-familles strictes
+ mediateur ou joint minimal
```

Formulation stricte :

```text
minimal access coalitions
= subfamilies of interfaces
  whose combined observations close target-required residual distinctions
  while every strict subfamily fails
```

Donc la contribution a viser n'est pas :

```text
we discover sensor selection
```

mais :

```text
we introduce a theory of minimal access coalitions
```

Formulation papier possible :

```text
We introduce a theory of minimal access coalitions:
finite subfamilies of interfaces whose joint observations close the residual
distinctions required by a target, while every strict subfamily fails.
```

Cette formulation est plus solide que "discovers", parce qu'elle reconnait le prior art tout en isolant
la nouveaute : un critere de fermeture par coalitions minimales fonde sur les distinctions residuelles.

Reference de contexte :

```text
Yongmian Zhang and Qiang Ji.
Sensor Selection for Active Information Fusion.
AAAI 2005.
https://auld.aaai.org/Library/AAAI/2005/aaai05-195.php
```

## 13. Reponse provisoire a la question

Oui, la decouverte peut avoir autant d'interfaces qu'on veut, mais pas sous la forme naive :

```text
rho(A,B,C,...) comme simple nombre
```

La bonne generalisation est :

```text
famille d'interfaces
-> residual commun de distinctions
-> incidence des pertes
-> fermeture par sous-famille
-> irreductibilite par toutes les sous-familles strictes
-> mediation qui ne descend vers aucune sous-famille suffisante
```

Le binaire actuel n'est alors que le premier cas non trivial.

En formulation scientifique :

```text
Le programme multi-interface transforme la decouverte binaire
en theorie des coalitions minimales d'acces informationnel.
```

Le vrai risque theorique est de perdre l'information d'incidence en ne gardant que `rho`. Le vrai risque
Lean est de commencer trop vite par des produits heterogenes. Le chemin robuste est donc :

1. formaliser les sous-familles homogenes ;
2. prouver les definitions dynamiques n-interface ;
3. relier au residual fini ;
4. seulement ensuite passer aux interfaces heterogenes.
