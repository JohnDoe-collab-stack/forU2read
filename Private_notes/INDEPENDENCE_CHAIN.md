# Indépendance → Rapport → Médiateur : chaîne complète

## Pourquoi ce n’est pas une “reformulation statique”

Une vue **statique** typique se limite à constater que :

- chaque marge prise seule peut être insuffisante (`A` ne détermine pas `T`, et `B` ne détermine pas `T`) ;
- alors que le joint `⟨A,B⟩` peut suffire à décider `T`.

La méthode ici n’est pas une reformulation de ce constat. Elle change l’objet et le type de conclusion :

- la vérité `T` est **dynamique** (compatibilité future le long d’un `step` depuis un point de fibre), pas une cible statique ;
- l’échec des décisions “marge-only” est **forcé** par une obstruction intra-fibre (diagonalisation), pas seulement observé ;
- le “rapport” requis est **quantifié minimalement** (capacité finie `Fin n`) et réalisé canoniquement (factorisation) ;
- et, dans les cas pertinents, cette médiation forcée admet une **signature interventionnelle** (swap/ablation) qui atteste qu’elle est effectivement déterminante.

## 0) Cadre (objets)

- Un espace d’états `S`.
- Une vérité dynamique locale à décider, typiquement
  `T(x) := Compatible sem obs target_obs step x`
  (donc dépend d’un `step` futur et d’un point de fibre au présent).
- Deux interfaces partielles (deux “marges”, deux vues) :
  `A : S → VA` et `B : S → VB`.

Dans le dépôt, on instancie ce schéma en choisissant `obs := A` ou `obs := B` (ou `obs := (A,B)`).

## 1) Notion d’“indépendance” (au sens structurel du dépôt)

Ici, “indépendance” ne veut pas dire probabiliste. Elle veut dire :

> **l’interface ne détermine pas la vérité dynamique**.

Formellement, pour une interface `A`, c’est exactement le contenu de :
- **échec de clôture** : `¬ ObsPredictsStep` (avec `obs := A`)  
  (aucune règle dépendant *seulement* de `VA` ne décide correctement `T` sur la fibre pertinente).

Et, quand on peut extraire un témoin (hypothèses finitaires/constructives), cet échec se manifeste comme :
- **séparation intra-fibre** : `StepSeparatesFiber`  
  (il existe deux micro-états indiscernables par `A` mais distingués par `T`).

Donc l’indépendance “A seule ne suffit pas” = **non-clôture obs-only** = **variation de `T` à l’intérieur d’une fibre de `A`**.

Même chose pour `B`.

## 2) Diagonalisation ⇒ indépendance certifiée

La diagonalisation (au sens du dépôt) produit un témoin d’obstruction (`LagEvent`) qui force l’indépendance :

- `LagEvent → ¬ ObsPredictsStep` (pour l’interface considérée).

C’est la partie “destruction du régime statique” : toute décision *obs-only* échoue parce que la vérité dynamique varie dans une même fibre.

## 3) Pont (bridge) : du négatif (`¬ ObsPredictsStep`) à un témoin explicite (`StepSeparatesFiber`)

Pour “sortir du conditionnel” (extraire un témoin sans choix classique), la méthode passe par une hypothèse **constructive de finitude** de la fibre + décidabilité de `Compatible` sur la fibre.

Chaîne (forme la plus longue) :

1. On suppose une finitude *donnée* de la fibre, sous forme d’une **équivalence explicite**  
   `Equiv (FiberPt obs target_obs h) (Fin N)`  
   (pas “Fintype + choix”, mais une donnée constructive).
2. On convertit ça en **énumération finitaire** (`FiberEnum`) via le bridge
   `FiberEnum.ofEquivFin`.
3. Avec `decCompat` (décidabilité de `Compatible` sur la fibre), on obtient :
   `¬ ObsPredictsStep → StepSeparatesFiber`  
   via le bridge
   `stepSeparatesFiber_of_not_obsPredictsStep_of_equivFin`
   (celui qu’on vient d’ajouter dans `COFRS/ConverseNormalForm.lean`).

C’est exactement le passage “indépendance certifiée” → “témoin constructif”.

## 4) Séparation ⇒ borne informationnelle minimale (dimension)

Une fois `StepSeparatesFiber` obtenu, la méthode ne s’arrête pas à “ça échoue” : elle quantifie l’écart.

- `StepSeparatesFiber` interdit `CompatDimLe 1` (tu ne peux pas résumer en 1 classe).
- Sous décidabilité, on a typiquement `CompatDimLe 2` (un prédicat décidable se résume en 2 classes).
- Donc on ferme une **minimalité binaire** : `CompatDimEqTwo` (dans les cas où la borne est serrée).

C’est le moment “l’écart devient un objet mesuré”.

## 5) Dimension ⇔ médiateur fini canonique (factorisation forcée)

Le dépôt a l’équivalence centrale :

- `CompatDimLe … n ↔ RefiningLift … n`.

Donc la “réparation” n’est pas un raffinement ad hoc, c’est :

- construire un **médiateur fini** `Fin n` (supplément minimal en capacité),
- et une interface raffinée `extObs : fiber → V × Fin n`
  telle que la vérité dynamique factorise par ce supplément.

C’est la formalisation exacte de “le surplus relationnel devient un troisième terme”.

## 6) Médiation ⇒ signature causale testable

Dans le cas binaire (notamment `n = 2`), la méthode ajoute une couche opérationnelle :

- `StepSeparatesFiber` + `RefiningLift 2` ⇒ `CausalSignature2`
  (ablation + permutation).

Donc le “troisième terme” n’est pas seulement une factorisation descriptive : il devient **auditable** par interventions.

## 7) Où intervient “deux indépendances” et le “rapport irréductible” ?

Avec deux interfaces `A` et `B`, la forme forte (“écart maximal” au sens que tu décris) s’écrit proprement comme :

- **Indépendance marginale double** :
  `¬ ObsPredictsStep` pour `obs := A` **et** `¬ ObsPredictsStep` pour `obs := B`.
- **Séparation jointe (ingrédient propre de la forme forte)** :
  il faut (et le spine utilise explicitement) une séparation **sur la fibre jointe** pour `obs := (A,B)` :
  `StepSeparatesFiber` sur `AB`.  
  Remarque importante : cette séparation jointe **ne découle pas automatiquement** de la double insuffisance
  marginale ; elle intervient comme hypothèse/témoin spécifique de la version “maximale”.
- **Existence d’un terme relationnel qui ferme** :
  opérationnellement, le dépôt ne postule pas un “`R` ontologique unique” : il exhibe une médiation **canonique**
  sous forme d’un supplément fini `Fin n` (capacité minimale), via `CompatDimEq n` / `RefiningLiftData`.
- **Irréductibilité (forme forte)** :
  ni la **vérité jointe** ni le **supplément minimal** ne “descendent” à un bord isolé : la prédiction jointe est
  impossible depuis `A` seul ou `B` seul, et (plus fort) la composante `Fin n` d’un témoin canonique de médiation
  n’est reconstructible ni depuis `A` seul ni depuis `B` seul.
- **Dominance** (forme “maximale”) :
  tout ce qui décide effectivement passe par `R` (au sens factorisation + signature interventionnelle).

Remarque de clarification : “rapport irréductible” ne signifie pas “prendre simplement le joint `⟨A,B⟩`”.
L’idée est qu’il existe un contenu décisif qui **n’apparaît dans aucune des deux marges** (et qui rend leurs
décisions marginales impossibles), et que ce contenu peut ensuite être (i) isolé comme un médiateur minimal
(`Fin n`) et (ii) validé opérationnellement via des interventions.

Autre remarque de précision : le symbole `R` sert ici d’intuition (rapport/couplage). Dans Lean, ce qui est
canonique est : (a) une **capacité minimale** `n` (compatibility dimension), et (b) un **témoin de médiation**
`RefiningLiftData` qui réalise cette capacité par un supplément fini `Fin n`, sans prétendre à une unicité
ontologique du médiateur.

### 7.1 Isolation de l’objet irréductible (au niveau du médiateur)

La formulation la plus forte ne s’arrête pas à l’irréductibilité de **la prédiction** (“`T_joint` n’est pas lisible
depuis `A` seul / `B` seul”). Elle isole aussi un **objet** irréductible : le *médiateur* lui-même.

Dans le cadre COFRS, cet objet est la composante finie `Fin n` portée par un témoin de médiation canonique
`RefiningLiftData` sur la fibre jointe : c’est le second composant de `extObs : fiberAB → (VA×VB) × Fin n`.

Dire que cet objet est irréductible aux deux marges signifie (opérationnellement), **pour un témoin donné**
`L : RefiningLiftData ... n` :

- **non-descente à gauche** : il n’existe pas de lecture `ρA : VA → Fin n` telle que, pour tout point de fibre
  `x`, la classe médiatrice `(extObs x).2` soit égale à `ρA (obsA x.1)` ;
- **non-descente à droite** : il n’existe pas de lecture `ρB : VB → Fin n` telle que `(extObs x).2 = ρB (obsB x.1)`.

Cette forme “descente du médiateur” est plus forte que la simple illisibilité de `T_joint` : elle dit que même le
supplément minimal qui répare la décision ne peut pas être reconstruit depuis un bord pris isolément. Dans la
preuve Lean, on obtient typiquement ces non-descentes en montrant que “descente ⇒ prédiction marginale”, puis
en détruisant la prédiction marginale par séparation intra-fibre.

Remarque de quantification : si l’on veut une conclusion indépendante du choix de `L`, on la formule
universellement : “pour **tout** témoin `L` de médiation canonique de capacité `n`, la non-descente vaut”.
Dans le code, les lemmes sont formulés de manière à pouvoir conclure ainsi, car `L` est arbitraire une fois
la séparation jointe fixée.
