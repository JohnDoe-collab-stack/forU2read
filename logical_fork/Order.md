# Théorie des ordres dynamiques centrée sur l’interface

## 0. Thèse

La théorie ne porte pas d’abord sur des états, mais sur des **régimes de devenir**.
Elle étudie **cinq ordres** et une **relation de lisibilité**, à savoir :

1. **Ordre 1 (informationnel)** : ordre de raffinement des interfaces ;
2. **Relation (lisibilité)** : descente des tests dans l’ordre informationnel ;
3. **Ordre 2 (difficulté relative)** : ordre des tests au-dessus d’une base ;
4. **Ordre 3 (médiations)** : ordre des lifts au-dessus d’une base ;
5. **Ordre 4 (capacité)** : ordre des coûts dans une famille admissible ;
6. **Ordre 5 (stabilisation)** : ordre de solvabilité sous budgets croissants.

Le statique n’est qu’un cas dégénéré.

---

## 1. Primitives

### 1.1. Espace des comportements

La primitive fondamentale est un ensemble `B` de **comportements**.
Un élément de `B` peut être, selon le cadre :

- une trace ;
- un arbre de futurs ;
- une continuation ;
- un processus ;
- une sémantique locale de compatibilités futures ;
- ou tout autre objet dynamique.

Un système concret peut être représenté par une application

`Beh : X -> B`

depuis un espace de configurations internes `X`, mais **`X` n’est pas premier**.
Le niveau fondamental est `B`.

### 1.2. Interfaces

Une interface sur `B` est une observation effective

`obs_i : B -> Im(obs_i)`

On note `Int(B)` l’univers absolu de toutes les interfaces sur `B`.

### 1.3. Tests dynamiques

Un test dynamique est une application effective

`t : B -> Im(t)`

Un test n’est donc pas une propriété présente d’un état ; c’est une **question sur le comportement**.

### 1.4. Familles admissibles

On introduit une famille de sous-univers admissibles

`I_λ ⊆ Int(B)`

indexée par un ordre de budgets ou de ressources `(Λ, <=_Λ)`, avec la monotonie :

`λ <=_Λ μ  =>  I_λ ⊆ I_μ`

`Λ` peut mesurer :

- horizon de regard ;
- mémoire ;
- nombre de classes ;
- nombre de sondes ;
- coût d’implémentation ;
- profondeur de raffinement.

Cette donnée rend la théorie immédiatement dynamique et non purement informationnelle.

---

## 2. Premier ordre : l’ordre informationnel des interfaces

### Définition 1 — Raffinement

Pour deux interfaces `i,j ∈ Int(B)`, on pose

`i <= j`

s’il existe

`π(j,i) : Im(obs_j) -> Im(obs_i)`

telle que

`obs_i = π(j,i) ∘ obs_j`

Lecture : `j` est au moins aussi informative que `i`.

### Définition 2 — Noyau

Le noyau de `i` est

`K_i = { (b,b') in B^2 | obs_i(b) = obs_i(b') }`

### Proposition 1 — Caractérisation par noyaux

`i <= j  <=>  K_j ⊆ K_i`

Donc, modulo équivalence informationnelle,

`Int(B)/≡  ≅  Eq(B)^op`

Remarque (statut / Lean) : cette identification est à lire au niveau mathématique abstrait.
Dans la formalisation Lean du dépôt, on travaille directement avec les noyaux / setoids et les relations
de raffinement (factorisations), sans introduire de quotient-type global des interfaces.

En cadre absolu, on obtient un treillis complet :

- le **join** correspond à l’intersection des noyaux ;
- le **meet** correspond à l’équivalence engendrée par leur union.

C’est le premier ordre fondamental.

---

## 3. Lisibilité des tests dans l’ordre informationnel

### Définition 3 — Descente

Un test `t` descend à une interface `i` s’il existe

`t_i : Im(obs_i) -> Im(t)`

telle que

`t = t_i ∘ obs_i`

### Proposition 2 — Critère de descente

Les trois conditions suivantes sont équivalentes :

- `t` descend à `i`
- `t` est constant sur les classes de `K_i`
- `K_i ⊆ K_t`

Comme un test est lui-même une interface, cela se réécrit :

`t` descend à `i`  `<=>`  `t <= i`

### Définition 4 — Barrière dynamique

Il y a barrière pour `t` à `i` lorsque

`not (t <= i)`

Équivalemment, il existe `b,b'` tels que

`obs_i(b) = obs_i(b')` mais `t(b) != t(b')`.

Une barrière n’est donc pas une erreur d’algorithme.
C’est une **insuffisance d’ordre informationnel**.

### Proposition 3 — Monotonies élémentaires

- si `i ≤ j` et `t ≤ i`, alors `t ≤ j` ;
- si `i ≤ j` et `not (t <= j)`, alors `not (t <= i)`.

Le raffinement aide la descente ; l’appauvrissement propage les barrières.

---

## 4. Deuxième ordre : l’ordre de difficulté relative des tests

Tous les tests dynamiques n’exigent pas le même raffinement au-dessus d’une interface donnée.

### Définition 5 — Difficulté relative

Pour une interface de base `i`, on pose

`t ≼_i u`

si tout raffinement de `i` qui rend `u` lisible rend aussi `t` lisible :

`pour tout j >= i, si u <= j alors t <= j`.

Lecture : au-dessus de `i`, `t` est au plus aussi difficile à rendre lisible que `u`.

### Proposition 4 — Forme canonique

En cadre absolu,

`t ≼_i u  <=>  (i ∨ t) <= (i ∨ u)`

Corollaire (lecture “seuil de lisibilité”) :

- `t ≼_i u` implique `t <= (i ∨ u)` (prendre `j := i ∨ u` dans la définition).

Donc l’ordre de difficulté est un **ordre relatif au point de départ informationnel**.

C’est le deuxième ordre central de la théorie.

---

## 5. Troisième ordre : l’ordre des médiations

### Définition 6 — Lift

Un lift de `i` pour `t` est une interface `j` telle que

`i <= j` et `t <= j`.

En cadre absolu, c’est un majorant commun de `i` et `t`.

### Définition 7 — Lift canonique

Le plus petit lift absolu est le join

`L(i,t) := i ∨ t`

Son noyau vérifie

`K(i ∨ t) = K(i) ∩ K(t)`

Lecture : il ajoute exactement la séparation dynamique manquante pour rendre `t` lisible au-dessus de `i`.

### Cadre relatif

Dans un univers admissible `I_λ`, le join absolu peut ne pas appartenir à `I_λ`.
On introduit alors l’ensemble des lifts admissibles

`Lift_i^λ(t) := { j in I_λ | L(i,t) <= j }`

(En cadre absolu, c’est équivalent à demander séparément `i <= j` et `t <= j`.)

Le **meilleur lift interne** est le plus petit élément de cet ensemble, lorsqu’il existe.
Il peut ne pas exister.

La théorie doit donc étudier :

- existence ;
- non-existence ;
- multiplicité de minimaux incomparables ;
- stabilité des sous-familles admissibles par join.

C’est ici que la théorie devient vraiment une théorie des ordres, et non seulement des factorisations.

---

## 6. Quatrième ordre : l’ordre de capacité

Une médiation peut être minimale informationnellement sans être minimale en coût.

### Définition 8 — Capacité

On fixe un ordre `(C, <=_C)` et une application.

On pose `I_total := union over λ in Λ of I_λ`.

`Cap : I_total -> C`

### Définition 9 — Min-lift capacitaire

`MinLift_i^λ(t) := inf { Cap(j) | j in I_λ, L(i,t) <= j }`

Il faut distinguer trois notions :

1. **minimum informationnel absolu** : `(i ∨ t)` ;
2. **minimum interne admissible** : plus petit lift dans `I_λ`, s’il existe ;
3. **minimum de capacité** : borne inférieure de `Cap` sur les lifts admissibles.

Ces trois niveaux peuvent diverger.

C’est le quatrième ordre structurant : l’ordre des coûts de médiation.

---

## 7. Cinquième ordre : l’ordre de stabilisation

C’est ici que la théorie devient pleinement dynamique.

La question n’est plus seulement :

> “ce test descend-il déjà ?”

mais :

> “à quel stade de budget, de raffinement, de mémoire ou de profondeur la descente devient-elle stable ?”

### Définition 10 — Profil de solvabilité

Pour une base `i` et un test `t`, on définit le profil

`D(i,t,λ) :<=>  existe j in I_λ tel que i <= j et t <= j`

Ce profil est monotone en `λ` :

`λ <=_Λ μ  =>  D(i,t,λ) => D(i,t,μ)`

### Définition 11 — Rang (premier budget de solvabilité)

Quand `Λ` est bien ordonné ou ordinalisé, on définit

`rho(i,t) := min { λ in Λ | D(i,t,λ) }`

Quand un tel minimum n’existe pas, on peut n’avoir qu’un infimum, ou aucune stabilisation interne.

Remarque : ici, `rho(i,t)` mesure un **rang de solvabilité sous budget croissant**
(le premier niveau où un lift admissible existe). Si plus tard on introduit un opérateur
itératif de “stabilisation” (au sens fermeture/limite), il faudra distinguer nettement ces deux notions.

### Définition 12 — Obstruction de stabilisation

Il y a obstruction de stabilisation finie lorsque :

- `D(i,t,λ)` échoue à tout niveau fini ;
- mais réussit au niveau total ou limite.

C’est exactement le type de phénomène exprimé dans le dépôt par les schémas de `ProbeObstruction` et de non-stabilisation finie.

C’est le cinquième grand ordre de la théorie.

---

## 8. Causalité : non pas un ordre premier, mais une adéquation des lifts

La causalité n’est pas l’ordre fondamental.
Elle intervient comme **test d’adéquation** d’un lift dynamiquement forcé.

### Définition 13 — Adéquation causale

Un lift `j` de `i` pour `t` est causalement adéquat lorsqu’une lecture du médiateur vérifie au moins :

- **ablation** : supprimer le médiateur détruit la réussite ;
- **permutation** : permuter le médiateur fait suivre la décision ;
- **non-trivialité** : la permutation ne laisse pas le readout inchangé.

La causalité ne remplace donc pas la théorie des ordres.
Elle certifie que le lift minimal n’est pas seulement corrélé au succès, mais **charge effectivement la séparation dynamique requise**.

---

## 9. Théorème directeur de la théorie

La forme générale visée est :

> **une séparation dynamique intra-interface produit une barrière ;
> cette barrière force un lift ;
> ce lift se compare dans un ordre informationnel, dans un ordre de capacité, et dans un ordre de stabilisation ;
> lorsqu’il est minimal et interventionnellement actif, il admet une signature causale.**

C’est la colonne vertébrale.

---

## 10. Instanciation directe dans `COFRS`

Votre dépôt devient alors une famille d’instances de cette théorie.

### Version strictement dynamique (alignée “primitive comportementale”)

On fixe un préfixe `h`.

1) Niveau interne local (micro-états sur la fibre) :

`X_h := FiberPt obs target_obs h`.

2) Niveau comportemental local (devenir complet vu comme signature de compatibilité future) :

`Beh_h := Sig sem obs target_obs : X_h -> (Future h -> Prop)`.

3) Espace comportemental effectif :

on travaille sur `B_h_dyn := Im(Beh_h)`, c’est-à-dire les signatures qui apparaissent réellement.

4) Tests dynamiques premiers :

pour chaque `step : Future h`, on prend le test “évaluation”
`t_step : B_h_dyn -> Prop` défini par “lire la vérité de compatibilité au pas `step`”.

Sur les micro-états, le test correspondant est la réalisation via `Beh_h` :
`T_step := t_step ∘ Beh_h`, ce qui coïncide avec `CompatibleFuture sem obs target_obs step`.

5) Interface visible locale :

sur une fibre fixée, la valeur visible est constante par définition ; l’interface visible locale est donc
triviale (vers `Unit`). Les témoins `LagEvent` / `StepSeparatesFiber` expriment alors exactement que certains
tests `T_step` ne descendent pas à cette interface triviale.

### Pont comportement / représentation (point de fond)

Dans l’instanciation `COFRS`, les objets de médiation (`CompatDimLe`, `RefiningLiftData`, etc.) sont
définis d’abord au niveau représentationnel `X_h`.

Or, dans la théorie abstraite, les interfaces admissibles vivent sur l’espace des comportements `B`.
Pour lire une observation concrète `e : X_h -> W` comme une interface de la théorie, on impose la
condition d’**invariance comportementale** :

- si `Beh_h x = Beh_h x'` alors `e x = e x'`.

Équivalemment, `e` factorise par `Beh_h` : il existe `e_bar : B_h_dyn -> W` telle que
`e = e_bar ∘ Beh_h`.

Sans cette condition, un witness Lean peut sur-séparer des micro-états qui ont pourtant le même
comportement (même signature `Sig`), ce qui relève du niveau implémentationnel plutôt que du niveau
comportemental de la théorie.

### Médiation

`CompatDimLe n` et `RefiningLift` réalisent l’existence d’un lift interne de capacité finie `n`,
dans la mesure où les witnesses sont lus comme interfaces de la théorie via le pont
“invariance comportementale / factorisation par `Beh_h`” ci-dessus (sinon, ils restent au niveau représentationnel sur `X_h`).

### Capacité

La dimension `n` de `Fin n` est une instance directe de `Cap`.

### Stabilisation

`ProbeObstruction`, `StableAt`, `FinitaryCompactness` donnent déjà une première théorie de l’ordre de stabilisation.

### Causalité

`CausalSignature2` exprime l’adéquation causale d’un lift binaire forcé.

Donc le dépôt n’est pas encore la théorie générale des ordres, mais il en fournit déjà les **schémas dynamiques canoniques**.

---

## 11. Programme d’écriture

La théorie complète doit maintenant être rédigée dans cet ordre :

1. **Ordre informationnel** des interfaces dynamiques ;
2. **Ordre de difficulté relative** des tests dynamiques ;
3. **Ordre des lifts** et join canonique ;
4. **Ordre de capacité** sur les lifts admissibles ;
5. **Ordre de stabilisation** sous budgets croissants ;
6. **Adéquation causale** des lifts minimaux.

C’est cette hiérarchie qui fait une vraie **théorie des ordres dynamiques**.
