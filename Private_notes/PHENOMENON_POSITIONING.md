# Positionnement mathématique — “obstruction diagonale → médiation forcée → extension”

Cette note fixe un positionnement mathématique (non-empirique) du phénomène central :

> Une non-clôture (témoignable par diagonalisation) n’est pas seulement un *no-go* ; c’est un **moteur génératif**
> qui force (i) une factorisation, (ii) l’apparition d’un médiateur non descendant aux marginales,
> et (iii) une extension canonique du référentiel qui restaure une clôture.

---

## 1) Définition intensive (le phénomène, en une phrase)

Les mathématiques ne sont plus vues seulement comme “des vérités dans un cadre fixé”, mais comme une théorie des
**régimes de clôture relatifs à une interface** et des **transitions forcées de référentiels** :

> Une obstruction diagonale est une donnée constructive qui détermine la forme de la médiation requise et la forme
> canonique de l’extension du visible, et ce schème peut être itéré sous forme de dérivation témoinée.

Cette définition est “intensive” au sens où elle caractérise la nature du phénomène : ce n’est pas un objet, c’est
une **loi de passage**.

---

## 2) Schème canonique (forme minimale)

On considère un référentiel `(X, q : X → Q, T : X → Prop)` :

- **Clôture** : `T` est *close* sur `q` quand `T` factorise par `q`.
- **Obstruction (diagonale)** : il existe une fibre de `q` sur laquelle `T` varie.
- **Médiation finie** : `T` est décidée par un résumé fini `σ : X → Fin n`.
- **Non-descente** : `σ` n’est pas une fonction de `q` (sinon `T` fermerait déjà).
- **Extension** : `q' x := (q x, σ x)` ferme `T`.

Le schème est :

1. `DiagonalWitness` (variation intra-fibre)
2. `MediatesLe` (un résumé fini décide la vérité)
3. donc `¬ DescendsToQuot` (le résumé ne descend pas aux marginales)
4. et `Closes(extendQuot)` (l’extension ferme)

Ce noyau a deux traits : il est **structurel** (pas probabiliste), et **itérable** (il supporte une chaîne de transitions).

---

## 3) Différences avec des phénomènes classiques (cartographie)

Le phénomène ressemble partiellement à plusieurs constructions connues, mais il ne se réduit à aucune.
On peut le situer proprement par “ce qui est premier” et “ce qui est forcé”.

### 3.1 Complétion (ex. complétion métrique)

Ressemblance :
- on adjoint quelque chose pour rendre une propriété vraie (fermeture).

Différence :
- la complétion vise typiquement un **objet terminal** (une clôture globale) dans une classe,
  alors qu’ici l’objet premier est une **transition guidée par obstruction** (référentiel → référentiel),
  et la clôture est relative à une interface, pas une propriété absolue de l’objet.

### 3.2 Localisation (inversion de morphismes)

Ressemblance :
- changer de cadre rend visibles des distinctions auparavant indiscernables.

Différence :
- la localisation est guidée par une **classe de morphismes à inverser** ;
  ici le moteur est une **obstruction diagonale** (variation dans une fibre) qui force un médiateur.

### 3.3 Adjonction libre / objets universels (free constructions)

Ressemblance :
- l’extension `q ↦ (q, σ)` est une adjonction d’information structurée.

Différence :
- l’adjonction libre est “générique” (définie par une propriété universelle externe) ;
  ici l’extension est **déterminée par la vérité visée** et sa non-clôture sur l’interface.
  Le médiateur n’est pas décoratif : il est forcé par la variation intra-fibre.

### 3.4 Théorie des obstructions (lifting problems)

Ressemblance :
- un témoin d’obstruction force l’impossibilité d’un relèvement dans le cadre courant.

Différence :
- ici l’obstruction ne conclut pas seulement “pas de relèvement” :
  elle **spécifie** la médiation manquante et fournit un schème canonique d’extension (`extendQuot`).
  Le “pas” est un objet mathématique (pas uniquement une information négative).

### 3.5 Forcing (extension contrôlée)

Ressemblance :
- on étend le cadre en ajoutant une information “nouvelle” pour rendre une propriété réalisable.

Différence :
- le forcing est une méthode de construction de modèles (souvent non constructive) ;
  ici le schème est constructive et local : il part d’une fibre, force une factorisation,
  et spécifie un médiateur fini (quand il existe) comme réparation.

### 3.6 Systèmes de factorisation / images

Ressemblance :
- la notion “descend / ne descend pas” est une contrainte de factorisation.

Différence :
- le point premier n’est pas un morphisme mais une **vérité relative à une interface**,
  et la factorisation est pilotée par la structure de fibres (diagonale).

---

## 4) Ce qui rend le phénomène “nouveau” (signature)

La signature distinctive est la conjonction de cinq composantes :

1) **Vérité interface-relative** (clôture sur `q`, pas vérité absolue “dans le vide”)
2) **Diagonalisation comme donnée générative** (obstruction = signal de transition)
3) **Médiateur caractérisé par non-descente** (il porte l’intra-fibre)
4) **Extension canonique** (`q ↦ (q, σ)` comme réparation minimale du point de vue de la clôture)
5) **Itération disciplinée** (re-ciblage + témoin que la nouvelle cible utilise l’extension)

La cinquième composante transforme le schème en une **induction structurelle** :
une dérivation porte les raisons de chaque pas (témoins), plutôt qu’une simple indexation.

---

## 5) Visée mathématique (ce qui manque pour une “forme universelle” complète)

Le noyau “pas + chaîne” fixe la grammaire. La visée forte est une propriété universelle de type factorisation :

> Parmi toutes les extensions d’interface qui ferment `T`, il existe une extension canonique
> telle que toute autre extension qui ferme `T` factorise (au sens approprié) par elle.

Cette visée a deux variantes naturelles :

- **(U1) Minimalité relative à `T`** : la canonisation dépend de la vérité visée.
- **(U2) Stratification des régimes** : la classe des solveurs admissibles est déterminée par le régime de clôture.

Une formulation cible (à développer) :

- définir la classe des “extensions admissibles” `R ↦ R*` qui ferment `T`,
- définir une notion de “raffinement”/“contient l’information” entre extensions,
- prouver que `extendQuot(R, σ)` est minimal parmi les fermetures construites à partir d’un médiateur fin,
  et que la non-descente est nécessaire dès qu’il y a diagonale.

---

## 6) Résumé (en une ligne)

Le phénomène n’est pas “une astuce” : c’est une théorie des **passages forcés** où la diagonalisation joue le rôle
de principe générateur de structure, et où l’induction est une dérivation témoinée de changements de référentiels.

