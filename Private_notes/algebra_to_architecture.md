# De l’algèbre des distinctions au design d’architecture (implications directes)

Ce document explique comment l’algèbre de clôture par distinctions (calcul dans `𝒫(R_σ)` puis cardinalisation)
donne des **principes de design** pour une architecture de solveur à requêtes/médiation, et comment s’en servir
pour améliorer un protocole du type `law_v3b`.

---

## 0) Vocabulaire minimal (rappel)

- `X` : états présents (latents).
- `σ : X → S` : signature future (vérité cible / profil futur pertinent).
- `E` : une interface (partition sur `X`), avec :
  - `C_E` : confusions induites par l’interface,
  - `L_σ(E) := R_σ ∩ C_E` : pertes requises sous `E`.
- `R_σ := {(x,x') | σ(x) ≠ σ(x')}` : distinctions requises.

Vue conjointe (meet) :

```text
E_{∧I} := ∧_{i∈I} E_i
L_σ(E_{∧I}) = ⋂_{i∈I} L_σ(E_i)
```

Invariant résiduel :

```text
ρ_σ(A_1,…,A_n) := #(⋂_{i=1}^n L_{A_i})
```

Clôture conjointe :

```text
ρ_σ(A_1,…,A_n) = 0
```

---

## 1) Traduction “solveur” (une phrase)

Un solveur actif est une machine qui **choisit** une conjonction d’interfaces (par action/requête)
de façon à rendre l’intersection des pertes requises **aussi petite que possible**, idéalement nulle.

---

## 2) Ce que l’algèbre apporte au design (au-delà du benchmark)

### 2.1 Objectif explicite pour la politique de requête

Sans l’algèbre, la requête est souvent optimisée “indirectement” via la performance finale.

Avec l’algèbre, l’objectif structurel devient :

```text
choisir des interfaces dont ⋂ L_i est minimal
```

et le critère de réussite est :

```text
⋂ L_i = ∅   (donc ρ_σ = 0)
```

### 2.2 Multi-interfaces = union des accessibilités

La dualité :

```text
pertes conjointe        = intersection des pertes marginales
accessibilité conjointe = union des accessibilités marginales
```

donne un principe de composition :

> une nouvelle requête est utile lorsqu’elle apporte des accessibilités **non redondantes**
> (ses pertes se recouvrent peu avec les pertes déjà présentes).

### 2.3 Principe de design : utilité relative au résidu courant

Le critère “complémentarité” devient exact dès qu’on le formule relativement au résidu courant.

Pour un ensemble de vues déjà conjointe `I`, définir la perte résiduelle :

```text
L_res(I) := ⋂_{i∈I} L_i
```

Ajouter une vue `j` produit :

```text
L_res(I ∪ {j}) = L_res(I) ∩ L_j
```

Le gain exact de la requête `j` sur l’état courant `I` est :

```text
Δ_j(I) := #L_res(I) - #(L_res(I) ∩ L_j)
        = #(L_res(I) \ L_j)
        = #(L_res(I) ∩ A_j)
```

où :

```text
A_j := R_σ \ L_j
```

Lecture :

```text
Δ_j(I) = nombre de distinctions encore perdues que la vue j rend accessibles.
```

Règle de choix (greedy idéal) :

```text
choisir j qui maximise #(L_res(I) ∩ A_j)
```

ou, de façon équivalente :

```text
choisir j qui minimise #(L_res(I) ∩ L_j).
```

Phrase de design compacte :

```text
Une requête vaut par son intersection avec la perte résiduelle courante.
```

### 2.3 Diagnostic d’échec structuré (3 causes)

Quand un run échoue, l’algèbre force une classification de cause :

1) `R_σ` est mal représenté (la signature pertinente n’est pas correctement capturée).
2) Les pertes `L_σ(E)` sont mal apprises/estimées (l’interface effective n’est pas celle prévue).
3) La politique de conjonction choisit des interfaces dont l’intersection de pertes reste non nulle
   (mauvais choix de requêtes / vues, ou manque de vues disponibles).

Ce diagnostic est actionnable : il dicte quoi changer (représentation, interfaces disponibles, ou politique).

---

## 3) Comment “rendre ρ_σ optimisable” dans une architecture neurale

Dans un modèle, `L_σ(E)` n’est pas disponible explicitement comme ensemble de paires.
L’idée est donc de créer une **approximation opérationnelle** (une surrogate) qui conserve le bon sens :
“quelle part des distinctions requises reste indistinguable sous l’interface courante”.

### 3.1 Surrogate par paires (pairwise witness head)

Construire un head qui prend deux traces/états internes `h(x), h(x')` et prédit si la paire est
**requise** (σ différente) et si elle est **confondue** par l’interface.

Schéma :

- un encodeur d’état interne : `x ↦ h(x)`,
- un discriminateur de paires : `(h(x), h(x')) ↦ score`.

Puis apprendre :

- un signal “σ-différence” (distinction requise),
- un signal “interface-confusion” (distinction perdue sous une vue donnée).

Cette couche ne remplace pas la tâche ; elle sert à aligner la politique de requête sur l’objet `ρ_σ`.

### 3.2 Surrogate par familles de vues (intersection de pertes)

Pour une famille de vues requêtables `(E_i)`, on vise une approximation de :

```text
⋂_i L_i
```

Opérationnellement : on apprend des scores de “perte résiduelle” par vue, puis on impose une agrégation qui
mime l’intersection (par exemple via un AND logique différentiable / t-norm, ou via min-pooling sur logits).

Le point de design important : l’agrégateur doit refléter :

```text
plus on ajoute des vues, plus la perte résiduelle peut seulement diminuer
```

(monotonie vers le bas).

### 3.3 Politique de requête guidée par “réduction d’intersection”

La règle d’action devient :

> choisir la requête qui minimise la perte résiduelle estimée après conjonction.

Dans le cas multi-steps :

- étape 0 : interface de base,
- étape 1..T : requêtes successives,
- objectif : rendre la perte résiduelle estimée proche de 0.

### 3.4 Surrogate neurale : score de réduction de résidu

Une traduction directe du critère greedy consiste à apprendre des scores pairwise qui approximent :

- quelles paires sont **requises** par la signature (`R_σ`),
- quelles paires restent **perdues** sous chaque interface.

Une forme pratique (scores probabilistes) :

```text
q_θ(x,x')    ≈ P[(x,x') ∈ R_σ]
l_θ(i,x,x')  ≈ P[(x,x') ∈ L_i]
a_θ(i,x,x')  ≈ P[(x,x') ∈ A_i] ≈ 1 - l_θ(i,x,x')
```

Pour un ensemble de vues `I`, un score de perte résiduelle pairwise peut être agrégé par une t-norm (ex. produit) :

```text
l_res,θ(I,x,x') ≈ ∏_{i∈I} l_θ(i,x,x')
```

Une estimation de la perte résiduelle globale :

```text
ρ_θ(I) := Σ_{x,x'} q_θ(x,x') · l_res,θ(I,x,x')
```

La politique choisit alors une requête `j` qui minimise :

```text
ρ_θ(I ∪ {j})
```

ou maximise la réduction :

```text
ρ_θ(I) - ρ_θ(I ∪ {j}).
```

Cette écriture est l’analogue neurale de :

```text
Δ_j(I) = #(L_res(I) ∩ A_j).
```

---

## 4) Comment relier ça à `law_v3b` (lecture directe)

Une lecture “algebra-first” de `law_v3b` :

- l’interface visible-only correspond à une partition `E_base`,
- la requête choisit une extension (ou une vue) qui ajoute une interface `E_query`,
- la décision finale exploite la vue conjointe `E_base ∧ E_query`,
- les audits (barrières, baselines, ablation/swap, IID+OOD, seeds) vérifient que la réussite dépend bien
  de la conjonction de vues (et donc d’une réduction effective de pertes), pas d’un canal parasite.

Dans ce cadre, le “bon” comportement est exactement :

```text
ρ_σ(base, query) = 0
```

sur les distributions d’évaluation.

---

## 5) Ce que ça change concrètement dans l’architecture

### 5.1 Passage de “requête comme feature” à “requête comme opérateur de clôture”

Le design devient :

- **interface(s) explicitement typées** (famille de vues),
- **politique** explicitement orientée vers l’extinction de la perte résiduelle,
- **médiateur** vu comme mécanisme de sélection de vues (et non comme “source d’information”).

### 5.2 Extension naturelle : plusieurs vues, pas un seul bit

L’algèbre pousse vers :

- plusieurs interfaces requêtables,
- une politique qui construit une conjonction (sélection de sous-ensemble),
- des tests qui vérifient que l’intersection des pertes se contracte réellement à mesure que des vues sont ajoutées.

### 5.3 Outillage de vérification plus fin

En plus du “pass/fail” final, on peut instrumenter :

- une mesure de perte résiduelle estimée après chaque requête,
- la monotonicité (la perte résiduelle ne remonte pas quand on ajoute une vue),
- la non-redondance (des vues qui n’améliorent rien).

Ces mesures ne remplacent pas les audits ; elles rendent l’échec diagnostiquable plus vite.

---

## 6) Résumé (ce qui est réellement nouveau côté design)

Le gain n’est pas “un score de plus”.

Le gain est un changement de variable d’analyse et d’optimisation :

```text
optimiser la clôture = optimiser l’incidence des pertes de distinctions requises
```

Le solveur devient une machine qui :

- identifie une signature pertinente `σ`,
- choisit des interfaces dont les pertes se recouvrent le moins possible,
- ferme la cible lorsque l’intersection des pertes s’éteint.
