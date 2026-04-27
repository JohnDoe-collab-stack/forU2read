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
- `ΔX` : espace des distinctions non ordonnées `{x,x'}` avec `x ≠ x'`.
- `R_σ := {{x,x'} ∈ ΔX | σ(x) ≠ σ(x')}` : distinctions requises.

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

Pour un ensemble `I` de vues déjà conjointes, définir la perte résiduelle :

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

### 2.4 Diagnostic d’échec structuré (3 causes)

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

Formulation structurale : si l’agrégateur est une t-norm `T` (ex. produit sur `[0,1]`), on veut :

```text
T(a,b) ≤ a
T(a,b) ≤ b
```

ce qui garantit que chaque vue ajoutée contracte bien la confusion résiduelle.

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

Séparation propre des objets :

```text
R_σ = distinctions requises
C_i = confusions induites par la vue i
L_i = R_σ ∩ C_i
```

Une forme probabiliste propre factorise donc :

```text
q_θ(p)   ≈ P[p ∈ R_σ]
c_θ(i,p) ≈ P[p ∈ C_i]
```

où `p ∈ ΔX` représente une paire (distinction) `{x,x'}`.

Pour un ensemble de vues `I`, un score de perte résiduelle pairwise peut être agrégé par une t-norm (ex. produit) :

```text
c_res,θ(I,p) := ∏_{i∈I} c_θ(i,p)
l_res,θ(I,p) := q_θ(p) · c_res,θ(I,p)
```

Une estimation de la perte résiduelle globale :

```text
ρ_θ(I) := Σ_{p∈ΔX} l_res,θ(I,p)
```

La politique choisit alors une requête `j` qui minimise :

```text
ρ_θ(I ∪ {j})
```

ou maximise la réduction :

```text
ρ_θ(I) - ρ_θ(I ∪ {j}).
```

Avec la factorisation `q_θ · ∏ c_θ`, la réduction estimée s’écrit aussi :

```text
Δ_θ(j | I)
= ρ_θ(I) - ρ_θ(I ∪ {j})
= Σ_{p∈ΔX} q_θ(p) · ∏_{i∈I} c_θ(i,p) · (1 - c_θ(j,p)).
```

Lecture :

```text
la requête j vaut par les distinctions requises encore confondues qu’elle sépare.
```

Cette écriture est l’analogue neurale direct de :

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

Une propriété attendue quand la politique ajoute des vues successivement (greedy ou quasi-greedy) :

```text
ρ_θ(I_0) ≥ ρ_θ(I_1) ≥ … ≥ ρ_θ(I_T)
```

où `I_t` est l’ensemble des vues sélectionnées après `t` requêtes.

On peut aussi instrumenter le rendement marginal :

```text
η_t := ρ_θ(I_t) - ρ_θ(I_{t+1})
```

Lecture :

```text
η_t mesure la quantité de perte résiduelle supprimée par la requête t.
```

### 5.4 Contrat expérimental (audit algébrisé)

Un protocole de type `law_v3b` peut être relu comme un test de causalité structurelle :
la performance suit la contraction de `ρ`.

Un contrat simple à vérifier (qualitatif, puis quantitatif) :

```text
ρ_θ(base)                          élevé
ρ_θ(base ∧ query utile)            fortement réduit (idéalement ≈ 0)
ρ_θ(base ∧ query swap)             élevé
ρ_θ(base ∧ query ablatée)          élevé
Δ_θ(query utile | base)            élevé
Δ_θ(query swap | base)             faible
```

Ce contrat exprime que le gain vient de la réduction de perte résiduelle par conjonction de vues,
et que l’intervention (swap/ablation) détruit précisément ce mécanisme.

---

## 6) Résumé (ce qui est réellement nouveau côté design)

Le gain n’est pas “un score de plus”.

Le gain est un changement de variable d’analyse et d’optimisation :

```text
optimiser la clôture = optimiser l’incidence des pertes de distinctions requises
```

Le solveur devient une machine qui :

1. estime les distinctions requises `R_σ`,
2. estime les confusions `C_i` propres aux vues disponibles,
3. maintient une perte résiduelle `L_res(I)`,
4. choisit la vue qui maximise `Δ_j(I)`,
5. ferme la cible lorsque `ρ_σ(I)` atteint `0`.

Formulation de conclusion :

```text
Une architecture de médiation est algébriquement correcte lorsque ses requêtes
maximisent la transformation des confusions résiduelles en distinctions accessibles.
```

Version compacte :

```text
La requête est un opérateur de clôture.
```
