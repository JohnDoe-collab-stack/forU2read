# Bridge holographie (QECC discret) → clôture par interface (décidabilité)

Ce document instancie le plan “dictionnaire → logique d’accès” dans un cadre **QECC discret** (code holographique jouet),
afin de pouvoir **démontrer** (et pas seulement suggérer) :

1) no‑go marginal (une région du bord ne décide pas une vérité bulk `σ`) ;
2) clôture conjointe (une composition de régions décide `σ`) ;
3) minimalité (capacité minimale d’un médiateur fini nécessaire/suffisante).

Le but n’est **pas** de postuler “RT/QES = médiateur”, mais de fournir un **théorème de traduction** dans un modèle discret
où tout est calculable.

Référence conceptuelle interne (cadre général) :
- `Private_notes/distinction_arithmetic_refined.md`
- `Private_notes/DICTIONARY_CLOSURE_LAYER.md`

---

## A. Cadre fixé (choix de modèle)

On travaille dans un modèle QECC discret suffisamment simple pour :
- exhiber explicitement des témoins “même marginale / `σ` différent” ;
- exhiber explicitement une procédure de décision/reconstruction ;
- prouver une borne inférieure de capacité (minimalité).

Choix recommandé : **stabilizer access toy‑model / GHZ encoding** (modèle d’accès) au lieu d’un réseau de tenseurs géométriquement lourd.
Raison : la minimalité se prouve proprement par arguments de dimension/indistinguabilité, et les témoins sont explicites.

Réserve terminologique :
le code GHZ/répétition est utilisé ici comme **toy model d’accès/reconstruction** (clôture par interface) ;
ce n’est pas, dans ce document, une prétention à “corriger des erreurs arbitraires” au sens général QECC.

---

## B. Traduction : interfaces et vérité visée

### B1. Espaces

- Espace logique : `H_L`.
- Espace physique (bord) : `H_phys = ⊗_{i∈Phys} H_i`.
- Code subspace : `C ⊂ H_phys` et isométrie d’encodage `V : H_L → H_phys` (image = `C`).

### B2. Interface

Une interface `A` est un sous‑système physique `A ⊂ Phys`.  
On note `ρ_A` la réduction de `ρ` sur `A` (trace partielle sur `Phys\\A`).

### B3. Vérité visée

Une vérité bulk `σ` est un observable logique (ou une propriété logique) sur `H_L`.
Deux choix possibles (on en fixe un seul dans l’exemple) :

- **(Obs)** un opérateur logique `O_L` (Hermitien, ou projecteur) ; ou
- **(Bit)** un bit logique `σ(ψ) ∈ {0,1}` défini par mesure d’un projecteur logique.

On prendra **(Bit)** dans l’exemple : `σ` est la valeur d’un projecteur logique `Π_L` sur `H_L`.

---

## C. Définition unique de “clôture sur A” (décidabilité par interface)

On fixe une définition **opérationnelle** :

> `σ` est décidable depuis `A` sur le code `C` s’il existe une mesure (POVM) `M_A` sur `A` telle que,
> pour tout état logique `|ψ⟩` dans un **domaine de décision** `D_σ ⊂ H_L`, le résultat de `M_A` détermine `σ(|ψ⟩)`
> (sans erreur) sur l’état encodé `V|ψ⟩`.

Équivalent pratique (dans les exemples) :

> Il existe un projecteur (ou observable) `Π_A` supporté sur `A` tel que  
> `Π_A V|ψ⟩ = V Π_L |ψ⟩` pour tout `|ψ⟩`.  
> (c’est une reconstruction exacte de `σ` sur `A`.)

On note ce prédicat :

```text
Close(A, σ)  :⇔  σ est décidable depuis A sur C.
```

---

## D. Deux régimes + théorèmes à prouver (dans le modèle discret fixé)

On introduit une abréviation :

```text
Fail(I, σ) :⇔ ¬ Close(I, σ).
```

et, pour distinguer explicitement les deux schémas :

```text
Residue(A∪B, σ) :⇔ Fail(A∪B, σ).
```

L’intérêt de `Residue` est uniquement sémantique : “la composition existe, mais ne ferme pas encore”.

Traduction de notation (composition) :
dans la théorie abstraite, la composition d’interfaces est notée `A ∧ B` ;
dans ce bridge par sous‑systèmes, elle est instanciée par l’accès conjoint `A ∪ B`.

### Théorème 1 — No‑go marginal (témoins)

Pour une région `A`, on prouve :

```text
¬ Close(A, σ)
```

en exhibant explicitement deux états logiques `|ψ0⟩, |ψ1⟩` tels que :

```text
ρ_A(V|ψ0⟩⟨ψ0|V†) = ρ_A(V|ψ1⟩⟨ψ1|V†)
mais
σ(|ψ0⟩) ≠ σ(|ψ1⟩).
```

Lecture : “même visible sur `A`, vérité différente”.

### Package direct — la composition ferme

Schéma :

```text
Fail(A, σ)
Fail(B, σ)
Close(A∪B, σ)
```

Le dernier point se prouve en donnant explicitement une procédure (un `Π_{A∪B}` ou une POVM) qui décide `σ`.

### Package médié — la composition localise un résidu réparable

Schéma :

```text
Fail(A, σ)
Fail(B, σ)
Residue(A∪B, σ)
Close(A∪B∪M_n, σ)
∀ m < n, Fail(A∪B∪M_m, σ)
```

Le point dur est la borne inférieure (la clause `∀ m<n`).

### Théorème — Minimalité du médiateur (capacité)

On formalise un médiateur `M` comme un supplément d’interface de capacité finie :

- soit un registre classique/quantique de dimension `d(M)`,
- soit un sous‑système additionnel autorisé dans l’accès.

On vise un énoncé de type :

```text
∃ n,  Close(A ∪ M_n, σ)  ∧  ∀ m < n,  ¬ Close(A ∪ M_m, σ)
```

où `M_n` désigne un médiateur de capacité `n` (ou dimension `2^n` selon convention).

Le point dur est la borne inférieure : produire un **argument d’indistinguabilité** qui montre
qu’avec capacité `< n`, les deux témoins du no‑go restent confondus.

---

## E. Exemple worked‑out : code GHZ / répétition à 3 qubits

Cet exemple fournit un témoin QECC fini de la couche de clôture :
la **phase logique** est invisible à toute marginale stricte, devient décidable sur l’interface composée,
et, dans une présentation médiée, requiert exactement **un qubit** de capacité additionnelle.

### E1. Code

Espace logique `H_L = span{|0⟩,|1⟩}` et encodage :

```text
V|0⟩ = |000⟩
V|1⟩ = |111⟩
```

### E2. Vérité visée `σ` (phase logique)

On prend pour observable logique la phase (états propres de `X_L`) :

```text
|+_L⟩ = (|0_L⟩ + |1_L⟩)/√2
|-_L⟩ = (|0_L⟩ - |1_L⟩)/√2
```

Encodés :

```text
|+_C⟩ = (|000⟩ + |111⟩)/√2
|-_C⟩ = (|000⟩ - |111⟩)/√2
```

La vérité visée `σ` est le bit “signe de phase” :

```text
σ(|+_L⟩)=0,   σ(|-_L⟩)=1
```

et elle est définie sur le **domaine de décision** :

```text
D_σ = {|+_L⟩, |-_L⟩}.
```

et elle est décidable sur l’interface complète `{1,2,3}` via la mesure de :

```text
X_1 X_2 X_3
```

car :

```text
X_1 X_2 X_3 |+_C⟩ = + |+_C⟩
X_1 X_2 X_3 |-_C⟩ = - |-_C⟩
```

### E3. No‑go marginal strict

Pour tout sous‑système strict `S ⊊ {1,2,3}` :

```text
ρ_S(|+_C⟩⟨+_C|) = ρ_S(|-_C⟩⟨-_C|)
```

donc toute interface stricte échoue à décider la phase logique :

```text
Fail(S, σ)   pour tout S strict.
```

Preuve courte (traces partielles) :

```text
|±_C⟩⟨±_C|
= 1/2(
  |000⟩⟨000|
  + |111⟩⟨111|
  ± |000⟩⟨111|
  ± |111⟩⟨000|
).
```

Dès qu’on trace au moins un qubit (i.e. `S` strict), les termes croisés `|000⟩⟨111|` et `|111⟩⟨000|`
disparaissent, car ils portent une cohérence sur le qubit tracé. On obtient donc :

```text
ρ_S(|+_C⟩⟨+_C|) = ρ_S(|-_C⟩⟨-_C|)
= 1/2(
  |0…0⟩⟨0…0|
  + |1…1⟩⟨1…1|
).
```

La phase logique est donc invisible sur toute marginale stricte.

### E4. Lecture “package direct” sur le même exemple

Prendre :

```text
A = {1,2}
B = {3}
```

Alors :

```text
Fail(A, σ)
Fail(B, σ)
Close(A∪B, σ)     (car A∪B = {1,2,3})
```

### E5. Lecture “package médié” sur le même exemple

Prendre :

```text
A = {1}
B = {2}
M = {3}
```

Alors :

```text
Fail(A, σ)
Fail(B, σ)
Residue(A∪B, σ)     (car A∪B = {1,2} échoue encore)
Close(A∪B∪M, σ)     (car {1,2,3} décide σ)
```

Minimalité : `M` doit porter au moins un qubit de capacité.
Avec la convention :

```text
capacité = log₂ dim(M),
```

une capacité `< 1 qubit` signifie `dim(M) < 2`, donc un médiateur trivial (un seul état distinguable).
Dans ce cas, l’interface effective reste `{1,2}` et les réductions de `|+_C⟩` et `|-_C⟩` y restent identiques ;
la décision est impossible. Donc :

```text
n = 1 qubit
```

### E6. Phrase de synthèse (à réutiliser)

```text
Le code GHZ/répétition fournit un témoin QECC fini de la couche de clôture :
la phase logique échoue sur toute marginale stricte, devient décidable sur l’interface composée,
et, dans la présentation médiée, requiert exactement un qubit de capacité additionnelle.
```

---

## F. Sorties attendues (pour être “montrable”)

1) Un document `Bridge` (celui‑ci) qui fixe définitions + théorèmes.
2) Un document `Example` qui contient l’exemple complet (témoins + reconstruction + minimalité).
3) (Option) Un mini proofpack empirique sur le même schéma (pour illustrer la différence “universel vs instancié”),
   mais **la preuve** ici est mathématique et fermée.
