# Arithmétique de clôture par distinctions (treillis-based)

Idée : remplacer le comptage d’unités (`ℕ`) par un calcul sur des **distinctions** (paires d’états), puis appliquer un
cardinal `#` seulement à la fin.

Déplacement arithmétique :

```text
Peano cardinalise des collections.
L’arithmétique de clôture conserve d’abord l’incidence des pertes de distinctions, puis cardinalise.
```

Par **incidence**, on entend la position relative des sous-ensembles de pertes dans `R_σ` :
leur recouvrement, leur disjonction, ou leur alignement.

Point central :

```text
la clôture conjointe dépend de L_A ∩ L_B, pas seulement de #L_A et #L_B.
```

Deux slogans (dualité pertes / accessibilités) :

```text
perte conjointe        = intersection des pertes marginales
accessibilité conjointe = union des accessibilités marginales
```

Noyau formel :

```text
R_σ      := distinctions requises
L_A      := pertes requises sous A
L_B      := pertes requises sous B
ρ_σ(A,B) := #(L_A ∩ L_B)

Alors :

a_{A∧B} = r_σ - ρ_σ(A,B)

La clôture conjointe équivaut à :

ρ_σ(A,B) = 0
```

---

## 0) Signature abstraite (sortes, opérations, invariants)

Le document définit une **algèbre dérivée** : les objets de calcul sont des partitions et des sous-ensembles de
distinctions, et les nombres n’interviennent qu’après transport du calcul dans l’espace des pertes.

### Définition canonique (structure multi-sortée)

Pour `X` fini et `σ : X → S`, définir l’algèbre de clôture par distinctions (relative à `σ`) comme la structure :

```text
𝔠_σ(X)
:=
(
  Part(X), EqConf(X), 𝒫(R_σ), ℕ ;
  ≤, ∧, ∨ ; ⊆, ∩, ∪, \, # ;
  C, L_σ, A_σ, ρ_σ
)
```

où :

```text
C(E)      = C_E
L_σ(E)    = R_σ ∩ C_E
A_σ(E)    = R_σ \ L_σ(E)

ρ_σ(E₁,…,Eₙ)
  := #(⋂_{i=1}^n L_σ(E_i))

ρ_σ(A,B)
  := ρ_σ(E_A, E_B)
```

Remarques de typage (compléments).

```text
D_E      := ΔX \ C_E
A_σ(E)   := R_σ \ L_σ(E)
```

La clôture conjointe (multi-interface) se décide par :

```text
ρ_σ(E₁,…,Eₙ) = 0  ⇔  (∧_{i=1}^n E_i) ≤ E_σ.
```

### Sortes (types d’objets)

```text
X         : ensemble fini d’états
Part(X)   : treillis des partitions (relations d’équivalence) sur X
ΔX        : espace des distinctions {x,x'} avec x ≠ x'
σ : X → S : signature (cible dynamique)
R_σ ⊆ ΔX  : distinctions requises par σ
EqConf(X) : { C_E ⊆ ΔX | E ∈ Part(X) } (confusions admissibles)
```

### Opérations (côté partitions et distinctions)

Sur `Part(X)` :

```text
E ≤ F     : ordre “plus fin que”
E ∧ F     : meet (rencontre) = intersection de relations
E ∨ F     : join (jonction) = fermeture d’équivalence de l’union engendrée
```

Transport vers les distinctions :

```text
C_E ⊆ ΔX  : confusions induites par E
D_E       : distinctions conservées (= ΔX \ C_E)
```

Relativement à `σ` :

```text
L_σ(E) ⊆ R_σ : pertes requises (R_σ ∩ C_E)
A_σ(E) ⊆ R_σ : accessibilités requises (R_σ \ L_σ(E))
```

Projection numérique :

```text
#        : cardinal (sur ensembles finis)
ρ_σ(A,B) : #(L_σ(E_A) ∩ L_σ(E_B))
```

### Lois (schéma minimal)

```text
L_σ(E_A ∧ E_B) = L_σ(E_A) ∩ L_σ(E_B)
A_σ(E_A ∧ E_B) = A_σ(E_A) ∪ A_σ(E_B)

ρ_σ(A,B) = 0  ⇔  clôture conjointe de σ par A∧B
```

## 1) Espace des distinctions `ΔX`

Soit `X` un ensemble fini d’états.

```text
ΔX := {{x, x'} | x ≠ x'}
```

On travaille dans `𝒫(ΔX)` (sous-ensembles de distinctions), puis on applique :

```text
# : 𝒫(ΔX) → ℕ
```

---

## 2) Partitions / interfaces comme confusions

Une partition `E` sur `X` (relation d’équivalence) confond certaines paires :

```text
C_E := {{x, x'} ∈ ΔX | x E x'}
D_E := ΔX \ C_E
```

- `C_E` : distinctions confondues par `E`
- `D_E` : distinctions conservées par `E`

---

## 3) Signature future : distinctions requises

Pour une signature future (profil dynamique) :

```text
σ : X → S
```

la partition dynamique minimale est :

```text
E_σ := Ker(σ)
```

Les distinctions requises (celles que `σ` sépare) :

```text
R_σ := D_{E_σ}
     = {{x, x'} ∈ ΔX | σ(x) ≠ σ(x')}
```

et le total pertinent :

```text
r_σ := #R_σ
```

---

## 4) Pertes et accessibilité

Perte sous une interface/partition `E` :

```text
L_σ(E) := R_σ ∩ C_E
ℓ_σ(E) := #L_σ(E)
```

Distinctions requises accessibles sous `E` :

```text
A_σ(E) := R_σ \ L_σ(E)
a_σ(E) := #A_σ(E) = r_σ - ℓ_σ(E)
```

Forme canonique :

```text
accessible = requis - perdu
```

avec un “perdu” qui est un **sous-ensemble** de `R_σ` (incidence conservée).

---

## 5) Théorème central (vue conjointe A∧B)

Clarification de vocabulaire : la **vue conjointe** correspond au *meet* (rencontre) des partitions, pas au *join* (jonction).

- vue conjointe `A∧B` (rencontre / meet) :

```text
E_{A∧B} := E_A ∧ E_B := E_A ∩ E_B
```

- jonction `A∨B` (join) : fermeture transitive de l’union (utile ailleurs, pas ici).

Notations :

```text
L_A     := L_σ(E_A)
L_B     := L_σ(E_B)
L_{A∧B} := L_σ(E_{A∧B})
```

Alors :

```text
C_{A∧B} = C_A ∩ C_B
```

et donc :

```text
L_{A∧B} = L_A ∩ L_B
```

Thèse centrale :

```text
la vue conjointe A∧B perd exactement l’intersection des pertes marginales.
```

Proposition.

```text
Pour toute signature σ et toutes partitions E_A, E_B :

L_σ(E_A ∧ E_B) = L_σ(E_A) ∩ L_σ(E_B).
```

Preuve.

```text
E_A ∧ E_B = E_A ∩ E_B.
Donc une paire est confondue par E_A ∧ E_B exactement quand elle est confondue par E_A et par E_B,
c’est-à-dire : C_{A∧B} = C_A ∩ C_B.
En intersectant avec R_σ, on obtient :

L_σ(E_A ∧ E_B) = R_σ ∩ C_{A∧B} = (R_σ ∩ C_A) ∩ (R_σ ∩ C_B) = L_σ(E_A) ∩ L_σ(E_B).
```

---

## 6) Critère de clôture (encadré)

Clôture prédictive par `E` :

```text
E ⊆ E_σ
⇔ L_σ(E) = ∅
⇔ A_σ(E) = R_σ
⇔ a_σ(E) = r_σ
```

Clôture conjointe :

```text
L_σ(E_{A∧B}) = ∅
⇔ L_A ∩ L_B = ∅
⇔ ρ_σ(A,B) = 0
⇔ a_{A∧B} = r_σ
```

---

## 7) XOR (exemple)

Convention : écrire `00|01` pour la paire `{00,01}` (non ordonnée).

Pour `σ(x)=xor(x)` :

```text
R_σ = {00|01, 00|10, 01|11, 10|11}
#R_σ = 4
```

Pour `A` (1er bit) :

```text
L_A = {00|01, 10|11}
#L_A = 2
a_A = 4 - 2 = 2
```

Pour `B` (2e bit) :

```text
L_B = {00|10, 01|11}
#L_B = 2
a_B = 4 - 2 = 2
```

Pour la vue conjointe `A∧B` :

```text
L_{A∧B} = L_A ∩ L_B = ∅
#L_{A∧B} = 0
a_{A∧B} = 4 - 0 = 4
```

---

## 7bis) Exemple séparateur (cas explicite avec ρ=1)

Le cas XOR donne un exemple canonique où `ρ_σ(A,B)=0`. Un second exemple minimal montre un **résidu strict**.

Toujours avec :

```text
X = {00,01,10,11}
σ(x) = xor(x)
R_σ = {00|01, 00|10, 01|11, 10|11}
```

Prendre :

```text
E_A = {{00,01},{10,11}}
```

donc :

```text
L_A = {00|01, 10|11}.
```

Prendre :

```text
E_B = {{00,01,10},{11}}.
```

Alors :

```text
L_B = {00|01, 00|10}.
```

Donc :

```text
L_A ∩ L_B = {00|01}
ρ_σ(A,B) = 1.
```

Lecture : les pertes marginales ont une intersection non vide, donc la conjonction ne ferme pas totalement `σ`.

---

## 8) Contre-exemple (cardinalités marginales identiques, diagnostics différents)

Deux configurations peuvent avoir les mêmes cardinaux peaniens locaux
`r_σ`, `#L_A`, `#L_B`, tout en ayant des valeurs différentes de `#(L_A ∩ L_B)`.

La donnée :

```text
#L_A = 2
#L_B = 2
```

ne fixe pas :

```text
#(L_A ∩ L_B)
```

Trois cas typiques (même cardinalité marginale, diagnostics différents) :

```text
cas 1 : #(L_A ∩ L_B) = 0  → clôture conjointe complète
cas 2 : #(L_A ∩ L_B) = 1  → perte résiduelle
cas 3 : #(L_A ∩ L_B) = 2  → pertes alignées
```

Donc la donnée pertinente pour le joint est :

```text
#(L_A ∩ L_B)
```

et pas seulement `#L_A` et `#L_B`.

Nommer l’invariant critique :

```text
ρ_σ(A,B) := #(L_A ∩ L_B)
```

Lecture :

```text
ρ_σ(A,B) = perte résiduelle de la vue conjointe A∧B.
```

Alors :

```text
a_{A∧B} = r_σ - ρ_σ(A,B).
```

Option (gain de conjonction).

```text
g_σ(A,B) := min(ℓ_σ(E_A), ℓ_σ(E_B)) - ρ_σ(A,B).
```

Dans XOR : `ℓ_A=2`, `ℓ_B=2`, `ρ_σ(A,B)=0`, donc `g_σ(A,B)=2`.

---

## 9) Résumé du mécanisme

```text
R_σ       = distinctions requises
L_A       = requises perdues par A
L_B       = requises perdues par B
L_{A∧B}   = requises perdues par la vue conjointe
ρ_σ(A,B)  = #(L_A ∩ L_B) (perte résiduelle conjointe)
```

Alors :

```text
L_{A∧B} = L_A ∩ L_B
```

et la clôture conjointe se lit par :

```text
L_A ∩ L_B = ∅
⇔ ρ_σ(A,B) = 0
```

---

## 10) Notes techniques (pour rester dans `Part(X)`)

Cette écriture “par distinctions” est un calcul utile, avec deux précisions formelles :

1) Une partition `E` n’est pas un sous-ensemble arbitraire de `ΔX`.  
   La forme `C_E ⊆ ΔX` doit provenir d’une **relation d’équivalence** (donc d’un élément de `Part(X)`).

2) Pour la jonction `E_A ∨ E_B`, la description “`E_A ∪ E_B`” se lit comme
   “fermeture transitive / composantes connexes” de la relation engendrée,
   afin de rester une relation d’équivalence.

Remarque : si `ΔX` est défini en excluant la diagonale `{(x,x)}`, alors les opérations de “fermeture en relation
d’équivalence” doivent être comprises comme portant implicitement sur `X×X` (avec la diagonale), puis restreintes
à `ΔX`. C’est ce qui fait fonctionner la lecture “composantes connexes / EqClosure”.

---

## 11) Généralisation à `n` interfaces (multi-interface)

Soit une famille finie **non vide** d’interfaces (partitions) `(E_i)_{i∈I}` sur `X`
(où `I` est un ensemble fini d’indices, `I ≠ ∅`).

### Vue conjointe multi-interface

La vue conjointe correspond au *meet* sur toute la famille :

```text
E_{∧I} := ∧_{i∈I} E_i
```

Dans `Part(X)`, ce *meet* s’écrit comme intersection de relations d’équivalence :

```text
E_{∧I} = ⋂_{i∈I} E_i
```

### Formule centrale (pouvoir d’incidence)

Au niveau des distinctions confondues :

```text
C_{∧I} = ⋂_{i∈I} C_i
```

Donc, pour une signature `σ` fixée :

```text
L_σ(E_{∧I})
= R_σ ∩ C_{∧I}
= R_σ ∩ ⋂_{i∈I} C_i
= ⋂_{i∈I} (R_σ ∩ C_i)
= ⋂_{i∈I} L_σ(E_i).
```

Autrement dit :

```text
L_{∧I} = ⋂_{i∈I} L_i.
```

Cette égalité est la généralisation directe de `L_{A∧B} = L_A ∩ L_B`.

### Invariant résiduel multi-interface

Définir :

```text
ρ_σ(A_1,…,A_n) := #(⋂_{i=1}^n L_{A_i})
```

Lecture :

```text
ρ_σ(A_1,…,A_n) = perte résiduelle conjointe (après conjonction de n interfaces).
```

Alors :

```text
a_{∧i A_i} = r_σ - ρ_σ(A_1,…,A_n).
```

### Critère de clôture multi-interface

La clôture conjointe de la famille vaut :

```text
ρ_σ(A_1,…,A_n) = 0
```

équivalent à :

```text
⋂_{i=1}^n L_{A_i} = ∅
```

et à :

```text
a_{∧i A_i} = r_σ.
```

Convention (cas vide, si besoin). Si l’on autorise `I = ∅`, on fixe :

```text
⋂_{i∈∅} L_i := R_σ
```

ce qui correspond à une “vue conjointe vide” sans information additionnelle, donc à une perte totale
des distinctions requises.

---

## 12) Propriétés algébriques (morphismes de treillis)

### Morphisme “confusions” : `E ↦ C_E`

Définir :

```text
C : Part(X) → 𝒫(ΔX)
E ↦ C_E
```

où :

```text
C_E := {{x, x'} ∈ ΔX | x E x'}.
```

**Monotonie (morphisme d’ordre).** Pour l’ordre “plus fin que” :

```text
E ≤ F  ⇒  C_E ⊆ C_F.
```

Lecture : si `E` est plus fine que `F` (elle identifie moins), alors l’ensemble des paires confondues par `E`
est inclus dans celui confondu par `F`.

**Préservation des rencontres.** Pour toute famille finie `(E_i)` :

```text
C_{∧i E_i} = ⋂i C_{E_i}.
```

Formulation précise : `E ↦ C_E` est un morphisme d’ordre qui préserve les rencontres finies
(un homomorphisme de *meet-semilattice* vers `(𝒫(ΔX), ⊆, ∩)`).

Pour la jonction, une écriture pleinement propre sépare deux niveaux :

1) `C_E ⊆ ΔX` encode des **paires non ordonnées** `{x,x'}` (distinctions confondues).
2) Une fermeture d’équivalence vit naturellement sur des **paires ordonnées** `(x,x') ∈ X×X`.

On introduit donc :

```text
Δ_X^diag := {(x,x) | x ∈ X}

Rel(C) := Δ_X^diag ∪ {(x,x'), (x',x) | {x,x'} ∈ C}
```

Alors la jonction des partitions s’écrit :

```text
E_A ∨ E_B = EqClosure(Rel(C_{E_A}) ∪ Rel(C_{E_B}))
```

où `EqClosure` désigne la fermeture réflexive-symétrique-transitive (équivalemment : les composantes connexes
du graphe engendré).

Et, en revenant aux distinctions non ordonnées :

```text
C_{E_A ∨ E_B}
= {{x,x'} ∈ ΔX | (x,x') ∈ EqClosure(Rel(C_{E_A}) ∪ Rel(C_{E_B}))}.
```

### Morphisme “pertes relatives” : `L_σ`

Pour une signature fixée `σ`, définir :

```text
L_σ : Part(X) → 𝒫(R_σ)
E ↦ L_σ(E) := R_σ ∩ C_E.
```

Alors `L_σ` est aussi monotone et préserve les rencontres :

```text
E ≤ F  ⇒  L_σ(E) ⊆ L_σ(F)
```

et :

```text
L_σ(∧i E_i) = ⋂i L_σ(E_i).
```

Ces deux propriétés expliquent pourquoi l’algèbre de clôture multi-interface se réduit à une arithmétique
d’intersections avant cardinalisation.

### Formule duale (accessibilités)

Poser :

```text
Acc_i := A_σ(E_i) = R_σ \ L_σ(E_i).
```

Alors, par De Morgan :

```text
A_σ(∧i E_i)
= R_σ \ ⋂i L_σ(E_i)
= ⋃i (R_σ \ L_σ(E_i))
= ⋃i A_σ(E_i).
```

Donc :

```text
accessibilité conjointe = union des accessibilités marginales
perte conjointe         = intersection des pertes marginales
```

---

## 12bis) Image des partitions dans `𝒫(ΔX)` (objets admissibles)

Une partition `E ∈ Part(X)` induit un ensemble de confusions `C_E ⊆ ΔX`. L’inverse n’est pas vrai : un sous-ensemble
arbitraire de `ΔX` ne correspond pas forcément à une relation d’équivalence.

Définir l’ensemble des confusions admissibles :

```text
EqConf(X) := { C_E ⊆ ΔX | E ∈ Part(X) }.
```

Alors :

```text
C : Part(X) → EqConf(X)
E ↦ C_E
```

est bijectif (chaque partition correspond à exactement un ensemble de paires confondues).

De plus, c’est un isomorphisme d’ensembles ordonnés :

```text
E ≤ F   ⇔   C_E ⊆ C_F.
```

Au niveau des opérations, la rencontre est transportée sans perte :

```text
C_{E ∧ F} = C_E ∩ C_F.
```

On peut donc équiper `EqConf(X)` d’un *meet* transporté :

```text
U ∧_Δ V := U ∩ V.
```

Pour la jonction, l’opération transportée doit passer par une fermeture d’équivalence au niveau relationnel
(`X×X`), puis être restreinte aux distinctions `ΔX` (cf. section 12 pour `Rel(·)` et `EqClosure`). On peut la noter :

```text
U ∨_Δ V
:=
C_{ EqClosure(Rel(U) ∪ Rel(V)) }.
```

Avec ces opérations transportées, on peut lire :

```text
Part(X) ≅ EqConf(X)
```

comme treillis (via transport).

---

## 13) Théorèmes caractéristiques (propriétés d’invariance et de comparaison)

### 13.1) Invariance par renommage (isomorphisme d’états)

Soient `X` et `X'` des ensembles finis et `φ : X ≃ X'` une bijection.
En transportant :

```text
σ' := σ ∘ φ⁻¹
E' := transport(E, φ)   (relation : x' E' y' ⇔ φ⁻¹(x') E φ⁻¹(y'))
```

on a un transport canonique des distinctions et des pertes :

```text
R_σ  ↔ R_{σ'}
L_σ(E) ↔ L_{σ'}(E')
```

Donc :

```text
ρ_σ(E_A, E_B) = ρ_{σ'}(E'_A, E'_B)
```

Lecture : `ρ` dépend uniquement de la **configuration relative** des partitions, pas des noms des états.

### 13.2) Cardinalisation immédiate vs différée (perte d’information)

La donnée marginale :

```text
#L_A, #L_B
```

ne détermine pas la quantité conjointe :

```text
#(L_A ∩ L_B).
```

Donc la cardinalisation immédiate (type “Peano”) écrase l’incidence. La cardinalisation différée conserve :

```text
L_A ⊂ R_σ,  L_B ⊂ R_σ,  L_A ∩ L_B.
```

### 13.3) Classification minimale (clôture vs résidu)

Le diagnostic de clôture conjointe se réduit à :

```text
ρ_σ(A,B) = 0   (clôture)
ρ_σ(A,B) > 0   (résidu strict)
```

Et le contre-exemple de la section 8 montre que deux systèmes peuvent partager les mêmes
valeurs marginales tout en tombant de part et d’autre de ce seuil.

---

## 14) Calcul effectif (complexité)

Le calcul peut être implémenté directement sur des bitsets indexant `R_σ ⊆ ΔX`.

Pour une paire `(x,x')`, indexer une coordonnée `p ∈ {0,…,|ΔX|-1}`.
Alors :

```text
bitset(R_σ)         : masque des distinctions requises
bitset(C_E)         : masque des distinctions confondues par E
bitset(L_σ(E))      = bitset(R_σ) AND bitset(C_E)
bitset(L_res)       = AND_i bitset(L_σ(E_i))
ρ_σ(A_1,…,A_n)       = popcount(bitset(L_res))
```

La complexité est linéaire en taille de bitset :

```text
O(|ΔX| / w)
```

où `w` est la taille de mot machine (ex. 64), avec une constante faible (`AND` + `popcount`).
