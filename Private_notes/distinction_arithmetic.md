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

---

## 11) Généralisation à `n` interfaces (multi-interface)

Soit une famille finie d’interfaces (partitions) `(E_i)_{i∈I}` sur `X` (où `I` est un ensemble fini d’indices).

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
