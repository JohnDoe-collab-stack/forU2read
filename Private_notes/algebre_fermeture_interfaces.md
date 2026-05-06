# Coalitions minimales d’accès — algèbre de fermeture par interfaces

Statut : document autonome de définition.

Objet : formaliser une algèbre générale de l’accès informationnel par interfaces, fondée sur les
distinctions requises, les pertes d’interface, l’incidence des pertes, le résidu commun, la fermeture,
l’irréductibilité et la médiation minimale.

## 1. Données primitives

On fixe :

```text
X       : ensemble fini d’états
σ : X → Y : cible, signature ou vérité à décider
J       : ensemble fini d’interfaces
```

Une interface `j ∈ J` est modélisée par une observation :

```text
obs_j : X → V_j
```

Deux états `x,y ∈ X` sont confondus par l’interface `j` lorsque :

```text
obs_j(x) = obs_j(y).
```

La cible `σ` distingue `x` et `y` lorsque :

```text
σ(x) ≠ σ(y).
```

La théorie ne commence pas par des scores. Elle commence par des distinctions.

## 2. Distinctions requises

L’espace des distinctions est :

```text
ΔX := {{x,y} | x,y ∈ X, x ≠ y}.
```

Les distinctions requises par la cible sont :

```text
R_σ := {{x,y} ∈ ΔX | σ(x) ≠ σ(y)}.
```

`R_σ` est le domaine pertinent de la décision. Une interface n’a pas besoin de séparer toutes les
distinctions de `ΔX`; elle doit séparer les distinctions nécessaires à `σ`.

Le total pertinent est :

```text
r_σ := #R_σ.
```

## 3. Pertes d’une interface

Pour une interface `j`, la perte relative à `σ` est :

```text
L_j := {{x,y} ∈ R_σ | obs_j(x) = obs_j(y)}.
```

Donc :

```text
L_j ⊆ R_σ.
```

Lecture :

```text
d ∈ L_j
```

signifie que la distinction requise `d` est invisible depuis l’interface `j`.

L’accessibilité de `j` est le complément relatif :

```text
Acc_j := R_σ \ L_j.
```

Donc :

```text
d ∈ Acc_j
```

signifie que l’interface `j` sépare la distinction requise `d`.

## 4. Vue conjointe

Pour une sous-famille d’interfaces `I ⊆ J`, la vue conjointe identifie deux états lorsque toutes les
interfaces de `I` les identifient :

```text
x ≡_I y
⇔
∀ j ∈ I, obs_j(x) = obs_j(y).
```

La perte conjointe de `I` est donc :

```text
Res(I) := {{x,y} ∈ R_σ | ∀ j ∈ I, obs_j(x) = obs_j(y)}.
```

En termes des pertes marginales :

```text
Res(I) = ⋂_{j∈I} L_j.
```

Convention pour la famille vide :

```text
Res(∅) := R_σ.
```

Cette convention signifie que sans interface aucune distinction requise n’est couverte.

Pour des interfaces de types hétérogènes, l’observation conjointe a un type produit dépendant :

```text
Joint_I : X → Π_{j∈I} V_j
Joint_I(x) := (obs_j(x))_{j∈I}.
```

Dans le cas homogène `V_j = V`, cela se réduit à :

```text
Joint_I : X → I → V.
```

## 5. Fermeture

Une sous-famille `I` ferme la cible `σ` si la cible est déterminée par la vue conjointe de `I`.

Forme fonctionnelle :

```text
Closed(I,σ)
⇔
∃ pred : (Π_{j∈I} V_j) → Y,
  ∀ x ∈ X,
    σ(x) = pred(Joint_I(x)).
```

Pour une cible propositionnelle `φ : X → Prop`, la forme correspondante est :

```text
Closed(I,φ)
⇔
∃ pred : (Π_{j∈I} V_j) → Prop,
  ∀ x ∈ X,
    φ(x) ↔ pred(Joint_I(x)).
```

Forme par fibres :

```text
Closed(I,σ)
⇔
∀ x,y ∈ X,
  (∀ j ∈ I, obs_j(x) = obs_j(y)) → σ(x) = σ(y).
```

Forme par résidu :

```text
Closed(I,σ)
⇔
Res(I) = ∅.
```

Forme numérique :

```text
ρ(I) := #Res(I)
```

Alors :

```text
Closed(I,σ) ⇔ ρ(I) = 0.
```

## 6. Incidence des pertes

Le scalaire `ρ(I)` ne contient pas toute la structure. Il indique seulement combien de distinctions
restent perdues par toute la famille `I`.

L’objet complet est l’incidence :

```text
Inc_σ : R_σ → 𝒫(J)
Inc_σ(d) := { j ∈ J | d ∈ L_j }.
```

Pour une distinction requise `d` :

```text
Inc_σ(d)
```

est l’ensemble des interfaces qui perdent `d`.

Dualement, on peut utiliser la table des intersections :

```text
W(U) := ⋂_{j∈U} L_j
```

pour toute sous-famille `U ⊆ J`.

La quantité `ρ(U)` est alors :

```text
ρ(U) = #W(U).
```

Le scalaire `ρ` est une projection de l’incidence. L’incidence est l’objet structurel.

## 7. Monotonie

Si `I ⊆ K`, alors ajouter des interfaces ne peut pas augmenter le résidu :

```text
Res(K) ⊆ Res(I).
```

Donc :

```text
ρ(K) ≤ ρ(I).
```

La fermeture est monotone :

```text
Closed(I,σ) and I ⊆ K
⇒
Closed(K,σ).
```

## 8. Gain marginal

Le gain marginal de l’interface `j` après la sous-famille `I` est :

```text
δ(I,j) := ρ(I) - ρ(I ∪ {j}).
```

Comme :

```text
Res(I ∪ {j}) = Res(I) ∩ L_j,
```

on obtient :

```text
δ(I,j) = #(Res(I) \ L_j).
```

Lecture :

```text
δ(I,j)
```

compte les distinctions encore résiduelles après `I` que `j` sépare.

Une interface est utile relativement à `I` si :

```text
δ(I,j) > 0.
```

Elle est redondante relativement à `I` si :

```text
δ(I,j) = 0.
```

Equivalentement :

```text
j utile relativement à I
⇔
Res(I ∪ {j}) ⊂ Res(I).
```

```text
j redondante relativement à I
⇔
Res(I ∪ {j}) = Res(I).
```

## 9. Fermeture irréductible

Une sous-famille `I` est une fermeture irréductible de `σ` si elle ferme `σ` et si aucune sous-famille
stricte ne ferme `σ`.

Définition :

```text
IrreducibleClosed(I,σ)
⇔
Closed(I,σ)
and
∀ K ⊂ I, not Closed(K,σ).
```

Forme résiduelle :

```text
IrreducibleClosed(I,σ)
⇔
Res(I) = ∅
and
∀ K ⊂ I, Res(K) ≠ ∅.
```

Forme numérique :

```text
IrreducibleClosed(I,σ)
⇔
ρ(I) = 0
and
∀ K ⊂ I, ρ(K) > 0.
```

Une fermeture irréductible est une coalition minimale d’accès.

## 10. Essentialité et redondance dans une coalition fermante

Soit `I` une sous-famille telle que :

```text
Closed(I,σ).
```

Une interface `j ∈ I` est essentielle dans `I` si son retrait détruit la fermeture :

```text
Essential(j,I)
⇔
Res(I \ {j}) ≠ ∅.
```

Forme numérique :

```text
Essential(j,I)
⇔
ρ(I \ {j}) > 0.
```

Une interface `j ∈ I` est redondante dans `I` si son retrait préserve la fermeture :

```text
Redundant(j,I)
⇔
Res(I \ {j}) = ∅.
```

Forme numérique :

```text
Redundant(j,I)
⇔
ρ(I \ {j}) = 0.
```

Dans une fermeture irréductible, toute interface est essentielle.

## 11. Clôture directe et clôture médiée

Il faut distinguer deux régimes.

### Clôture directe

La sous-famille `I` ferme directement `σ` lorsque :

```text
Res(I) = ∅.
```

Dans ce cas, aucune information additionnelle n’est requise pour décider `σ` depuis `I`.

### Clôture médiée

La sous-famille `I` ne ferme pas directement `σ` lorsque :

```text
Res(I) ≠ ∅.
```

Une médiation finie ajoute une observation supplémentaire :

```text
M : X → Fin n.
```

L’observation conjointe médiée est :

```text
Joint_{I,M} : X → (Π_{j∈I} V_j) × Fin n
Joint_{I,M}(x) := (Joint_I(x), M(x)).
```

La famille médiée ferme `σ` lorsqu’il existe une règle de décision :

```text
Closed_M(I,M,σ)
⇔
∃ pred : ((Π_{j∈I} V_j) × Fin n) → Y,
  ∀ x ∈ X,
    σ(x) = pred(Joint_{I,M}(x)).
```

Le médiateur est minimal si :

```text
∃ M_n : X → Fin n, Closed_M(I,M_n,σ)
and
∀ m < n, ∀ M_m : X → Fin m, not Closed_M(I,M_m,σ).
```

Ainsi :

```text
clôture directe : Res(I) = ∅
clôture médiée  : Res(I) ≠ ∅, puis Joint_{I,M_n} ferme avec n minimal
```

## 12. Non-descente du médiateur

Un médiateur `M` descend vers une sous-famille `K ⊆ I` si sa valeur est déjà déterminée par l’interface
jointe de `K`.

Définition :

```text
Descends(M,K)
⇔
∃ f : (Π_{j∈K} V_j) → Fin n,
  ∀ x ∈ X,
    M(x) = f(Joint_K(x)).
```

Un médiateur est irréductible relativement à `I` s’il ne descend vers aucune sous-famille stricte :

```text
IrreducibleMediator(M,I)
⇔
∀ K ⊂ I, not Descends(M,K).
```

La non-descente signifie que le médiateur n’est pas une information marginale déguisée. Il dépend réellement
de la coalition d’accès.

## 13. Forme blackbox

Une boîte noire n’est pas opaque absolument. Elle est opaque relativement à une famille d’interfaces.

Pour une cible `σ`, l’opacité relativement à `I` est :

```text
Opaque(I,σ) ⇔ Res(I) ≠ ∅.
```

La boîte noire est fermée relativement à `I` lorsque :

```text
Closed(I,σ) ⇔ Res(I) = ∅.
```

L’explication minimale d’une décision cible est alors :

```text
une sous-famille I telle que
Res(I) = ∅
and
∀ K ⊂ I, Res(K) ≠ ∅.
```

Dans le régime médié, l’explication minimale est :

```text
une sous-famille I
un médiateur fini M_n
une preuve que Joint_{I,M_n} ferme
une preuve que m<n échoue
une preuve que M_n ne descend vers aucune sous-famille stricte pertinente
```

## 14. Schéma de preuve par interfaces

Un problème global peut être abordé par interfaces lorsque la cible `σ` admet une décomposition de l’accès :

```text
R_σ = distinctions requises
L_j = pertes d’interface
Res(I) = pertes communes
```

Une preuve par interfaces suit le schéma :

```text
1. définir les interfaces ;
2. identifier les pertes L_j ;
3. calculer l’incidence des pertes ;
4. montrer que certaines marges ne ferment pas ;
5. montrer qu’une coalition contracte le résidu ;
6. traiter le résidu restant ;
7. établir la fermeture ;
8. prouver l’irréductibilité ou la minimalité.
```

Ce schéma ne dépend pas de la nature particulière de `X`. Il dépend de l’existence :

```text
d’une cible σ
d’interfaces partielles
d’un espace de distinctions requises
d’une notion de perte par interface
d’un critère de fermeture
```

## 15. Exemple fini complet : XOR

Soit :

```text
X = {00, 01, 10, 11}
σ(x) = xor(x)
```

Les distinctions requises sont les paires non ordonnées de valeurs XOR différentes :

```text
R_σ = {00|01, 00|10, 01|11, 10|11}
r_σ = 4.
```

Définir deux interfaces :

```text
A(x) = premier bit de x
B(x) = second bit de x.
```

Pertes :

```text
L_A = {00|01, 10|11}
L_B = {00|10, 01|11}.
```

Chaque marginale échoue :

```text
Res({A}) = L_A ≠ ∅
Res({B}) = L_B ≠ ∅.
```

Le résidu conjoint est :

```text
Res({A,B})
= L_A ∩ L_B
= ∅.
```

Donc :

```text
Closed({A,B},σ)
ρ({A,B}) = 0.
```

La fermeture est irréductible :

```text
ρ({A}) = 2 > 0
ρ({B}) = 2 > 0
ρ({A,B}) = 0.
```

Ainsi `{A,B}` est une coalition minimale d’accès pour `σ`.

Les gains marginaux sont :

```text
δ(∅,A) = ρ(∅) - ρ({A}) = 4 - 2 = 2
δ(∅,B) = ρ(∅) - ρ({B}) = 4 - 2 = 2
δ({A},B) = ρ({A}) - ρ({A,B}) = 2 - 0 = 2
δ({B},A) = ρ({B}) - ρ({A,B}) = 2 - 0 = 2.
```

Lecture médiée :

```text
I = {A}
M = B : X → Fin 2.
```

Alors :

```text
Joint_{I,M}(x) = (A(x), B(x))
```

ferme `σ`. Un médiateur de taille `1` est constant, donc `Joint_{I,M_1}` ne porte pas plus
d’information que `A` seul. Comme `A` ne ferme pas `σ`, aucun médiateur `Fin 1` ne ferme au-dessus de `{A}`.

Donc, dans cette présentation :

```text
M = B
```

est un médiateur fini de taille minimale `2`, équivalemment un bit d’accès additionnel.

## 16. Résumé formel

Objets :

```text
X, σ, R_σ, J, (L_j)_{j∈J}
```

Résidu :

```text
Res(I) = ⋂_{j∈I} L_j
Res(∅) = R_σ
```

Fermeture :

```text
Closed(I,σ) ⇔ Res(I)=∅
```

Projection numérique :

```text
ρ(I)=#Res(I)
Closed(I,σ) ⇔ ρ(I)=0
```

Gain :

```text
δ(I,j)=ρ(I)-ρ(I∪{j})=#(Res(I)\L_j)
```

Irreductibilité :

```text
IrreducibleClosed(I,σ)
⇔
ρ(I)=0 and ∀K⊂I, ρ(K)>0
```

Médiation :

```text
I ne ferme pas directement
Joint_{I,M_n} ferme
∀m<n, Joint_{I,M_m} échoue
M_n ne descend pas vers une sous-famille stricte
```

Formule condensée :

```text
accès informationnel
=
incidence des pertes
+ contraction du résidu
+ fermeture
+ minimalité
```
