# Entropie, clôture informationnelle, action

## 0. Objets

On fixe :

- `S` : espace des états latents
- `V` : espace des observations visibles
- `A` : espace des vérités cibles
- `Act` : espace des actions possibles
- `B` : espace des réponses possibles

Hypothèse (pour que `H(·)` soit défini sans théorie de la mesure) :

- `S, V, A, B, Act` sont **finis** (ou, au minimum, discrets et traités avec la mesure de comptage),
- `P` est une loi discrète sur `S` (une pmf).

On a :

```text
O : S -> V
```

Interface observable.

```text
Y : S -> A
```

Vérité cible.

```text
R : S × Act -> B
```

Réponse obtenue après une action.

On fixe aussi une distribution :

```text
P on S
```

Alors `s ~ P` induit des variables aléatoires :

- `O := O(s)`
- `Y := Y(s)`
- et, pour chaque action `a`, `R_a := R(s, a)`

C’est seulement avec `P` qu’on peut parler d’entropie (et ici, on parle d’entropie **discrète**).

---

# 1. Clôture logique

`Y` est fermée sur `O` si :

```text
forall s1 s2 in S:

    O(s1) = O(s2)
    =>
    Y(s1) = Y(s2)
```

Equivalent :

```text
exists f : V -> A such that:

    Y = f ∘ O
```

Donc :

```text
Y closed on O
<=>
Y factors through O
```

Non-clôture logique :

```text
exists s1 s2 in S:

    O(s1) = O(s2)
    and
    Y(s1) != Y(s2)
```

Alors aucun solveur visible-only :

```text
F : V -> A
```

ne peut être correct partout, car il devrait satisfaire :

```text
F(O(s1)) = Y(s1)
F(O(s2)) = Y(s2)
```

mais :

```text
O(s1) = O(s2)
```

donc :

```text
F(O(s1)) = F(O(s2))
```

alors que :

```text
Y(s1) != Y(s2)
```

Contradiction.

---

# 2. Défaut entropique de clôture

Définition. Pour une vérité cible `Y` et une interface `O`, sous une loi `P` sur `S`, on définit le **défaut entropique de clôture** par :

```text
D_P(Y ; O) := H_P(Y | O)
```

Conventions techniques :

- on utilise `0 log 0 = 0`,
- les termes `P(Y = y | O = v)` ne sont évalués que pour `P(O = v) > 0`.

Définition (rappel) :

```text
H(Y | O)
=
sum over v:
    P(O = v) * H(Y | O = v)
```

avec :

```text
H(Y | O = v)
=
- sum over y:
    P(Y = y | O = v) * log P(Y = y | O = v)
```

Interprétation stricte :

```text
H(Y | O) = 0
```

signifie :

```text
Y is determined by O, P-almost surely.
```

Autrement dit :

```text
exists f : V -> A such that:

    Y(s) = f(O(s))
```

pour `P`-presque tout `s`.

Et :

```text
H(Y | O) > 0
```

signifie :

```text
O does not determine Y under P.
```

Donc `D_P(Y ; O)` mesure le défaut probabiliste de clôture.

---

## 2bis. Lecture sans perte des quantités de Shannon discrètes

Dans le cas fini/discret, les quantités de Shannon usuelles (dès qu’on fixe une variable-cible et une interface de conditionnement) se relisent à partir du défaut de clôture `D_P(Y ; O)`, ou comme différences de défauts de clôture.

Exemples (égalités exactes) :

- Shannon :

```text
H_P(Y) = D_P(Y ; *)
```

où `*` désigne une interface triviale (constante).

- Entropie conditionnelle :

```text
H_P(Y | O) = D_P(Y ; O)
```

- Information mutuelle (forme canonique) :

```text
I_P(Y ; O) = D_P(Y ; *) - D_P(Y ; O)
```

- Information mutuelle conditionnelle (forme canonique) :

```text
I_P(Y ; R | O) = D_P(Y ; O) - D_P(Y ; (O, R))
```

Donc l’information mutuelle mesure une réduction de défaut de clôture.

# 3. Différence entre clôture logique et clôture entropique

Clôture logique :

```text
forall s1 s2:
    O(s1) = O(s2) => Y(s1) = Y(s2)
```

Elle ne dépend pas de `P`.

Clôture entropique :

```text
H(Y | O) = 0
```

Elle dépend de `P`.

Lien exact :

```text
logical closure
=>
for every P:
    H(Y | O) = 0
```

Mais :

```text
H(Y | O) = 0
=>
logical closure only P-almost surely
```

Donc :

```text
logical closure is stronger than entropy closure.
```

---

# 4. Le médiateur ne crée pas d’information

Si le médiateur est calculé depuis l’observable :

```text
z = m(O(s))
```

alors :

```text
H(Y | O, z) = H(Y | O)
```

car `z` est une fonction de `O`.

Donc `z` seul ne ferme pas le problème.

Son rôle est différent :

```text
z chooses the action.
```

On a :

```text
a = pi(z)
```

Donc :

```text
a = pi(m(O(s)))
```

Le médiateur ne réduit pas directement l’entropie.

Il sélectionne l’action qui peut produire une réponse informative.

---

# 5. Politique d’action

Une politique visible dépend de l’observable :

```text
alpha : V -> Act
```

Dans ton architecture :

```text
alpha = pi ∘ m
```

c’est-à-dire :

```text
O(s) -> z -> a
```

La réponse obtenue sous cette politique est :

```text
R_alpha(s) = R(s, alpha(O(s)))
```

L’interface enrichie devient :

```text
O_alpha(s) = (O(s), R_alpha(s))
```

---

# 6. Clôture après action

La politique `alpha` ferme `Y` si :

```text
forall s1 s2 in S:

    O_alpha(s1) = O_alpha(s2)
    =>
    Y(s1) = Y(s2)
```

c’est-à-dire :

```text
forall s1 s2:

    O(s1) = O(s2)
    and
    R_alpha(s1) = R_alpha(s2)
    =>
    Y(s1) = Y(s2)
```

Equivalent :

```text
exists g : V × B -> A such that:

    Y(s) = g(O(s), R_alpha(s))
```

Donc la vérité devient fermée sur l’interface enrichie :

```text
(O, R_alpha)
```

Remarque : si la résolution nécessite plusieurs actions, on remplace naturellement `R_alpha` par un transcript
(par exemple `(R_{a1}, ..., R_{aT})`) et on applique exactement la même notion de clôture sur
`(O, transcript)`.

---

# 7. Entropie après action

Avant action :

```text
H(Y | O)
```

Après action sous politique `alpha` :

```text
H(Y | O, R_alpha)
```

L’action est informative si :

```text
H(Y | O, R_alpha) < H(Y | O)
```

Elle ferme probabilistiquement le problème si :

```text
H(Y | O, R_alpha) = 0
```

---

# 8. Gain informationnel

Le gain de la politique `alpha` est :

```text
I(Y ; R_alpha | O)
=
H(Y | O) - H(Y | O, R_alpha)
```

Une politique optimale satisfait :

```text
alpha* = argmax_alpha I(Y ; R_alpha | O)
```

équivalent à :

```text
alpha* = argmin_alpha H(Y | O, R_alpha)
```

Si l’action est choisie après observation de `O = v`, la forme locale est :

```text
alpha*(v)
=
argmin_a H(Y | O = v, R_a)
```

ou :

```text
alpha*(v)
=
argmax_a I(Y ; R_a | O = v)
```

où :

```text
R_a(s) = R(s, a)
```

---

# 9. Ton solveur

Visible-only :

```text
O(s) -> Y_hat
```

Il réussit seulement si :

```text
H(Y | O) = 0
```

ou, logiquement :

```text
Y factors through O.
```

Ton solveur actif :

```text
O(s) -> z -> a -> r -> Y_hat
```

avec :

```text
z = m(O(s))
a = pi(z)
r = R(s, a)
Y_hat = g(O(s), z, r)
```

Comme `z` est fonction de `O`, le point informationnel est :

```text
r = R(s, a)
```

La clôture pertinente est donc :

```text
H(Y | O, R_alpha) = 0
```

ou :

```text
Y factors through (O, R_alpha).
```

---

# 10. Forme déterministe de ton expérience

Dans ton expérience, la réponse est de type :

```text
r = k if a = h mod 2
r = 0 otherwise
```

Hypothèse (structure de la tâche) :

```text
Y factors through (O, k).
```

Donc :

```text
correct action:
    a = h mod 2
    r = k
```

et :

```text
wrong action:
    a != h mod 2
    r carries no useful information about k
```

Si la vérité cible dépend de `k`, alors :

```text
wrong action:
    H(Y | O, R_alpha) > 0
```

mais :

```text
correct action:
    H(Y | O, R_alpha) = 0
```

dans le cas idéal.

Donc le solveur doit apprendre :

```text
O -> z -> a = h mod 2
```

pour obtenir :

```text
r = k
```

puis fermer :

```text
Y
```

sur :

```text
(O, R_alpha)
```

---

# 11. Loi centrale

Non-clôture visible :

```text
H(Y | O) > 0
```

ou plus fort :

```text
exists s1 s2:
    O(s1) = O(s2)
    Y(s1) != Y(s2)
```

Clôture active :

```text
exists alpha:
    H(Y | O, R_alpha) = 0
```

ou logiquement :

```text
exists alpha, exists g:
    Y(s) = g(O(s), R(s, alpha(O(s))))
```

Résolution active :

```text
learn alpha such that:
    I(Y ; R_alpha | O) is maximal
```

---

# 11bis. Classification des régimes

L’objet important n’est pas seulement `H(Y | O)` isolément, mais la **stratification** suivante :

```text
1) D_P(Y ; O) = 0
   => clôture passive sur le visible (visible-only admissible sous P)

2) D_P(Y ; O) > 0
   => clôture passive impossible (erreur nulle visible-only impossible sous P)

3) exists alpha:
       D_P(Y ; O_alpha) = 0
   => clôture active possible (médiation/action/requête peut fermer)

4) for all alpha:
       D_P(Y ; O_alpha) > 0
   => non fermable par la classe d’actions autorisée
```

Dans ce cadre, dire que `D_P(Y ; O) > 0` est un “certificat d’impossibilité visible-only” signifie :
**aucun solveur `F : V -> A` ne peut être parfaitement correct `P`-presque sûrement**.

---

# 12. Phrase exacte

Le défaut entropique `D_P(Y ; O) = H_P(Y | O)` mesure le défaut probabiliste de clôture de la vérité cible `Y` sur l’interface observable `O`.

Un médiateur `z` calculé depuis `O` ne réduit pas cette entropie par lui-même.

Son rôle est de choisir une action `a`.

La réponse `r = R(s,a)` peut enrichir l’interface.

Le problème est résolu lorsque l’interface enrichie `(O, R_alpha)` ferme `Y` (intuitivement : quand on observe une réalisation `r = R_alpha(s)`), c’est-à-dire lorsque :

```text
H(Y | O, R_alpha) = 0
```

ou, structurellement :

```text
Y factors through (O, R_alpha).
```
