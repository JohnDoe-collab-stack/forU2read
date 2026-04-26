# Entropie de clôture (version courte)

On travaille dans le cas **fini/discret**.

## 1) Données

- `S` : états latents, avec une loi `P` sur `S`
- `O : S -> V` : interface observable
- `Y : S -> A` : vérité cible

L’observation `O` et la cible `Y` deviennent des variables aléatoires via `s ~ P`.

## 2) Définition (défaut de clôture)

On définit le **défaut entropique de clôture** de `Y` sur `O` par :

```text
D_P(Y ; O) := H_P(Y | O)
```

Lecture : `D_P(Y ; O)` est l’incertitude moyenne qui reste sur `Y` **après** avoir observé `O`.

## 3) Critère de clôture

Clôture (au sens probabiliste) :

```text
D_P(Y ; O) = 0
```

Équivalent :

```text
∃ f : V -> A,  Y(s) = f(O(s))   pour P-presque tout s.
```

Donc `D_P(Y ; O) = 0` signifie : « `O` détermine `Y` (sous `P`) ».

## 4) Shannon “sans perte”

Si `*` désigne l’interface triviale (constante), alors :

```text
H_P(Y) = D_P(Y ; *)
```

Et les quantités usuelles se relisent comme des **différences de défauts de clôture** :

```text
I_P(Y ; O)       = D_P(Y ; *) - D_P(Y ; O)
I_P(Y ; R | O)   = D_P(Y ; O) - D_P(Y ; (O, R))
```

Donc `D_P(Y ; O)` donne une lecture unifiée : *entropies = défauts*, *informations = réductions de défauts*.

## 5) Action : clôture active

On ajoute :

- `Act` : actions
- `R : S × Act -> B` : réponse de l’environnement
- une politique `α : V -> Act`

Réponse sous politique :

```text
R_α(s) := R(s, α(O(s)))
```

Interface enrichie :

```text
O_α(s) := (O(s), R_α(s))
```

Défaut après action :

```text
D_P(Y ; O_α) = H_P(Y | O, R_α)
```

La politique **ferme activement** la cible si :

```text
D_P(Y ; O_α) = 0.
```

## 6) Gain d’une politique

Le gain de clôture de `α` est :

```text
G_P(α) := D_P(Y ; O) - D_P(Y ; O_α) = I_P(Y ; R_α | O).
```

Interprétation : une bonne politique choisit l’action qui maximise l’information apportée par la réponse, relativement à ce qui est déjà visible.

## 7) Mini-exemple (intuition)

Si `O` ne donne rien (interface triviale), alors `D_P(Y ; O) = H_P(Y)` : toute l’incertitude sur `Y` reste.

Si une action correcte permet d’obtenir une réponse `R_α = Y`, alors :

```text
D_P(Y ; O_α) = H_P(Y | O, R_α) = H_P(Y | Y) = 0,
```

donc la clôture devient possible **après** enrichissement de l’interface par la réponse.
