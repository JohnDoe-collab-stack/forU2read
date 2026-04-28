# Objectif des “tests algèbre” (ce que l’on vise vraiment)

Ce mémo décrit la logique des tests “avec l’algèbre” dans `Empirical/aslmt/v18_*`.

## 1) L’objet visé

On fixe un espace fini d’états `X`, une signature cible `σ : X → Y`, et une famille de vues (interfaces) `O_i : X → V_i`.

Le solveur ne voit pas `x ∈ X` directement : il part d’une vue de base (interface initiale), puis choisit des vues additionnelles par action/requête.

La question n’est pas “faire un benchmark de plus”.

La question est :

> est-ce qu’un solveur peut *apprendre à choisir des interfaces* de façon à rendre `σ(x)` déterminable après composition de vues ?

## 2) Ce que le test “algèbre” ajoute par rapport à `law_v3b`

`law_v3b` atteste une boucle query + médiation via des audits (barrières, baselines, ablation/swap, IID/OOD, seeds).

Les tests “algèbre” ajoutent une **cible interne explicite** :

- l’objet qu’on veut rendre opérationnel est l’algèbre des pertes de distinctions,
- la réussite doit suivre une *contraction d’un résidu* (conceptuellement : l’analogue d’un `ρ`), pas seulement un score final.

Donc on passe de :

> “le solveur réussit”

à :

> “le solveur réussit *par réduction structurée de la perte résiduelle*”

ce qui rend l’échec diagnostiquable et rend l’audit plus fin.

## 3) Le cœur (version minimale, sans notation lourde)

À un instant donné, la trace observée (base + réponses précédentes) définit un **ensemble candidat** de states possibles.

Pour une vue `i`, regarder `O_i` sur cet ensemble candidat revient à dire :

- quelles distinctions restent confondues si on ajoute cette vue,
- quelles distinctions deviennent accessibles.

Le solveur doit choisir la vue qui “coupe” le meilleur morceau du résidu courant.

En multi-steps, la réussite correspond à :

- résidu non nul au départ (base seule),
- résidu qui diminue quand on ajoute des vues utiles,
- résidu nul après `T` requêtes (clôture sur l’interface conjointe).

## 4) Pourquoi une version “strong” est nécessaire

Une version trop facile peut laisser une règle de sélection évidente (ex. “prendre les vues où `uniq>1` dans la fibre de base”).

Dans ce cas, la boucle query + audits reste valide, et la réussite reste réelle,
mais la *sélection de vues* n’exerce pas l’algèbre au niveau visé.

La version “strong” vise donc une propriété simple :

> plusieurs vues varient dans la fibre de base (donc elles ressemblent toutes “utiles” localement),
> et seule la bonne conjonction ferme `σ`.

Donc la policy doit apprendre à discriminer les vues par leur effet sur la clôture, pas par un simple test local.

## 5) Ce que prouve un “pass” solide (lecture stricte)

Quand un run `solid` passe avec les audits (barrières + baselines + ablation/swap + IID/OOD + multi-seeds),
on peut conclure :

- la clôture sur l’interface initiale échoue (visible-only échoue),
- la réussite dépend bien d’une médiation interne qui pilote la requête,
- la requête est causalement responsable (swap suit le médiateur, ablation casse),
- et, en version “strong”, la politique choisit des vues selon le critère de clôture (pas selon une heuristique locale).

## 6) Où lire la théorie dans le projet

- `Private_notes/distinction_arithmetic.md` : algèbre “distinctions → pertes → incidence → cardinalisation”.
- `Private_notes/algebra_to_architecture.md` : traduction directe “algèbre → politique de requête → architecture + audit”.

