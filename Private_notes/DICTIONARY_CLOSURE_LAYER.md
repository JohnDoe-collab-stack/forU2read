# Clôture du dictionnaire : de la correspondance à la décidabilité par interface

Ce document explique **ce que la théorie apporte à un “dictionnaire”** (au sens large : une table de correspondances
entre objets/observables), en s’appuyant sur la version raffinée :
`Private_notes/distinction_arithmetic_refined.md`.

L’idée centrale est simple :

> Un dictionnaire dit *“à quoi correspond quoi”*.  
> La théorie de clôture dit *“quand une interface suffit à décider une vérité visée, quand elle échoue, et ce qu’il faut ajouter pour réparer l’accès”*.

## 0) Résumé en une phrase

> La théorie de clôture transforme un dictionnaire de correspondances en système de **décidabilité par interfaces** :
> elle distingue **échec marginal**, **clôture directe**, **clôture médiée** et **dimension minimale du médiateur**.

## 1) Notion de base : vérité visée, interface, fibre, clôture

On fixe :
- une **vérité dynamique visée** `σ` (ce qu’on veut décider, pas “tout l’état”),
- une ou plusieurs **interfaces** (observables) `A`, `B`,
- la **fibre** associée à une interface (les micro‑états indiscernables à interface fixée),
- et la notion de **décider depuis une interface** :

> “`σ` est *fermée* sur `A`” signifie : sur le domaine considéré, `σ` est une fonction de `A`  
> (autrement dit, il existe une règle qui dépend **seulement** de la valeur de `A`).

Ce point est important : on ne parle pas de “score”, mais d’un **critère de factorisation**.

## 2) Ce que la théorie ajoute au dictionnaire : une théorie d’accès

Une table de correspondance (un dictionnaire) ne dit pas automatiquement :
- si une interface `A` donne un accès suffisant à `σ`,
- si deux interfaces `A` et `B` composées suffisent,
- si une composition laisse encore un **résidu**,
- ni quelle est la **capacité minimale** d’un médiateur nécessaire pour stabiliser la décision.

La théorie ajoute exactement ces questions (et leurs réponses structurées) :

1) **No‑go marginal** : `A` seul ne ferme pas, et `B` seul ne ferme pas.
2) **Composition** : `A∧B` est le premier niveau où l’information devient soit
   - **directement décidable**, soit
   - **localisable comme résidu** réparable par médiation finie.
3) **Médiateur fini minimal** (si on est dans le cas médié) : il existe une capacité finie `n` suffisante, et
   **aucune** capacité strictement plus petite `m<n` ne suffit.

Cette distinction **direct vs médié** est le cœur de l’alignement :
elle évite de confondre “la composition ferme” avec “la composition *supporte* une réparation”.

## 3) Apport spécifique (ce que le dictionnaire standard laisse implicite)

La théorie ajoute quatre couches opératoires au‑dessus d’une correspondance :

| Dictionnaire | Théorie de clôture |
| --- | --- |
| objet ↔ observable | vérité visée `σ` ↔ interface capable de décider |
| correspondance globale | condition locale de clôture (sur un domaine) |
| table statique | régime dynamique d’accès (marges / composition / médiation) |
| reconstruction “admise” | médiateur minimal requis pour stabiliser la décision |

Point clé :

> **correspondance ≠ décidabilité**  
> Une correspondance peut exister tout en restant inopérante depuis une interface donnée,
> jusqu’à composition et/ou médiation.

## 3) Deux invariants complémentaires : `ρ` (résidu finitaire) et `n` (minimalité structurelle)

Dans un modèle fini explicite (calcul par distinctions), on dispose d’un invariant de résidu d’incidence :

- `ρ` mesure ce qui reste perdu après composition (au niveau finitaire).

Mais dans la couche structurelle COFRS (spine Lean), l’invariant fort de “ce qu’il faut ajouter” est :

- `n` = **dimension minimale** du médiateur (formalisée par `CompatDimEq … n`, et “pas plus petit”).

Repère (résumé) :
- **clôture directe** : le critère finitaire “résidu nul” capture bien le fait que `A∧B` ferme déjà ;
- **clôture médiée** : le finitaire peut signaler un résidu, mais le fait structurel est :
  *“il faut un médiateur fini minimal de dimension `n` pour rendre la décision stable”*.

## 4) Lecture “dictionnaire” (sans sur‑promettre une identification physique)

On peut utiliser ce cadre comme **couche d’analyse** au‑dessus d’un dictionnaire existant :

- le dictionnaire fournit des correspondances (objets ↔ observables),
- la théorie de clôture fournit un **critère d’accès** : quelle interface décide quelle vérité visée,
  et dans quel régime (direct ou médié).

Important : ce document ne postule **aucune identification** (par exemple “tel objet géométrique = médiateur minimal”).
Toute identification de ce type est une hypothèse supplémentaire qui doit être justifiée dans le contexte physique.

## 5) Application (exemple) : dictionnaire holographique comme problème d’accès

Lecture correcte (sans identification automatique) :

| Holographie (dictionnaire) | Lecture par clôture (accès) |
| --- | --- |
| bulk/bord | correspondance de base |
| sous‑région du bord | interface |
| observable bulk (ou propriété intérieure) | vérité visée `σ` |
| wedge d’intrication / reconstruction | domaine de clôture (où `σ` devient décidable) |
| RT/QES/island | **candidat** médiateur dans une instanciation physique |
| Page time | transition de régime d’accès |
| décodage de l’information | décision stabilisée depuis l’interface |

Ce que la théorie permet de demander proprement :

> “Cette région du bord ferme‑t‑elle `σ` ?  
> Si non, une composition de régions ferme‑t‑elle `σ` ?  
> Si un résidu subsiste, quel médiateur minimal (au sens structurel) est requis pour stabiliser la décision ?”

## 6) Ce qui est certifiable (preuve instanciée) vs prouvable (preuve universelle)

La théorie a deux couches complémentaires :

- **Couche universelle (Lean / COFRS)** : prouve des implications structurelles du type
  *no‑go marginal → nécessité d’une composition → existence et minimalité d’un médiateur fini*,
  avec des hypothèses explicitement formulées.

- **Couche expérimentale (proofpack)** : certifie sur des épisodes instanciés :
  - des témoins de no‑go marginal (même observation, vérité différente),
  - que la composition + médiateur marche,
  - et que si on réduit la capacité, on produit des contre‑exemples systématiques.

## 7) Pitch (version resserrée)

English:

```text
A holographic dictionary says what corresponds to what.
Closure theory says when a correspondence becomes decidable from an interface.

It separates marginal failure, direct closure, mediated closure, and minimal mediator dimension.
In Page-curve settings, Page time can be read as a transition in access regime: the radiation becomes able to decide the target information through the appropriate mediated reconstruction.
```

Français :

```text
Un dictionnaire dit ce qui correspond à quoi.
La théorie de clôture dit quand cette correspondance devient décidable depuis une interface.

Elle sépare échec marginal, clôture directe, clôture médiée et dimension minimale du médiateur.
Dans le cas de la Page curve, Page time se lit comme une transition de régime d’accès : la radiation devient capable de décider l’information visée via la reconstruction médiée appropriée.
```

## 8) Pointeurs

- Version raffinée (direct vs médié, `ρ` vs `n`) :
  `Private_notes/distinction_arithmetic_refined.md`.
- Chaîne COFRS (universelle) :
  `COFRS/Examples/IndependenceRelationMediationChain.lean`
  et la variante self-contained :
  `COFRS/Examples/IndependenceRelationMediationChain_DynamicsOnly.lean`.
