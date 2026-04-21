# Document corrigé (sans LaTeX)

Ce document est une réécriture corrigée du texte fourni, en restant aligné avec les définitions et objets Lean existants dans ce repo.

## 0) Références (chemins réels dans le repo)

Les fichiers mentionnés comme “bridges” dans ce projet sont :
- `C:\Users\frederick.loubli.TKS\Documents\lean\forU2read\COFRS\Examples\IndependenceToAutoreflexiveQueryBridge.lean`
- `C:\Users\frederick.loubli.TKS\Documents\lean\forU2read\COFRS\Examples\IndependenceToAutoreflexiveQueryRefiningLiftBridge.lean`
- `C:\Users\frederick.loubli.TKS\Documents\lean\forU2read\COFRS\Examples\IndependenceToAutoreflexiveQueryStrongBridge.lean`

La couche “référentielle / chaînes disciplinées” est formalisée ici :
- `C:\Users\frederick.loubli.TKS\Documents\lean\forU2read\COFRS\Examples\ReferentialInduction.lean`

La couche “théorèmes globaux paramétriques” (3 variantes de terminaison) est ici :
- `C:\Users\frederick.loubli.TKS\Documents\lean\forU2read\COFRS\Examples\DisciplinedChainsGlobal.lean`

La couche “dynamique” (Compatible, StepSeparatesFiber, etc.) est ici :
- `C:\Users\frederick.loubli.TKS\Documents\lean\forU2read\COFRS\Dynamics.lean`

## 1) La notion (notation mathématique “pure”, mais calquée sur Lean)

Un stade référentiel est un quadruplet :

    R = (X, Q, q, T)

- X : Type (domaine)
- Q : Type (quotient / référentiel courant)
- q : X -> Q
- T : X -> Prop (vérité cible)

Dans Lean, c’est `ReferentialProblem` avec champs `X`, `Q`, `q`, `T`.

### 1.1 Clôture (Closes)

Définition (exactement la forme Lean) :

    Closes(R)  :<->  exists pred : Q -> Prop, forall x : X,  T x <-> pred (q x)

Dans Lean : `ReferentialProblem.Closes`.

### 1.2 Témoin diagonal (DiagonalWitness)

Définition (forme Lean) :

    DiagonalWitness(R) :<-> exists x x' : X,
      x != x' and q x = q x' and T x and not (T x')

Dans Lean : `ReferentialProblem.DiagonalWitness`.

Conséquence (formalisée) :

    DiagonalWitness(R) -> not Closes(R)

Dans Lean : `not_closes_of_diagonalWitness`.

### 1.3 Médiation finie (MediatesLe)

Dans le code, “taille n” est représentée par `Fin n`. La médiation finie (donnée) est :

    MediatesLe(R, n) :<-> exists sigma : X -> Fin n,
                         exists predFin : Fin n -> Prop,
                         forall x : X, T x <-> predFin (sigma x)

Dans Lean : `ReferentialProblem.MediatesLe`.

### 1.4 Descente vers le quotient (DescendsToQuot)

Toujours en style Lean (avec `Fin n`) :

    DescendsToQuot(R, sigma) :<-> exists f : Q -> Fin n,
                                 forall x : X, sigma x = f (q x)

Dans Lean : `ReferentialProblem.DescendsToQuot`.

Conséquence (formalisée) :

    DescendsToQuot(R, sigma) and MediatesLe(R, n) -> Closes(R)

Dans Lean : `closes_of_descendsToQuot_of_mediatesLe`.

### 1.5 Extension forcée du quotient (extendQuot)

Dans Lean, l’extension par `sigma : X -> Fin n` est :

    Ext_sigma(R) = (X, Q × Fin n, x ↦ (q x, sigma x), T)

Dans Lean : `ReferentialProblem.extendQuot`.

Conséquence (formalisée) :

    MediatesLe(R, n) with witness (sigma, predFin)
    -> Closes(Ext_sigma(R))

Dans Lean : `closes_extendQuot_of_mediatesLe`.

### 1.6 Correction majeure par rapport au texte initial

Le texte initial contenait une flèche implicite du type :

    DiagonalWitness(R) -> “médiateur fini”

Ce n’est pas vrai en général.

Ce qui est vrai (et prouvé dans Lean) est plutôt :

    DiagonalWitness(R) -> not Closes(R)

et, séparément, si on te donne une médiation finie (MediatesLe), alors tu closes après extension.

Donc l’enchaînement correct est :

    (donnée de DiagonalWitness)  +  (donnée de MediatesLe)
    -> (le médiateur ne descend pas au quotient initial)
    -> (l’extension ferme)

Dans Lean : `not_descends_of_diagonalWitness_of_mediatesLe` + `closes_extendQuot_of_mediatesLe`.

## 2) Pas d’induction, transition disciplinée, dérivation finie (aligné Lean)

### 2.1 Pas d’induction référentielle (InductionStep)

Dans Lean, un “pas” est une donnée `InductionStep` qui contient :
- un stade `R`
- un `n`
- un `sigma : R.X -> Fin n`
- un prédicat `predFin : Fin n -> Prop`
- un témoin diagonal `diag : DiagonalWitness(R)`
- une preuve de médiation `mediates : forall x, T x <-> predFin (sigma x)`

Intuition : “diag” certifie que l’ancien quotient ne suffit pas ; “mediates” donne un résumé fini, mais pas forcément descendant au quotient initial.

### 2.2 Retarget (changement de contenu)

Une transition change ensuite le contenu en remplaçant T par Tplus sur le même X/Q/q :

    retarget(R, Tplus) = (X, Q, q, Tplus)

Dans Lean : `ReferentialProblem.retarget`.

### 2.3 Transition disciplinée (UsesExtension, DisciplinedStageTransition)

Dans `ReferentialInduction.lean`, la notion “le nouveau contenu utilise réellement l’extension” est encapsulée par :
- `UsesExtension` (prédicat sur une `StageTransition`)
- puis `DisciplinedStageTransition` = une `StageTransition` + une preuve `usesExtension`.

L’idée est exactement celle-ci (en français) :
“vu depuis l’ancienne vue (oldView), le nouveau contenu n’est pas clos, donc la transition force l’usage du nouveau quotient étendu”.

### 2.4 Dérivation disciplinée finie (DisciplinedReferentialDerivation)

Une dérivation disciplinée est un objet inductif (donc finitaire par construction) :
- soit on s’arrête si le stade est clos (`stop`)
- soit on prend une transition disciplinée et on continue sur le stade suivant (`next`)

Dans Lean : `DisciplinedReferentialDerivation`.

## 3) Instanciation dynamique (ce que disent les fichiers)

L’instance dynamique (pour un préfixe h et un step) sert à fabriquer un problème référentiel R_(h,step) dont la vérité T encode “Compatible(step, x)” restreint à une fibre.

Le texte initial dit :
- StepSeparatesFiber(h, step) -> DiagonalWitness(R_(h,step))
- et si on a RefiningLiftData ou CompatSigDimLe, alors on obtient un InductionStep sur R_(h,step)

Cette lecture est cohérente avec les théorèmes présents (voir notamment dans `ReferentialInduction.lean`) :
- `inductionStep_of_refiningLiftData`
- `inductionStep_of_compatSigDimLe_of_stepSeparatesFiber`

Important : les conditions exactes (niveaux, paramètres, “au même stade”, etc.) sont celles des théorèmes Lean, pas une règle générale sans hypothèses.

## 4) La relation de chaîne

Le texte initial définit une relation élémentaire R -> R' via “transition disciplinée avec réparation”.

Dans Lean, l’objet correspondant est `DisciplinedStageTransitionWithRepair`, et il fournit :
- une transition disciplinée `J`
- des définitions de “stade suivant” (`Rnext`, `Rnext'`)

Dans Lean, on peut définir explicitement la relation (déjà écrite dans `DisciplinedChainsGlobal.lean`) :

    Leadsto(R, R') :<-> exists K : DisciplinedStageTransitionWithRepair,
                          K.J.toStageTransition.I.R = R  and  K.Rnext' = R'

Et `leadsto*` est représenté dans le projet par la clôture réflexive-transitive :

    ReflTransGen Leadsto R0 RT

(définie dans `COFRS/Foundations.lean` comme `PrimitiveHolonomy.Relation.ReflTransGen`).

La notion “il existe une chaîne finie qui termine par un stade clos” est :

    exists RT,  R0 leadsto* RT  and  Closes(RT)

## 5) Le “théorème global des chaînes” (corrigé: attention au non-classique)

Le texte initial propose :

G1) Pour tout stade actif R, soit Closes(R), soit existe R' actif avec R leadsto R'.
G2) Il n’existe pas de chaîne infinie R0 leadsto R1 leadsto R2 ... avec tous actifs.
Conclusion) Pour tout R0 actif, il existe un RT tel que R0 leadsto* RT et Closes(RT).

Correction de fond :
- Classiquement, (G1)+(G2) est un schéma standard de “terminaison”.
- Constructivement, (G1)+(G2) sous forme “or exists” + “pas de chaîne infinie” ne suffit pas toujours à construire une chaîne finie, parce que (G1) ne donne pas un choix effectif de successeur quand on est dans le cas “exists R'”.

Deux formulations qui restent propres et constructives (compatibles avec Lean sans Classical) :

### Version A (successeur explicite + mesure)

Donner une donnée de progression quand non-clos, par exemple :

    next(R) : si Active(R) et not Closes(R), alors on fournit un R' avec Active(R') et R leadsto R'

et donner une mesure naturelle qui décroît strictement :

    rank : ActiveStages -> Nat
    et  R leadsto R'  implique  rank(R') < rank(R)

Alors on obtient une chaîne finie jusqu’à Closes, par induction sur Nat.

### Version B (bien-fondation)

Supposer directement que la relation `leadsto` est bien-fondée sur les stades actifs
(au sens Lean: `WellFounded` / `Acc`), plus une règle locale de progression (G1).
Alors on obtient le résultat par induction bien-fondée.

### Version C (rang fini, type Fin n)

C’est une variante pratique de “finitude + progrès strict” :

    rankFin : ActiveStages -> Fin n
    et  R leadsto R'  implique  rankFin(R').val < rankFin(R).val

Dans Lean, cette variante existe aussi (réduction vers la version Nat).

### Version D (cycle = “clôture / audit infini”)

Si, dans ton cadre, un “cycle” compte comme une forme de clôture (au sens : on a un audit infini mais périodique, donc stabilisé),
alors on peut remplacer l’objectif “atteindre Closes” par l’objectif plus faible :

    Terminal(R) := Closes(R)  OU  Cycle(R)

Ici “Cycle(R)” peut vouloir dire (au choix, selon ta théorie) :
- cycle dans la dynamique (un état x revient : x -> F(x) -> ... -> x),
- ou cycle au niveau des stades (un stade R_i réapparaît : R_i -> ... -> R_i),
- ou cycle au niveau d’un “audit” (la signature auditable associée au stade se répète).

Ce verrou est conceptuellement différent des invariants globaux classiques :
on ne cherche pas une quantité monotone sur tout le temps,
on cherche une notion de “récurrence” qui certifie que la branche n’errera pas à l’infini sans jamais revenir sur une forme déjà auditée.

Forme de théorème global typique dans ce mode :

    pour tout R0 actif,
    il existe RT atteignable tel que Terminal(RT)

Autrement dit : toute branche active atteint soit une clôture finie, soit une boucle (audit infini mais périodique).

Dans Collatz, si “cycle” est le critère terminal, l’énoncé global devient :
“toute trajectoire finit par entrer dans un cycle”, et la conjecture Collatz classique ajoute :
“le seul cycle est 4 -> 2 -> 1 -> 4”.

Conclusion corrigée :
Le “verrou” global est bien une hypothèse de terminaison, mais sa bonne forme constructive
est “bien-fondation” ou “mesure décroissante” (ou un mécanisme explicite de choix),
pas seulement une négation d’existence de chaîne infinie.

Note d’intégration :
Ces trois versions sont maintenant disponibles comme lemmes paramétriques dans
`COFRS/Examples/DisciplinedChainsGlobal.lean`, y compris des wrappers déjà instanciés sur
`ReferentialProblem` via la relation `Leadsto`.

Note : la version “cycle / audit infini” n’est pas encore encapsulée ici (elle dépend du sens précis de “cycle” dans ta théorie :
cycle sur X, sur Q, sur les stades, ou sur une signature d’audit). Si tu me dis quelle définition exacte tu utilises dans tes fichiers,
je l’intègre proprement au même niveau que les autres variantes.

## 6) Spécialisation Collatz (corrigée)

Dans ce repo, il n’y a pas de formalisation Collatz (pas de module, pas d’énoncé Collatz).

Tu peux garder la section Collatz comme un “template d’instanciation” :
“si on instancie la dynamique F de Collatz dans la couche Dynamics + ReferentialInduction,
alors l’énoncé global prend telle forme”.

Mais il faut éviter de la présenter comme un résultat déjà démontré par les fichiers existants.

## 7) Résumé corrigé (une ligne)

Localement, les fichiers construisent des étapes/bridges (diagonal + médiation finie via hypothèses dynamiques)
et des transitions disciplinées ; globalement, pour obtenir “toute branche termine”, il faut une hypothèse
de terminaison formulée constructivement (mesure décroissante ou bien-fondation, ou choix explicite de successeur).
