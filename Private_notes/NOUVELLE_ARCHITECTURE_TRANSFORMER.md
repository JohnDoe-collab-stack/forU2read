# Nouvelle architecture Transformer visée par le projet

Ce fichier décrit l architecture Transformer que le projet cherche a valider.

Il ne s agit pas d un audit externe de modeles existants.
Il s agit d une specification architecturale dont la theorie Lean donne le contrat structurel, et dont les protocoles empiriques testent la validite.

Convention de lecture du document :

- `description` = lecture humaine du phenomene
- `spec stricte` = objets, fonctions et chaine explicite
- `operativite` = operation exacte qui porte le mot dans le protocole
- `attestation` = ce que le test calcule effectivement pour tenir la propriete

## 1. Idee directrice

Le projet ne vise pas un Transformer qui decide seulement a partir de l interface visible fournie au moment de la decision.

Le projet vise un Transformer dans lequel :

- la fermeture sur le visible peut echouer structurellement
- cette non cloture force l apparition d un mediateur interne
- ce mediateur a une capacite finie mesurable
- la decision finale depend effectivement de ce mediateur
- et cette dependance peut etre testee par interventions

La these est donc architecturale :

- la bonne architecture n est pas une simple architecture visible vers sortie
- la bonne architecture est une architecture de mediation explicite

Dans le vocabulaire du projet, cela veut dire des le depart :

- une architecture autoreferentielle
- et, dans son extension la plus riche, une architecture autoreflexive

## 2. Ce que cette architecture n est pas

Cette architecture n est pas :

- un Transformer standard qui lit une interface et produit directement une sortie
- un simple Transformer avec plus de taille ou plus de donnees
- un systeme avec memoire implicite non contrainte
- un latent ajoute de facon opportuniste sans contrat de capacite ni test causal

Le projet ne cherche pas seulement a montrer qu un modele avec memoire peut mieux marcher.
Il cherche a valider une architecture ou la mediation interne fait partie du contrat du systeme.

## 3. Coeur de l architecture

Le coeur de la nouvelle architecture Transformer est le suivant.

### 3.1 Encodeurs d interface

Le systeme recoit une ou plusieurs interfaces.
Selon les protocoles, cela peut etre :

- une image de decision
- une image de cue
- plusieurs vues
- plusieurs quotients ou plusieurs interfaces partielles

Chaque interface est encodee par un bloc de type Transformer ou par un module equivalent compatible avec le contrat du systeme.

### 3.2 Mediateur interne explicite

L architecture doit produire un etat interne qui porte l information manquante pour la verite dynamique visee.

Ce mediateur :

- n est pas un residu cache laisse sans interpretation
- doit etre lu comme un objet interne de decision
- doit avoir une capacite controlable
- doit pouvoir etre soumis a des tests d ablation et de permutation

Dans les temoins actuels, ce role est joue par `z`.

### 3.2 bis Autoreferentialite

Description :

L autoreferentialite n est pas ici un mot vague.
Elle designe le fait empirique suivant :

- la decision correcte ne se ferme pas sur le visible seul
- le systeme doit passer par un etat interne qu il porte lui meme
- cet etat interne sert de mediateur pour la verite dynamique visee
- la tete de decision doit donc dependre de ce mediateur

Autrement dit, l architecture est dite autoreferentielle lorsque le systeme doit passer par sa propre mediation interne pour decider correctement.

Attestation operatoire :

- le visible seul rencontre une barriere explicite ou un baseline visible only plafonne
- un mediateur interne nomme est present dans le protocole
- la decision de A depend de ce mediateur de facon structurelle
- le protocole calcule sur les memes cas les trois branches base, ablation, swap
- l ablation degrade nettement la decision
- le swap detruit l adequation aux labels d origine et suit au contraire la permutation attendue

En pratique, on tient donc l autoreferentialite pour attestee seulement si le protocole expose le mediateur et si les mesures `ablation_drop`, `swap_vs_orig`, `swap_vs_perm` montrent qu il est effectivement load bearing.

Spec stricte :

- `v` = visible d entree
- `z` = mediateur interne
- `y` = decision finale

Chaine operatoire :

- `z = Encode(v)`
- `y = Decide(z)`

Mot en face de chaque terme :

- `v` = visible
- `z` = mediateur
- `y` = decision

Sens strict dans ce projet :

- l autoreferentialite = `v -> z -> y`
- et non `v -> y`

Operativite stricte :

- l operation explicite est la mediation par `z`
- autrement dit, la decision est calculee a travers `z`

Calcul de test :

- `base` = `y = Decide(z)`
- `ablation` = `y = Decide(0)`
- `swap` = `y_i = Decide(z_j)`

Attestation attendue :

- `ablation_drop` fort
- `swap_vs_perm` eleve
- `swap_vs_orig` degrade

Operation exacte dans le protocole :

- un mediateur interne `z` est calcule
- la decision finale est lue a travers `z`
- l ablation remplace `z` par `0`
- le swap remplace `z_i` par `z_j`
- la variation de la decision mesure alors explicitement la charge de `z`

Lecture humaine :

- le systeme ne peut pas decider correctement depuis le visible seul
- il doit d abord construire un mediateur interne
- puis la decision finale est lue a travers ce mediateur
- c est cela qui fait que l architecture est autoreferentielle

Ainsi, ici, l autoreferentialite ne veut pas seulement dire :

- etat interne

Elle veut dire strictement :

- visible d entree
- puis construction d un mediateur interne
- puis decision finale lue a travers ce mediateur

Et son attestation experimentale veut dire strictement :

- branche `base` sur `z`
- branche `ablation` sur `0`
- branche `swap` sur `z` permute
- comparaison explicite des sorties obtenues

### 3.3 Tete de decision verrouillee par l etat

Le point le plus important est que la tete de decision ne doit pas court circuiter le mediateur.

La decision finale doit etre produite a partir du mediateur, ou a partir d une interface etendue dans laquelle le mediateur joue un role structurel necessaire.

Dans la forme la plus nette de ce principe :

- la tete lit seulement le latent global `z`

Dans d autres formes de travail presentes dans le depot :

- la decision est conditionnee par une combinaison structuree du mediateur et d un terme visible necessaire

Mais dans tous les cas, la mediation ne doit pas etre contournable par une lecture directe du visible.

### 3.4 Audit interventionnel du mediateur

Le mediateur doit etre charge causalement.

Cela signifie que l architecture doit supporter des operations comme :

- ablation du mediateur
- permutation ou swap du mediateur entre exemples
- eventuellement reconfiguration de l acces a partir de l etat interne

Si l architecture est correcte, la decision doit suivre ces interventions de la facon attendue.

### 3.5 Autoreflexivite

Description :

L autoreflexivite designe ici un regime empirique plus fort.

Dans ce regime :

- l etat interne ne sert pas seulement a porter l information manquante
- il sert aussi a orienter l acces ulterieur a l information
- il peut selectionner une vue, un quotient, une requete ou une interaction suivante
- la decision finale se fait donc sous un acces transforme par le systeme lui meme

L autoreflexivite prolonge l autoreferentialite.
Elle ajoute a la mediation interne une action du systeme sur ses propres conditions d acces a la decision.

Attestation operatoire :

- etat interne vers choix d action
- choix d action vers nouvelle observation ou resultat de requete
- nouvelle observation vers decision finale

Ce n est donc pas seulement un test de memoire.
C est un test ou l etat interne pilote une action qui modifie ensuite le regime empirique de decision.

Spec stricte :

- `x` = vues initiales
- `m` = etat interne avant action
- `a` = action de requete
- `r` = retour d environnement
- `m'` = etat interne apres retour
- `y` = decision finale

Chaine operatoire :

- `m = Encode(x)`
- `a = Query(m)`
- `r = Env(a)`
- `m' = Update(m, r)`
- `y = Decide(m')`

Mot en face de chaque terme :

- `m` = etat interne
- `a` = action
- `r` = nouvelle observation
- `m'` = etat mis a jour
- `y` = decision

Sens strict dans ce projet :

- l autoreflexivite = `m -> a -> r -> m' -> y`
- sa partie proprement autoreflexive = `m -> a -> r`

Operativite stricte :

- l operation explicite n est pas seulement `Decide`
- l operation explicite est `Query` puis `Env`
- autrement dit, le systeme agit depuis son etat interne pour produire une information nouvelle avant de decider

Condition structurale :

- il doit exister une vraie etape `Query`
- il doit exister une vraie etape `Env`
- la decision doit se faire apres `r`
- un anti bypass doit interdire `visible courant -> action`

Attestation attendue :

- que l action est calculee depuis l etat interne et non depuis le visible courant
- que cette action produit une observation ou un resultat intermediaire nouveau
- que la decision finale depend de cette boucle et non d un contournement direct

Instance exacte dans `law_v3b` :

- `m = FoldViews(view_seq)`
- `a = QueryHead(m)`
- `r = Env(a)` avec retour `res_tok`
- `m' = Update(m, r)`
- `y = OutHead(m')`

Operation exacte dans `law_v3b` :

- la memoire interne est construite par accumulation de vues
- la requete est choisie par `logits_query(mem_for_query)`
- le visible courant est explicitement neutralise avant la requete par anti bypass
- la requete appelle ensuite l environnement et produit un `res_tok`
- la decision finale est ensuite lue apres cette transition

Lecture humaine :

- le modele construit un etat
- il choisit une requete depuis cet etat
- cette requete fait apparaitre une information nouvelle
- puis le modele decide

Ainsi, ici, l autoreflexivite ne veut pas seulement dire :

- memoire interne

Elle veut dire strictement :

- memoire interne
- puis requete choisie depuis cette memoire
- puis retour d environnement
- puis decision finale sur ce nouvel acces

Lecture complementaire :

- l etat interne ne sert pas seulement a memoriser
- il sert a choisir quoi faire ensuite
- cette action change alors ce que le systeme peut effectivement savoir
- la decision finale est prise apres cette transformation de l acces
- c est cela qui fait que l architecture est autoreflexive

## 4. Forme actuelle dans le depot

Le depot contient plusieurs temoins partiels ou plus avances de cette architecture.

Convention de cette section :

- chaque ligne ci dessous designe un temoin de contrat
- un temoin n est pas necessairement l architecture finale complete
- mais il instancie explicitement une partie de la spec

### 4.1 Ligne JEPA stateful

Description :

Dans `v7` et `v8`, on voit deja une ligne claire :

- encodeur de type Transformer sur les entrees
- etat interne mis a jour au fil des vues
- tete de masque predite depuis l etat
- variantes d ablation et de swap

Cette ligne montre la rupture avec un regime visible only.

Elle atteste surtout l autoreference operatoire.
Elle n est pas encore la forme pleine de l autoreflexivite, car il n y a pas encore de politique de requete explicite qui reconfigure l acces au probleme.

Spec stricte du temoin :

- `x = (v_1, ..., v_T)` = sequence de vues
- `m = FoldViews(x)` = etat interne accumule
- `y = MaskHead(m)` = sortie lue depuis l etat

Operativite stricte :

- l etat est mis a jour vue apres vue
- la tete lit cet etat pour produire la sortie
- des operations `ablation` et `swap` sont appliquees a cet etat

Attestation :

- la sortie suit la branche `base`
- elle chute sous `ablation`
- elle suit le latent permute sous `swap`

### 4.1 bis Ligne query POMDP autoreflexive

Description :

Dans `law_v3b`, le projet porte deja une forme empirique explicite d autoreflexivite :

- un etat memoire interne est construit depuis la sequence de vues
- une action de requete est choisie depuis cet etat interne
- cette action produit ensuite un resultat d environnement
- et la decision finale est prise apres cette reconfiguration d acces

Le point decisif est que la requete ne lit pas directement le visible courant comme source de decision interne.
Le protocole impose explicitement un anti bypass avant la requete.

Cette ligne n est donc pas seulement autoreferentielle.
Elle est deja autoreflexive au sens operatoire des tests.

Spec stricte du temoin :

- `m = FoldViews(view_seq)`
- `a = QueryHead(m)`
- `r = Env(a)`
- `m' = Update(m, r)`
- `y = OutHead(m')`

Operativite stricte :

- la requete est calculee depuis `m`
- le retour `r` n existe qu apres l action `a`
- la decision finale est lue apres mise a jour par `r`

Attestation :

- anti bypass sur le visible courant
- verification de la boucle `m -> a -> r -> y`
- audit causal sur les etats memoire

### 4.2 Ligne state-locked

Description :

Dans `law_v5b`, l idee est encore plus explicite :

- l architecture A calcule un latent global `z`
- la tete lit seulement ce latent
- les baselines visibles restent contraintes a des classes locales observables only

Ici, la mediation n est pas seulement presente.
Elle est verrouillee architecturalement.

Spec stricte du temoin :

- `z = EncoderA(v)`
- `y = Head(z)`

Operativite stricte :

- la tete de decision ne lit pas directement le visible
- la tete lit seulement `z`
- le visible ne peut donc pas court circuiter la mediation

Attestation :

- audit `base / ablation / swap` sur `z`
- comparaison contre des baselines visibles only

### 4.3 Ligne min-lift

Description :

Dans `vN3b`, `v9`, `v10` et leurs suites :

- le mediateur `z` a une capacite explicite
- on teste que `z = n` ferme
- et que `z < n` ne ferme pas

Cette ligne ne doit pas etre lue comme l architecture finale elle meme.
Elle doit etre lue comme une validation experimentale du contrat de capacite de l architecture visee.

Spec stricte du temoin :

- `cap(z) = k`
- on compare `k = n` et `k < n`

Operativite stricte :

- on fait varier explicitement la capacite du mediateur
- on mesure ensuite fermeture ou non fermeture du contrat

Attestation :

- `k = n` doit fermer
- `k < n` ne doit pas fermer
- la difference doit etre stable sous verification

## 5. Ce que les tests valident vraiment

Les tests du projet ne servent pas a auditer des modeles du marche.

Ils servent a valider que l architecture proposee satisfait bien son contrat.

Les tests verifient :

- qu il existe une barriere structurelle sur le visible
- qu une mediation interne restaure la decision
- que cette mediation a une capacite minimale mesurable
- que la decision suit causalement le mediateur
- et, dans les protocols de type query, que l etat interne pilote une action qui reconfigure ensuite ce qui est observe ou decide
- et que cette structure reste stable quand on varie la taille, la famille de taches et la classe de solveurs

Autrement dit :

- les tests ne servent pas d abord a comparer
- ils servent d abord a etablir que l architecture est la bonne

Spec de validation :

- `B0` = barriere sur le visible
- `M0` = restauration par mediation
- `C0` = capacite minimale mesurable
- `K0` = charge causale du mediateur
- `R0` = boucle autoreflexive quand le protocole contient une requete
- `U0` = stabilite de ces proprietes quand on varie regimes et solveurs

Operativite :

- `B0` se mesure par echec du visible only
- `M0` se mesure par succes du systeme medie
- `C0` se mesure par variation explicite de `cap(z)`
- `K0` se mesure par `base / ablation / swap`
- `R0` se mesure par la chaine `m -> a -> r -> y`
- `U0` se mesure par repetition a travers familles, tailles et classes de solveurs

## 6. Role de l universalite

L universalite n est pas un embellissement final.
Elle sert a montrer que les proprietes observees ne sont pas des accidents locaux de benchmark.

Si le programme reussit, on n obtient pas seulement une loi empirique.
On obtient une architecture validee.

L universalite doit montrer que :

- la mediation n est pas un hack local
- la capacite minimale n est pas un artefact d un seul monde
- les causal gates ne sont pas une curiosite de protocole
- le contrat tient a travers plusieurs regimes

Le resultat vise est donc :

- une architecture Transformer differente
- definie non par sa taille, mais par son contrat de mediation

Spec de validation par universalite :

- soit une famille de taches `F`
- soit une famille de tailles `N`
- soit une famille de solveurs `S`
- le contrat est dit stable si `B0`, `M0`, `C0`, `K0` et, quand applicable, `R0`, restent vrais a travers `F`, `N`, `S`

Operativite :

- l universalite ne construit pas un nouveau bloc
- elle teste la stabilite des specs deja posees
- elle sert donc de validation externe du contrat architectural

## 7. Direction finale de l architecture

La direction finale du projet peut etre formulee ainsi :

- un Transformer ne doit plus etre compris seulement comme un approximateur de fonction sur interface
- il doit etre compris comme un systeme autoreferentiel de mediation interne explicite
- cette mediation doit etre minimale, lisible, non triviale et testable

Dans une extension plus riche, deja annoncee dans certaines notes de conception, cette architecture peut devenir autoreflexive :

- le systeme porte plusieurs mediateurs locaux
- il peut construire des mediateurs de couplage
- et il peut choisir quelle interface ou quel quotient interroger ensuite a partir de son etat interne avant la decision finale

Cette extension ne remplace pas le coeur du projet.
Elle en est le prolongement naturel.

Spec cible minimale pour la construction :

- `InterfaceEncoder_i : X_i -> T_i`
- `MediatorCore : (T_1, ..., T_k, m_prev) -> m`
- `DecisionHead : m -> y`
- `CausalAuditHooks : m -> (ablation, swap)`

Extension autoreflexive :

- `QueryPolicy : m -> a`
- `EnvironmentAdapter : a -> r`
- `StateUpdate : (m, r) -> m'`
- `DecisionHeadReflexive : m' -> y`

Sens de construction :

- la version autoreferentielle minimale construit `m` puis decide
- la version autoreflexive construit `m`, agit via `a`, recoit `r`, met a jour en `m'`, puis decide

## 8. Formule courte

La nouvelle architecture Transformer visee par le projet est une architecture de mediation explicite :

- obstruction sur le visible
- mediateur interne a capacite finie
- regime autoreferentiel de decision
- tete de decision dependante de ce mediateur
- test causal de la charge du mediateur
- extension possible vers un regime autoreflexif
- validation de la stabilite de ce contrat par universalite

Sur la ligne autoreflexive deja presente dans les tests, ce contrat devient :

- etat interne
- choix d action ou de requete depuis cet etat
- nouvelle observation produite par cette action
- decision finale sous acces reconfigure

Formule de construction :

- autoreferentiel minimal : `v -> z -> y`
- autoreflexif : `x -> m -> a -> r -> m' -> y`

## 9. Statut de ce document

Ce document est une specification de travail.

Il dit ce que l architecture doit etre au sens du projet.
Il ne pretend pas que chaque detail d implementation finale est deja fige dans un unique fichier du depot.

Ce qui est deja fixe, en revanche, est le contrat structural que cette architecture doit satisfaire.
