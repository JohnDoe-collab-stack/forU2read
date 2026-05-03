## Incompletude

Note de terminologie : dans ce projet, “décider” / “décidable depuis une interface” signifie **clôture / factorisation**
(existence d’une règle dépendant seulement de la valeur d’interface). Ce n’est pas “décidable” au sens calculabilité.

Dans les cas diagonaux formalises ici, une interface observable est dite incomplete lorsqu une diagonalisation exhibe un echec de cloture sur le visible, c est a dire une situation ou la verite dynamique visee varie a visible fixe. Dans ce cas, aucune regle visible only ne peut etre correcte partout sur la fibre pertinente. L insuffisance est ensuite quantifiee par la plus petite capacite de mediation finie necessaire pour reparer la decision, autrement dit la dimension minimale du relevement mediateur requis.

## Completude

Une interface est dite complete lorsqu elle ferme deja, sans mediation non triviale, l ambiguite qu une diagonalisation pourrait autrement reveler. Autrement dit, aucune diagonalisation ne peut produire une separation intra fibre de la verite dynamique visee, et une regle visible only suffit deja a decider correctement cette verite sur la fibre pertinente. Dans ce sens, aucune information supplementaire n est necessaire pour restaurer la cloture.

## Referentiel

La diagonalisation, la factorisation dynamique qu elle force, et l isolement d un mediateur fini qui ne descend pas aux marginales sont relatifs a un sujet, au sens d un quotient, au sens ou ils ne sont formulables et certifiables causalement que dans un referentiel qui fixe une interface de decision, une verite dynamique visee, et un quotient d indiscernabilite.

Un quotient est dit sujet au sens referentiel lorsqu il est suffisamment structure pour rendre formulables, dans ce cadre, l indiscernabilite visible, la verite dynamique visee, et une separation diagonale eventuelle de cette verite a visible fixe.

Note: dans l exposition, j introduis souvent le mot sujet avant de nommer explicitement referentiel, parce que referentiel est facilement mal lu comme un vocabulaire de coordonnees.

## Auto reference

Un systeme est dit auto referentiel relativement a un referentiel donne lorsque la decision visee ne se ferme pas sur les marginales visibles seules, mais factorise a travers un etat interne ou un mediateur porte par le systeme.
Dans la lecture empirique, cela signifie que la decision correcte depend d une variable interne non reductible au visible seul, et que cette variable joue le role de mediateur minimal pour la verite dynamique visee.

## Autoreflexivite

Un systeme est dit auto reflexif relativement a un referentiel donne lorsque son etat interne n intervient pas seulement comme support passif de mediation, mais produit une operation qui reconfigure ensuite ce qui devient observable, accessible ou decidable pour le systeme lui meme.
Dans la lecture empirique, cela signifie que l etat interne sert a orienter une requete, une intervention, une selection ou une relecture, de sorte que la decision finale est prise sous un acces transforme par le systeme.

## Induction

Dans ce cadre, une induction est une iteration de referentiels.

1. On fixe un quotient, donc une interface de decision et une verite dynamique visee, dans un cadre suffisamment expressif pour formuler une diagonalisation.
2. Une diagonalisation exhibe une non cloture sur ce visible, ce qui force une factorisation dynamique par un mediateur qui ne descend pas aux marginales.
3. On construit alors le referentiel suivant en etendant l interface par ce mediateur, ou en passant a une interface jointe.
4. On re applique le meme schema a une nouvelle verite dynamique visee dans ce nouveau cadre.

## Physique

Un dispositif d’observation est complet pour une dynamique donnée, relativement à une vérité dynamique visée, si les observables qu’il fournit suffisent à décider sans ambiguïté cette vérité dans les situations considérées.
S il ne le fait pas, il existe des situations indiscernables dans l espace observable qui divergent sur la verite dynamique visee.
La mediation minimale est alors le plus petit supplement de variables necessaire pour lever exactement cette indiscernabilite vis a vis de la verite visee, sans pretendre decider autre chose que la verite visee.

ou bien

une interface observable est complète pour une vérité cible exactement quand cette vérité est déjà une fonction du visible ; sinon, l’incomplétude est la dimension minimale d’un supplément de médiation nécessaire pour rendre cette dépendance vraie.

## Langage courant

Un systeme est dit **complet** si ses observables suffisent a decider sans ambiguite la verite dynamique visee sur la dynamique consideree.
Inversement, un systeme est **incomplet** si des situations dynamiquement distinctes restent indiscernables dans l espace observable ; la mediation minimale est alors le plus petit supplement de variables necessaire pour lever cette indiscernabilite pour la verite visee.

Ou plus simplement

le visible n’est pas un invariant suffisant de la vérité dynamique, et la médiation mesure l’écart exact entre ce qui est observable et ce qui est décidable.

## Glossaire (pour ce document)

- Interface observable: application qui associe a un micro etat une observation visible. Deux micro etats sont visibles identiques s ils ont la meme observation.
- Quotient (sens referentiel): specification de ce qui est considere identique du point de vue de l interface observable.
- Marginales visibles: les composantes visibles d une situation, au sens du quotient choisi.
- Fibre: ensemble des micro etats qui partagent le meme visible, donc la meme valeur de l interface observable.
- Verite dynamique visee: la proposition a decider, definie par une dynamique et un critere (ce document ne suppose pas qu on decide tout l etat).
- Cloture (sur le visible): la verite dynamique visee est deja une fonction du visible, sur le domaine considere.
- Non cloture (sur le visible): la verite dynamique visee varie a visible fixe sur le domaine considere.
- Diagonalisation: methode qui produit un temoin de non cloture, par separation intra fibre.
- Mediation: supplement necessaire pour restaurer la cloture de la verite visee sans pretendre decider plus que cette verite.
- Mediateur fini: variable interne de capacite finie suffisante pour decider la verite visee sur le domaine considere.
- Descente: un mediateur descend au visible si sa valeur est deja reconstructible depuis le quotient visible.
- Non descente: impossibilite de reconstruire le mediateur depuis le visible seul, sous non cloture, lorsqu on exige une decision correcte.
- Certification causale (sens operatoire): attestation que la decision suit effectivement le mediateur, par interventions sur ce mediateur.

La stabilité émerge du plus long chemin vérifié capable de préserver son intégrité contextuelle. L’exactitude mesure la justesse des points le long de ce chemin ; l’optimisation point‑par‑point exerce une pression d’effondrement du contexte en isolant ces points de leur champ de dépendances.

Le contexte, entendu comme dépendance au chemin, se manifeste comme une diagonalisation : il force une factorisation dynamique entre interfaces, et fait apparaître des orthogonalités qui ne sont pas des corrélations, mais des invariants d’intervenabilité. Une orthogonalité existe lorsque deux marginales, prises isolément, restent privées d’un accès informationnel, tandis que leur composition rend cet accès possible. Le contenu de cet accès peut être comprimé en un médiateur fini, et la minimalité signifie qu’aucun médiateur strictement plus petit ne suffit à préserver la décision.

« Une orthogonalité existe lorsque deux marginales, considérées isolément, restent privées de l’accès à une pièce d’information, tandis que leur combinaison permet d’y accéder. »

Pensez à Maxwell et à la lumière : on peut lire l’électromagnétisme comme une instance où une loi de composition d’ordre supérieur rend accessible une variable qui n’existe pas comme observable marginale.
