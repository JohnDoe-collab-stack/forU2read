# v7 (Perfect Amodal Hidden-Target) — Conclusions Et Interpretation (Protocol-Grade)

Ce document fixe les conclusions et l'interpretation **protocol-grade** de `ASLMT v7`, en cohérence avec
`Empirical/aslmt/v7_descriptive/Docs/PLAN_UNIVERSAL_OBS_ONLY_NO_GO_AND_MIN_LIFT.md` et la note de conformite
`Empirical/aslmt/v7_descriptive/Docs/V7_CONFORMITY_TO_COFRS.md`.

Le but est d'avoir une lecture stable, audit-able et non ambiguë de ce que v7 établit, de ce que les runs montrent,
et de ce que cela implique pour la theorie COFRS et la gouvernance experimentale.

## 1) Objet Et Defs (Ce Que v7 Mesure Exactement)

### 1.1 Le witness v7 (structure)

Au niveau environnement, v7 construit une barriere d'interface au temps de decision:

- `obs` (observable de decision) = `image` (scaffold visible + occluder).
- deux états `x, x'` dans la meme fibre (meme `image`) mais avec des `hidden_target` differents.
- un "lift" candidat via `cue_image` (frame antérieure) qui contient l'information manquante.

Propriete structurelle garantie par construction (auditée dans `pair_eval`):

- `image` est identique pour `hidden_label=0` et `hidden_label=1` à contexte fixe.
- `hidden_target` diffère entre `hidden_label=0` et `hidden_label=1`.

Donc toute politique `obs-only` (decision depuis `image` uniquement) est structurellement insuffisante sur la paire.

### 1.2 Le critere "protocol-grade"

La version "protocol-grade" de v7 ne s'appuie pas sur une IoU moyenne. Elle impose une condition binaire par paire:

- pour une liste de contextes `ctx` (taille `n_ctx=64`),
- on rend les deux membres de la paire `(hidden_label=0, hidden_label=1)` a contexte fixe,
- et on exige que le modele A soit **both-correct**:
  - avec `cue0` il doit preferer `target0` à `target1`,
  - avec `cue1` il doit preferer `target1` à `target0`,
  - sur l'ensemble des contextes.

Dans le verifier strict `verify_aslmt_v7_perfect_amodal_hidden_target_pair_oodrequired.py`, la condition est:

- en IID: `A_both_correct_rate = 1.0` et `B_both_correct_rate = 0.0`,
- en OOD: `A_both_correct_rate = 1.0` et `B_both_correct_rate = 0.0`,
- et `obs_barrier_ok = True` partout.

Donc l'objectif experimental est: **perfection sur IID ∪ OOD**, avec barriere obs-only auditée.

## 2) Raccord COFRS (Lecture Theorique)

### 2.1 Correspondance minimale

Le schema COFRS pertinent ici est:

- `obs : S -> V` (projection d'interface) fixe l'information disponible au temps de decision.
- une fibre au-dessus d'un contexte `h` contient des etats distincts `x != x'` tels que `obs x = obs x'`.
- un `step` (verite future) separe `x` et `x'`.

Dans v7:

- `obs` correspond à `image`.
- la fibre est indexée par le contexte `ctx` (géométrie scaffold + occluder), avant tirage du `hidden_label`.
- la separation future correspond à la target `hidden_target` (interieur de l'occluder uniquement).
- le "lift" correspond à la possibilite d'utiliser un etat interne (ou un canal interne) qui transporte l'info du cue.

### 2.2 Ce que v7 ferme

v7 ferme experimentalement deux objets distincts:

1. **No-go obs-only** (structure): `obs` ne factorise pas la verite future.
2. **Existence d'un lift** (constructif empirique): un modele A peut etre rendu parfait sur la famille exigée,
   à condition que le protocole d'entraînement couvre la famille sur laquelle on exige la perfection.

## 3) Resultats (Etat Des Runs)

Les runs "reference" sont consignés dans `Empirical/aslmt/v7_descriptive/Docs/V7_CONFORMITY_TO_COFRS.md`.
Ici on fixe la lecture des deux regimes experimentaux observes dans la campagne `oodrequired`.

### 3.0 Cartographie IID/OOD (Sweep `train_ood_ratio`, verdict du verifier strict)

Les runs ci-dessous sont tous des runs `pair-grade OOD-required` (même vérificateur strict), et doivent être lus
avec la discipline suivante:

- `B_both_correct_rate = 0.0` est un attendu structurel (no-go obs-only) dès que `obs_barrier_ok=True`.
- La variable discriminante est donc uniquement: **est-ce que A ferme IID ∪ OOD** (`A_both_correct_rate=1.0` sur les deux) ?

Table synthèse (représentants auditables dans `Empirical/aslmt/runs/`):

| `train_ood_ratio` | Seeds observés | Verdict strict | Côté qui casse quand FAIL | Run dir représentant |
| --- | --- | --- | --- | --- |
| 0.00 | 0..4 | FAIL | OOD (`A_both<1`) | `aslmt_v7_pair_oodrequired_20260412_233112_63a03389b935` |
| 0.25 | 0..4 | OK | n/a | `aslmt_v7_pair_oodrequired_20260412_233341_63a03389b935` |
| 0.50 | 0..4 | OK | n/a | `aslmt_v7_pair_oodrequired_20260413_002349_63a03389b935` |
| 0.75 | 0..4 | OK | n/a | `aslmt_v7_pair_oodrequired_20260412_233914_63a03389b935` |
| 0.90 | 0 | OK | n/a | `aslmt_v7_pair_oodrequired_20260412_234215_63a03389b935` |
| 0.95 | 0 | OK | n/a | `aslmt_v7_pair_oodrequired_20260413_005043_63a03389b935` |
| 0.97 | 0 | OK | n/a | `aslmt_v7_pair_oodrequired_20260413_005359_63a03389b935` |
| 0.98 | 0 | OK | n/a | `aslmt_v7_pair_oodrequired_20260413_005714_63a03389b935` |
| 0.99 | 0 | OK | n/a | `aslmt_v7_pair_oodrequired_20260413_010025_63a03389b935` |
| 0.995 | 0 | OK | n/a | `aslmt_v7_pair_oodrequired_20260413_010335_63a03389b935` |
| 1.00 | 0..4 | FAIL | IID (`A_both<1`) | `aslmt_v7_pair_oodrequired_20260413_010650_63a03389b935` |

Lecture: les extrêmes (IID-only et OOD-only) ferment leur sous-famille, mais pas l'union IID ∪ OOD; dès qu'il y a
un mélange non nul, la fermeture redevient possible et stable sous le même vérificateur strict.

Seuil empirique actuel (seed 0, bundle `63a033…`, ctx-audit, verifier strict): `train_ood_ratio=0.995` passe `[OK]`,
mais `train_ood_ratio=1.0` échoue (casse en IID, OOD parfait). Donc une couverture IID strictement positive est
nécessaire, et la quantité minimale requise est au plus de l'ordre de `1 - 0.995 = 0.5%` dans ce witness.

### 3.1 Regime stable: `train_ood_ratio = 0.50`

Constat experimental:

- Avec `train_ood_ratio=0.50`, les runs multi-seeds (seeds 0..4) passent le verifier strict OOD-required.
- Autrement dit, la perfection protocol-grade sur IID ∪ OOD est atteinte et stable sur ce protocole.

Artefacts (seeds 0..4, tous `[OK]`):

- seed 0: `Empirical/aslmt/runs/aslmt_v7_pair_oodrequired_20260413_001810_63a03389b935/`
- seed 1: `Empirical/aslmt/runs/aslmt_v7_pair_oodrequired_20260413_002055_63a03389b935/`
- seed 2: `Empirical/aslmt/runs/aslmt_v7_pair_oodrequired_20260413_002349_63a03389b935/`
- seed 3: `Empirical/aslmt/runs/aslmt_v7_pair_oodrequired_20260413_002645_63a03389b935/`
- seed 4: `Empirical/aslmt/runs/aslmt_v7_pair_oodrequired_20260413_002942_63a03389b935/`

Interpretation:

- le training couvre IID et OOD,
- donc le modele apprend une regle conditionnelle correcte sur la famille IID ∪ OOD.

### 3.2 Regime de specialisation: `train_ood_ratio = 1.00`

Signature repetée:

- en OOD: `A_both_correct_rate = 1.0` (perfection OOD),
- en IID: `A_both_correct_rate < 1.0` (echec du protocole),
- et la barriere obs-only reste vraie (`obs_barrier_ok=True`).

Interpretation:

- le training voit une **sous-famille** (OOD seulement),
- la perfection apprise est donc relative à cette sous-famille,
- et la condition du verifier (perfection sur IID ∪ OOD) échoue.

Ce point est crucial: ce n'est pas un "bug de seed", c'est un diagnostic de couverture de famille.

## 4) Ctx-Audit (Resultat Cle: Frontiere IID Identifiee)

Le script `variants/pair/aslmt_train_v7_perfect_amodal_hidden_target_seeded_pair_trainood_ctxaudit.py` ajoute un champ
diagnostic `pair_eval.iid.A_fail_ctxs` (ignore par le verifier strict) qui liste les contextes IID où A échoue.

Sur le run ctx-audit OOD-only (exemple le plus net):

- Run dir: `Empirical/aslmt/runs/aslmt_v7_pair_oodrequired_20260412_235206_63a03389b935/`
- Master: `.../v7_master_20260412_235206_63a03389b935.jsonl`
- `pair_eval.iid.A_both_correct_rate = 0.796875` donc **13 échecs** sur 64.

Et dans ce run, les `A_fail_ctxs` exhibent une localisation parfaite:

- tous les échecs IID sont sur `occ_half=5`,
- tous les échecs IID sont sur `t=2`,
- et la forme d'échec est invariant: `A0_correct=True` (PLUS correct) et `A1_correct=False` (RING casse).

Donc l'échec IID sous training OOD-only n'est pas diffus:

- il se concentre sur une region géométrique précise de la famille IID,
- la "frontiere IID" correspond au plus petit occluder IID (`occ_half=5`) et épaisseur minimale (`t=2`),
- et la sous-classe affectée est systématiquement RING.

Interpretation theorique:

- la regle correcte n'est pas uniquement "porter le cue", mais "porter le cue et l'appliquer conditionnellement au contexte".
- l'entrainement OOD-only n'expose pas la region IID frontière, donc la regle apprise se specialse.
- le ctx-audit transforme "generalisation" en un diagnostic paramétrique explicite (contextes qui cassent).

### 4.1 Ctx-audit du cas dual (IID-only casse OOD)

Le run `train_ood_ratio=0.0` (IID-only) casse en OOD, et les `A_fail_ctxs` montrent un pattern dual:

- Run dir: `Empirical/aslmt/runs/aslmt_v7_pair_oodrequired_20260412_233112_63a03389b935/`
- Master: `.../v7_master_20260412_233112_63a03389b935.jsonl`
- `pair_eval.ood.A_both_correct_rate = 0.703125` donc **19 échecs** sur 64.
- Les échecs sont concentrés sur les gros occluders OOD (`occ_half ∈ {7,8,9}`) et surtout sur `t=4`.
- La forme d'échec majoritaire est opposée au cas OOD-only: `A0_correct=False` et `A1_correct=True` dans la grande majorité des échecs.

Ce n'est pas un détail: cela établit que la non-perfection aux extrêmes est bien une spécialisation de couverture,
pas un bruit d'optimisation.

## 4.1 Resume falsifiable (ce qui est maintenant établi, et comment cela pourrait être contredit)

Sur v7, au sens strict du protocole pair-grade OOD-required, les observations suivantes sont établies:

- (Structure) `obs_barrier_ok=True` en IID et en OOD, ce qui audite l'existence d'une paire `(x,x')` obs-identique mais target-différente.
- (Protocol-grade) `train_ood_ratio=0.50` ferme la perfection sur IID ∪ OOD (runs multi-seeds `[OK]` référencés dans `V7_CONFORMITY_TO_COFRS.md`).
- (Spécialisation) `train_ood_ratio=1.00` obtient la perfection en OOD mais échoue en IID, de manière reproductible.
- (Localisation) Sous `train_ood_ratio=1.00`, le ctx-audit localise l'échec IID sur la frontière `(occ_half=5, t=2)` et sur la classe RING.

Contre-exemples qui invalideraient la localisation:

- un run ctx-audit `train_ood_ratio=1.00` où les échecs IID apparaissent de façon diffuse (pas de concentration sur `occ_half=5, t=2`),
- ou un run où les échecs touchent également PLUS (symétrie brisée),
- ou un run où `occ_half=6` devient systématiquement le point de rupture.

Ces contre-exemples ne contrediraient pas la barrière obs-only (structure), mais contrediraient l'hypothèse "frontière géométrique unique"
et forceraient une analyse plus riche de la couverture minimale.

## 5) Implications Pour La Theorie Et La Gouvernance

### 5.1 No-go vs perfection

v7 met en evidence une separation nette:

- le no-go obs-only est un fait structurel du schema (il ne depend pas du training),
- la perfection du lift sur une famille dépend d'une condition minimale de protocole (couverture de la famille).

Ceci est exactement le type de distinction que COFRS cherche à rendre explicite:

- l'impossibilite obs-only est de nature "interface/fibre",
- la constructibilite d'un lift est de nature "refinement" mais doit etre gouvernée expérimentalement.

### 5.2 Condition minimale de couverture (analogue empirique du "minimal lift")

Le couple `(train_ood_ratio=0.50) OK` et `(train_ood_ratio=1.00) FAIL (sans couverture IID)` n'est pas seulement un fait de performance:

- c'est un diagnostic de "couverture minimale" pour fermer l'objectif protocol-grade IID ∪ OOD,
- et le ctx-audit rend cette condition localisable sur des paramètres de contexte.

Autrement dit, on observe un objet de la forme:

- famille exigée = IID ∪ OOD,
- perfection observable si et seulement si le training couvre une region minimale de contextes,
- et cette region minimale peut être identifiée (frontiere) via les `ctx` d'échec.

Le test "frontier injection" ferme ensuite la boucle: on passe d'un diagnostic (frontiere) à une condition constructive minimale (injection explicite de frontiere) qui restaure `[OK]` même en régime quasi OOD-only.

## 6) Claims Autorises (Et Scope)

Formulation stable et correcte (scope v7):

- v7 établit un no-go obs-only universel au temps de decision (barriere de fibre), audité par `obs_barrier_ok`.
- v7 démontre l'existence d'un lift qui ferme le protocole strict sur IID ∪ OOD sous un protocole d'entrainement
  qui couvre IID et OOD (ex: `train_ood_ratio=0.50`, multi-seeds `[OK]`).
- v7 met en evidence une condition minimale de protocole: OOD-only (`train_ood_ratio=1.0`) atteint la perfection OOD
  mais échoue en IID **si** aucune couverture IID n'est présente, et le ctx-audit localise l'échec sur la frontiere IID (`occ_half=5, t=2`, RING).
- v7 montre une condition constructive minimale: en régime `train_ood_ratio=1.0`, une injection frontière explicite (`frontier_frac`) peut suffire à restaurer `[OK]` sur IID ∪ OOD sous le même vérificateur strict.

Ce que v7 ne revendique pas à lui seul:

- une loi universelle sur toutes architectures et tous mondes possibles,
- une equivalence "OOD-only est toujours pire" (le diagnostic dépend de la famille exigée et du verifier).

## 7) Prochaine Etude (Ce Qu'on Cherche A Fermer)

Prochain test prioritaire: **sweep fin `train_ood_ratio` près de 1.0** pour localiser la couverture minimale qui garde `[OK]`.

Le sweep coarse est déjà établi en seed 0 (table §3.0). Il reste à déterminer le plus grand ratio OOD qui reste `[OK]`
de manière reproductible (multi-seeds), ce qui fixe une "couverture IID minimale" au sens expérimental strict.

Prochain test explicatif (apres sweep): "frontier injection" contrôlée:

- garder `train_ood_ratio` haut,
- injecter explicitement une petite fraction de contextes IID frontière (`occ_half=5, t=2`),
- et tester si cela suffit à fermer IID ∪ OOD.

Objectif: passer d'un diagnostic ("casse sur la frontiere") à une condition minimale constructive ("ajouter X suffit").

### 7.1 Frontier injection (implémentation)

Le test "frontier injection" est implémenté comme une **variante** d'entraînement (nouveau fichier, aucun script historique modifié) :

- train script : `Empirical/aslmt/v7_descriptive/variants/pair/aslmt_train_v7_perfect_amodal_hidden_target_seeded_pair_trainood_ctxaudit_frontier_inject.py`
- campaign runner : `Empirical/aslmt/v7_descriptive/aslmt_campaign_v7_perfect_amodal_hidden_target_pair_oodrequired_v2_frontier_inject.py`

Le principe est strict :

- l'évaluation reste identique (vérificateur strict OOD-required, perfection IID ∪ OOD),
- l'entraînement est quasi OOD-only (`train_ood_ratio=1.0`),
- mais on injecte une fraction `frontier_frac` d'exemples IID **frontière** au training :
  `occ_half=5`, `t=2`, `cx,cy` dans les plages IID, `hidden_label` tiré, et rendu via `render(Ctx(...))`.

Critère de succès : obtenir `[OK]` sous le même vérificateur strict, avec `train_ood_ratio=1.0` et un `frontier_frac` minimal.

### 7.2 Frontier injection (résultat)

Des runs de référence montrent que l'injection frontière ferme effectivement la perfection IID ∪ OOD sous le même vérificateur strict:

- run dir : `Empirical/aslmt/runs/aslmt_v7_pair_oodrequired_20260413_164749_c43988f1e2d0/`
- protocole: `train_ood_ratio=1.0`, `frontier_frac=0.002`, `steps=3000`, `seed=0`, `device=cuda`
- verdict verifier (pair-grade OOD-required) : `[OK]` avec `A_both=1.0000` en IID et en OOD, `B_both=0.0000`, `obs_barrier_ok=True`

Stabilisation protocole-grade (multi-seeds) : la même variante ferme aussi sur seeds 1..4 :

- seed 1 : `Empirical/aslmt/runs/aslmt_v7_pair_oodrequired_20260413_180707_c43988f1e2d0/`
- seed 2 : `Empirical/aslmt/runs/aslmt_v7_pair_oodrequired_20260413_181044_c43988f1e2d0/`
- seed 3 : `Empirical/aslmt/runs/aslmt_v7_pair_oodrequired_20260413_181405_c43988f1e2d0/`
- seed 4 : `Empirical/aslmt/runs/aslmt_v7_pair_oodrequired_20260413_181741_c43988f1e2d0/`

Interprétation minimale: la couverture IID nécessaire pour fermer IID ∪ OOD n'a pas besoin d'être un mélange IID/OOD massif; un epsilon ciblé sur la frontiere suffit (au moins dans ce witness et à ce budget d'entrainement).

## 8) Index Des Artefacts (Scripts)

Canonique (OOD-required, verifier strict):

- `Empirical/aslmt/v7_descriptive/aslmt_campaign_v7_perfect_amodal_hidden_target_pair_oodrequired_v2.py`
- `Empirical/aslmt/v7_descriptive/aslmt_train_v7_perfect_amodal_hidden_target_seeded_pair_trainood.py`
- `Empirical/aslmt/v7_descriptive/verify_aslmt_v7_perfect_amodal_hidden_target_pair_oodrequired.py`

Ctx-audit (diagnostic supplémentaire, sans changer le verifier):

- `Empirical/aslmt/v7_descriptive/variants/pair/aslmt_train_v7_perfect_amodal_hidden_target_seeded_pair_trainood_ctxaudit.py`

Conformite docs:

- `Empirical/aslmt/v7_descriptive/Docs/V7_CONFORMITY_TO_COFRS.md`
- `Empirical/aslmt/v7_descriptive/Docs/COFRS_UNIFIED_STATEMENT.md`
