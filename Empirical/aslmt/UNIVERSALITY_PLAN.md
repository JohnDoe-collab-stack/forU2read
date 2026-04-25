# Plan — Universalité empirique contrôlée → caractérisation abstraite partielle (ASLMT / COFRS)

Ce document fixe un **objectif testable** (universalité *empirique* contrôlée) et un plan d’exécution pour y parvenir, **sans perdre la traçabilité** des résultats.

## 0) Objectif (énoncé cible, version empirique)

Objectif (2 niveaux) :

- **Objectif principal :** établir une **universalité empirique contrôlée** (invariant stable quand on varie `n`, la famille de tâches, et la classe de solveurs).
- **Objectif secondaire :** rechercher une **caractérisation abstraite partielle** (converse / normal form) de la classe de phénomènes couverts.

Universalité empirique contrôlée = établir un invariant stable, reproduisible et falsifiable de la forme :

> Pour une large classe de tâches dynamiques à barrières d’interface, et pour une large classe de solveurs,  
> (i) toute décision *mono-interface* échoue structurellement (barrière),  
> (ii) la réparation exige une capacité minimale mesurable (*min-lift*),  
> (iii) et la dépendance au médiateur est certifiable par interventions (causal gates).

On veut que cet énoncé ne soit pas seulement “il existe une famille qui le réalise”, mais qu’il soit **stable** quand on varie :

- `n` (taille/capacité minimale du médiateur),
- la **famille de tâches** (grammaire de mondes),
- la **classe de modèles** (solveurs),
- et idéalement qu’il existe une **caractérisation abstraite** (converse partiel) de la classe couverte.

## 1) Critères “DONE” (ce qui compte comme fermeture)

Un jalon n’est “fermé” que si un **verifier strict** produit un verdict binaire sur **IID ∪ OOD** et que les runs sont auditables.

### 1.1 Spine minimal à fermer (un seul test consistant)

Un test “consistant” doit vérifier simultanément :

1. **Barrières structurelles**
   - au moins une barrière `obs`-only (comme `v7`),
   - idéalement une **double barrière** (comme `v8`: image-only + cue-only).
2. **Min-lift / capacité**
   - réussite à `z = n`,
   - échec à au moins deux valeurs `z < n` (ex. `z=n-1` et `z=⌊n/2⌋`).
3. **Causal gates**
   - **ablation** : casser la lecture du médiateur casse la réussite,
   - **permutation/swap** : permuter le médiateur fait “suivre” la décision,
   - tout cela sur **IID et OOD**.

### 1.2 Exigences de reproductibilité

- Multi-seeds (par défaut `seed=0..4`).
- Scripts figés (timestamp + hash) et outputs avec le même suffixe (cf. règles de traçabilité du dépôt).
- Un tableau de synthèse qui pointe vers les répertoires `Empirical/aslmt/runs/...` auditables.

## 2) État actuel (ce qui est déjà isolé)

- `v8_descriptive` : **double barrière** + (si causal-gated) interventions (ablation/swap).
- `vN3b_descriptive` : **min-lift** très net sur un cas (ex. `n=4`, `z=4` OK, `z=3` FAIL) + causal gates.
- `v9_unified` : témoin **unifié** (double barrière + min-lift + causal gates) avec une fermeture stricte connue en `n=4`
  (voir le README de `v9_unified` pour les runs de référence).
- `v10_phaseA1` : couche **campagne+verifier matrice** pour exécuter **Phase A1** en une seule passe (multi-`n`, multi-`z`, multi-seeds)
  en s’appuyant sur le témoin `v9_unified` *n-scalable* (verrou barrière + injectivité).
- `v10_phaseA1_kdet_spaced2` : même protocole A1 avec un témoin **spaced2** (anti-overlap) ; sur le run
  `aslmt_v10_phaseA1_unified_nscalable_posloss_pairrank_kdet_spaced2_20260416_074821_9fcd16977fda`,
  **Phase A1 est fermée** sur `n ∈ {3,4,5,6}` avec `seed=0..4` (référence `z=n` OK sur IID/OOD, `z<n` FAIL sur l’image-barrier, causal gates OK).
- `v15_phaseA2_kdet_spaced2_64_contractrank_poswtdice_diag` : montée en échelle A2 (`n ∈ {8,12,16}`) avec witness-level fix (OOD cue corruption contract-preserving) ;
  sur le run `aslmt_v15_phaseA2_unified_nscalable_poswtdice_contractrank_imgcuerank_kdet_spaced2_64_20260420_082149_5c9bb19a82ab`,
  **Phase A2 est fermée** sur `n ∈ {8,12,16}` avec `seed=0..4` (référence `z=n` OK sur IID/OOD, `z<n` FAIL sur l’image-barrier, causal gates OK).
- `law_v3b_unified_v2_strong_qforced_zread` : instanciation explicite d’un régime **autoreflexif** (action→réponse) dont l’action est une lecture du médiateur interne `z` (zread),
  avec audit ablation/swap sur le médiateur, et vérification stricte en `solid` (IID ∪ OOD, multi-seeds, matrice `z∈{n,n-1,⌊n/2⌋}`).
  Référence fermée en `n=8` : `Empirical/aslmt/runs/aslmt_law_v3b_unified_v2_strong_qforced_zread_solid_20260423_102039_9f958bfafaad/` (matrix `z∈{8,7,4}`, `seed=0..4`, verifier strict OK).
  Stabilité en `n` : le bloc `n=12` est fermé en `solid` (multi-seeds, verifier strict OK) via `law_v3b_unified_v2_strong_qforced_zread_stability_n` :
  `Empirical/aslmt/runs/aslmt_law_v3b_unified_v2_strong_qforced_zread_stability_n_solid_20260424_213134_9f958bfafaad/`.
  Prochaine fermeture : bloc `n=16` sous le même protocole/verifier (stabilité-in-n complète).
  Axe orthogonal : ajouter une famille OOD supplémentaire via `law_v3b_unified_v2_strong_qforced_zread_ood2_family` (verifier strict IID+OOD+OOD2).
- `v16_phaseB_temporal_zigzag_64` : **famille Phase B** (sans occlusion, vérité dynamique = trajectoire zigzag temporelle) ; outillage prêt (renderer+env+trainer+campaign+verifier).
- `v17_phaseB_symbolic_orbit_64` : **famille Phase B** (sans occlusion, vérité dynamique = orbite symbolique affine) ; outillage prêt (renderer+env+trainer+campaign+verifier).

Conclusion : le spine est présent, Phase A1 est fermée, Phase A2 est fermée ; le prochain travail est la généralisation (familles / solveurs / converse).

### 2.1 Résultat A1 (tableau minimal)

Run : `Empirical/aslmt/runs/aslmt_v10_phaseA1_unified_nscalable_posloss_pairrank_kdet_spaced2_20260416_074821_9fcd16977fda/`
Master : `Empirical/aslmt/runs/aslmt_v10_phaseA1_unified_nscalable_posloss_pairrank_kdet_spaced2_20260416_074821_9fcd16977fda/v10_master_20260416_074821_9fcd16977fda.jsonl`

Lecture (résultat “publisable” au niveau Phase A1) :

> Sous `profile=solid`, la chaîne unifiée (double barrière + min-lift + causal gates) est stable quand `n` varie :
> pour `n=3,4,5,6` et `seed=0..4`, le groupe de référence `z=n` ferme strictement (IID ∪ OOD), et des groupes `z<n`
> échouent strictement sur l’image-barrier, avec barrières valides, baselines à 0, ablation à 0, et swap-follow qui suit l’échec.

Table (min sur seeds 0..4, deux splits) :

| `n` | `z=n` (réf) | `z<n` testés | Réf : `A_img_min` / `A_cue_min` (IID/OOD) | Sous-capacité : `A_img_min` (IID/OOD) |
|---:|:--:|:--|:--|:--|
| 3 | PASS | `z=2` | `1.0 / 1.0` | `0.6719 / 0.6719` |
| 4 | PASS | `z=3`, `z=2` | `1.0 / 1.0` | `0.8281/0.7500`, `0.6719/0.6719` |
| 5 | PASS | `z=4`, `z=2` | `1.0 / 1.0` | `0.8281/0.8906`, `0.5938/0.5625` |
| 6 | PASS | `z=5`, `z=3` | `1.0 / 1.0` | `0.9062/0.9375`, `0.7812/0.7969` *(OOD cue drops to `0.9688` for `z=3`)* |

### 2.2 Résultat A2 (v15, tableau minimal)

Run : `Empirical/aslmt/runs/aslmt_v15_phaseA2_unified_nscalable_poswtdice_contractrank_imgcuerank_kdet_spaced2_64_20260420_082149_5c9bb19a82ab/`
Master : `Empirical/aslmt/runs/aslmt_v15_phaseA2_unified_nscalable_poswtdice_contractrank_imgcuerank_kdet_spaced2_64_20260420_082149_5c9bb19a82ab/v15_master_20260420_082149_5c9bb19a82ab.jsonl`

Lecture (résultat “publisable” au niveau Phase A2) :

> Sous `profile=solid`, pour `n=8,12,16` et `seed=0..4`, le groupe de référence `z=n` ferme strictement (IID ∪ OOD) avec barrières valides,
> baselines à 0, ablation à 0, swap-follow à 1.0, swap-orig à 0.0 ; et des groupes `z<n` échouent strictement sur l’image-barrier.

Table (min sur seeds 0..4, deux splits, sous-capacité : `A_img_min`) :

| `n` | `z=n` (réf) | `z<n` testés | Sous-capacité : `A_img_min` (IID/OOD) |
|---:|:--:|:--|:--|
| 8  | PASS | `z=7`, `z=4`  | `0.9531/0.9531`, `0.6875/0.7031` |
| 12 | PASS | `z=11`, `z=6` | `0.9844/0.9844`, `0.8125/0.8438` |
| 16 | PASS | `z=15`, `z=8` | `0.9844/0.9844`, `0.9375/0.9375` |

## 3) Roadmap (ordre recommandé)

### Phase A — Fermer la loi en `n` (d’abord stabilité locale, puis montée en échelle)

**But :** passer de “cas convaincant” à “loi stable quand `n` varie”, sans confondre (i) vérité de la loi et (ii) contraintes de budget/architecture quand `n` grandit.

#### Phase A1 — Stabilité forte locale (`n = 3,4,5,6`)

0. **Verrou “barrière” (précondition non négociable).** Pour chaque valeur testée de `n` (et pour IID *et* OOD),
   exiger que le témoin instancie bien la barrière visée :
   - les paires “obs-only” doivent être réellement indiscernables par l’interface (observable égal),
   - et la vérité ciblée doit réellement différer (séparation réelle par le test).
   Autrement dit, les sanity checks `obs_*_barrier_ok` doivent être `true` dans le groupe de référence.
   Si ce verrou échoue (collisions / dégénérescence du test), on **ne** mesure pas la loi : on doit corriger le témoin.

0b. **Injectivité du test (anti-collisions).** En particulier, garantir que l’encodage de la classe cachée `h`
    dans la cible (ou l’objet à prédire) reste **injectif dans le régime IID** (et pas seulement en OOD).
    Interdire les codages de type “`h mod largeur_disponible`” qui peuvent collisionner quand `n` grandit.

1. Fixer `n ∈ {3,4,5,6}`.
2. Pour chaque `n`, tester `z ∈ {n, n-1, ⌊n/2⌋}` (au minimum deux niveaux `z<n`).
3. Exiger le même verdict strict sur IID ∪ OOD, multi-seeds.

**DONE(A1)** quand on obtient, pour **tous** `n ∈ {3,4,5,6}` :

- `z=n` : OK (spine complet),
- `z<n` : FAIL (au moins deux niveaux),
- et les causal gates passent pour `z=n`.

#### Phase A2 — Montée en échelle (`n = 8,12,16`)

1. Tester `n ∈ {8,12,16}`.
2. Même grille `z ∈ {n, n-1, ⌊n/2⌋}` et mêmes exigences de verifier.

**DONE(A2)** quand le pattern `z=n` OK / `z<n` FAIL reste stable sur au moins deux valeurs de `n` ≥ 8, sans dégrader les critères (IID ∪ OOD, multi-seeds, causal gates).

### Phase B — Fermer la loi sur plusieurs familles de tâches (au moins 3 grammaires)

**But :** montrer que l’invariant n’est pas un artefact “occluder+cue+marks”.

Définir au moins **2 nouvelles familles** réellement différentes.

Familles candidates déjà préparées :

- `v16_phaseB_temporal_zigzag_64` (**temporel discret**) : vérité dynamique = trajectoire zigzag de longueur `horizon` ; OOD = horizons plus longs + bruit de fond non porteur de `h`.
- `v17_phaseB_symbolic_orbit_64` (**structure non-occlusion**) : vérité dynamique = orbite de points sous une dynamique affine ; OOD = horizons plus longs + densité de bruit plus élevée.

Chaque famille doit réimplémenter : barrières, min-lift, causal gates.

**DONE(B)** quand Phase A est reproduite sur au moins 2 familles supplémentaires (mêmes critères).

### Phase B’ — Contrôles négatifs (anti-artifacts obligatoires)

**But :** montrer que le phénomène **ne survit pas** quand on casse la structure pertinente (renforcer la falsifiabilité et éviter les lectures “artefact de benchmark”).

Pour chaque famille (y compris la famille actuelle), ajouter un paquet de contrôles négatifs qui doivent **échouer** au verifier strict :

- cue brouillé (ou cue supprimé) avec le reste inchangé,
- image brouillée (ou image supprimée) avec le reste inchangé,
- permutation **aléatoire** de `z` (doit casser la réussite),
- “coordonnées présentes” mais cue supprimé (éviter les canaux parasites),
- capacité augmentée côté baseline **sans** médiateur (ne doit pas contourner la barrière),
- randomisation des associations symbole→cible (doit détruire la règle).

**DONE(B’)** quand ces contrôles échouent de manière reproductible (multi-seeds), tout en conservant la réussite du test positif correspondant.

### Phase C — Fermer la loi sur plusieurs classes de solveurs (robustesse modèle)

**But :** éviter que le phénomène dépende d’un solveur “aidé” (extraction trop spécialisée).

Pour chaque famille, tester au moins 3 solveurs :

1. **Solveur S_det** (référence / témoin) : canal médiateur rendu très fiable (comme `vN3b`).  
   Statut : **solveur témoin** utile pour isoler le phénomène, mais **ne doit pas porter seul** la prétention d’universalité.
2. **Solveur S_learned** : extraction apprise (plus générique), même objectif/verifier.
3. **Solveur S_alt** : architecture différente (mémoire explicite / autre décodeur / autre inductive bias).

**DONE(C)** quand le spine (barrières + min-lift + causal gates) est stable sur ≥2 solveurs non-identiques, en donnant la priorité à `S_learned` et `S_alt` comme support principal de robustesse.

### Phase D — Converse / normal form (caractérisation abstraite partielle)

**But :** passer de “familles qui réalisent la théorie” à “classe abstraite couverte”.

Livrables attendus :

- une définition abstraite (spécification) du type de tâche/fibre-barrière visée (conditions structurelles),
- un théorème (ou au minimum une conjecture + preuves partielles) :  
  “toute tâche satisfaisant ces conditions admet un témoin de type ‘min-lift + causal signature’”.
- contrainte d’écriture : la classe abstraite doit être formulée **sans référence** aux détails d’implémentation (pas de “marker 2x2”, “occluder carré”, “argmax déterministe”, etc.), uniquement en termes de : fibre d’observables, séparation de compatibilité future, existence d’un médiateur fini, et signatures interventionnelles.

**DONE(D)** quand une classe abstraite est écrite + au moins un résultat “converse partiel” est fermé (même si la complétude totale reste ouverte).

## 4) Livrables concrets (fichiers et sorties)

Pour éviter l’ambiguïté, chaque phase doit produire :

- un `README_...md` (protocole + commandes),
- un `verify_...py` strict (verdict binaire),
- un `campaign_...py` (orchestration multi-seeds / grille `n,z`),
- un document `RESULTS_AND_INTERPRETATION_...md` avec un tableau de runs auditables,
- des runs dans `Empirical/aslmt/runs/` avec `train_*.txt`, `verify_*.txt`, `*_master_*.jsonl`.

## 5) Gouvernance expérimentale (règles non-négociables)

- Ne pas modifier un script historique ayant produit un résultat cité.
- Toute variante = nouveau fichier (suffixe timestamp+hash).
- Outputs (`jsonl`, `txt`) portent le même suffixe timestamp+hash que le script exécuté.
- Un verifier strict ne doit pas “adoucir” le verdict : on garde des conditions binaires type “min=1.0 / max=0.0”.

## 6) Prochaines actions (immédiates)

1. Définir le **test unique consistant** (verifier) qui agrège :
   - double barrière (à la `v8`),
   - min-lift (à la `vN3b`),
   - causal gates (ablation + swap),
   - IID ∪ OOD, pair-grade.
   Et ajouter explicitement les **préconditions de validité** :
   - sanity barrière `obs_*_barrier_ok == true` dans le groupe de référence (IID *et* OOD),
   - pas de collisions (injectivité du test) lorsque `n` varie.
2. Lancer **Phase A1** : `n ∈ {3,4,5,6}` et `z ∈ {n, n-1, ⌊n/2⌋}` sur `seed=0..4`.
3. Fixer un **solveur learned de référence** pour la fermeture (ex. `posloss + pairrank` s’il ferme là où `posloss` seul est instable),
   et garder la contrainte : un solveur témoin “aidé” ne doit pas porter seul l’universalité.
4. Ajouter les **contrôles négatifs** (Phase B’) au même verifier, et documenter “tests positifs” vs “anti-artifacts”.
5. Documenter les résultats dans un tableau unique pointant vers les runs.
