# Autoreflexivite et autoreference

But
regrouper les ancrages (code, verifieur, runs) pour auto reflexivite et auto reference.

Ce fichier a deux niveaux:
1) niveau design architecture: ce que ces mots veulent dire dans votre cadre general (referentiel, quotient, diagonalisation, mediation)
2) niveau validation tests: comment ces proprietes sont operationalisees et verifiees (code, verifieur, runs)

## 1) Definitions operationnelles (strictement celles des tests)

Dans ce document, "autoreflexivite" et "autoreference" sont prises au sens strictement operatoire des tests.
Il ne s agit pas ici de redefinir le phenomene fondamental.
Il s agit de fixer comment ces proprietes sont attestees dans le projet par code, verifieur, et runs.

Autoreflexivite
un choix d action est produit a partir de l etat interne du modele, et ce choix modifie ensuite ce qui est observe ou decide.

Autoreference (sens operatoire des tests, mediateur mis a l epreuve par base, ablation, swap)
la decision pertinente passe par un mediateur interne du systeme.
dans ce document, cette propriete est tenue pour attestee lorsque le protocole definit ce mediateur et calcule, sur les memes cas:
base, ablation, swap.

Swap se lit toujours en deux scores:
- swap_vs_orig: performance du swap evaluee sur les labels originaux
- swap_vs_perm: performance du swap evaluee sur les labels permutes

Dans ces tests, si l objet interne est load bearing au sens operatoire, indicateurs attendus:
- ablation_drop fort
- swap_vs_perm eleve
- swap_vs_orig degrade

## 1.1) Gradation des cas (force d attestation)

Autoreflexivite (etat interne vers action vers observation ou decision)
- law_v3b
- aslmt_v2

Autoreference explicite (mediateur interne nomme et sortie state locked sur ce mediateur)
- law_v5b

Autoreference operatoire (interventions sur le mediateur dans le pair eval, clauses base, ablation, swap)
- v7 (spec implementee, pas de master jsonl present dans Empirical/aslmt/runs pour le variant single)
- v8
- vN3b
- v9

## 2) Sens design architecture (referentiel, quotient, sujet)

Cadre general
un referentiel est ici un quotient suffisamment expressif pour rendre formulables:
1) une interface de decision (ce qui est tenu pour visible)
2) une verite dynamique visee
3) une diagonalisation au sens intra fibre (variation de la verite dynamique a visible fixe)

Sujet (sens referentiel)
un quotient est dit "sujet" au sens referentiel lorsqu il est suffisamment structure pour rendre formulables, dans ce cadre:
1) l indiscernabilite visible (classes de quotient)
2) la verite dynamique visee
3) une separation diagonale eventuelle de cette verite a visible fixe

Lien structurel (formulation propre, alignee projet)
referentiel: cadre qui fixe le quotient (indiscernabilite), l interface de decision, et la verite dynamique visee.
auto reference: propriete de systeme relative a ce cadre (decision via mediateur interne non contenu dans les marginales).
auto reflexivite: propriete de systeme relative a ce cadre (etat interne vers action de requete vers nouveau regime d observation ou decision).

Auto reference (sens design)
le systeme porte en interne la mediation necessaire pour fermer une decision que les marginales ne ferment pas.
operatoirement, cela correspond aux protocols ou la decision suit un mediateur manipulable (base, ablation, swap).

Auto reflexivite (sens design)
le systeme utilise son etat interne pour choisir une action qui change ensuite son acces au probleme.
operatoirement, cela correspond aux protocols de type query: etat interne vers action vers nouvelle observation vers decision.

## 3) law_v3b (hard OOD masks query POMDP)

Ce test atteste explicitement l autoreflexivite (choix d action) et l autoreference (audit sur etat interne).

Autoreflexivite

Le modele A choisit une action de requete a partir de son propre etat memoire `mem_for_query`:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:59`.

Le choix passe par `logits_q = model.logits_query(mem_for_query)` puis selection `a_hi`, puis appel environnement:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:60`
et
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:68`.

Anti bypass explicite
le token visible `lo_tok` n est pas injecte dans la memoire avant la requete:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:56`.

Autoreference (audit direct sur etats memoire)

L audit causal est une fonction explicite, et elle manipule des objets memoire:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:135`.

Le swap est un swap sur `mem_out`:
`mem_out_swapped = base['mem_out'][perm]` et metriques swap_vs_orig, swap_vs_perm:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:145`.

Verif (clauses verrouillees)

Le verifieur impose schema et kind uniques, puis exige des seuils sur ablation et swap:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/verify_aslmt_campaign_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:35`
et verifie des bornes sur `min_ablation_drop`, `max_swap_vs_orig`, `min_swap_vs_perm`:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/verify_aslmt_campaign_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:126`.

Resultats (master jsonl existant)

`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_law_v3b_20260408_171512_f299c7d9e94a/master_20260408_171512_f299c7d9e94a.jsonl`
contient, dans `iid.audit` et `ood.audit`, les champs:
`base_success`, `ablate_success`, `ablation_drop`, `swap_vs_orig`, `swap_vs_perm`.

Procedure de verification (a executer)

- `python3 -u /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/verify_aslmt_campaign_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py --master-jsonl /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_law_v3b_20260408_171512_f299c7d9e94a/master_20260408_171512_f299c7d9e94a.jsonl`

## 4) aslmt_v2 (autoreflective query POMDP no aids)

Run present (master jsonl).
Les metriques du master jsonl montrent le pattern d audit (ablation_drop et swap_vs_perm).

Resultats (master jsonl existant)

`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v2_20260404_195247_f09b861728b9/master_20260404_195247_f09b861728b9.jsonl`
contient `kind = aslmt_v2_autoreflective_query_pomdp_no_aids` et, dans `iid.audit` et `ood.audit`:
`ablation_drop`, `swap_vs_perm`, `swap_vs_orig`.

Etat snapshot (factuel)
snapshot associe present dans `Empirical/aslmt/runs/snapshots`: non.

Pointeurs code et verif
non disponibles ici via snapshot (donc pas d ancrage code et verif dans ce document pour v2).

## 5) law_v5b (amodal localclass)

Ce test est une forme explicite d autoreference (mediateur interne `z` avec ablation et swap).
Ce n est pas un test d autoreflexivite, car il n y a pas d action de requete.

Autoreference (mediateur explicite et state locked)

La sortie A est decodee uniquement depuis `z`:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v5b_amodal_localclass/aslmt_model_law_v5b_amodal_localclass.py:121`.

Swap explicite sur `z`:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v5b_amodal_localclass/aslmt_model_law_v5b_amodal_localclass.py:126`.

Audit ablation et swap sur batch OOD:
`z_zero` et `swap_forward`:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v5b_amodal_localclass/aslmt_train_law_v5b_amodal_localclass_family.py:167`.

Verif (clauses verrouillees)

Le verifieur strict refgate impose notamment des bornes sur:
`ood.audit.ablation_drop`, `ood.audit.swap_vs_perm`, `ood.audit.swap_vs_orig`:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v5b_amodal_localclass/verify_aslmt_campaign_law_v5b_amodal_localclass_family_strict_refgate.py:171`.

Resultats (master jsonl existant)

`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_law_v5b_amodal_localclass_20260411_083117_843fe3a41e75/master_20260411_083117_843fe3a41e75.jsonl`
contient, dans `ood.audit`, les champs:
`ablation_drop`, `swap_vs_orig`, `swap_vs_perm`.

Procedure de verification (a executer)

- `python3 -u /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v5b_amodal_localclass/verify_aslmt_campaign_law_v5b_amodal_localclass_family_strict_refgate.py --master-jsonl /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_law_v5b_amodal_localclass_20260411_083117_843fe3a41e75/master_20260411_083117_843fe3a41e75.jsonl`

## 6) v7_descriptive (perfect amodal hidden target)

Ce test atteste l autoreference au sens operatoire des tests (audit sur `z`).

Autoreference (audit ablation et swap sur `z`)

Le modele expose explicitement les deux hooks:
`swap_forward` et `ablated_forward`:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v7_descriptive/aslmt_model_v7_perfect_jepa.py:126`
et
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v7_descriptive/aslmt_model_v7_perfect_jepa.py:132`.

`ablated_forward` et `swap_forward` sont appeles dans les audits:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v7_descriptive/variants/single/aslmt_train_v7_perfect_amodal_hidden_target_seeded.py:111`
et
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v7_descriptive/variants/single/aslmt_train_v7_perfect_amodal_hidden_target_seeded.py:113`.

Verif (clauses verrouillees)

Le verifieur impose des seuils sur `ablation_drop`, `swap_vs_orig`, `swap_vs_perm`:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v7_descriptive/variants/single/verify_aslmt_v7_perfect_amodal_hidden_target.py:38`.

Etat run (factuel)
master jsonl present dans `Empirical/aslmt/runs`: non.

Procedure de verification (a executer)

- entrainement: `python3 -u /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v7_descriptive/variants/single/aslmt_train_v7_perfect_amodal_hidden_target_seeded.py --device cuda --out-jsonl /tmp/v7_single_master.jsonl`
- verif: `python3 -u /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v7_descriptive/variants/single/verify_aslmt_v7_perfect_amodal_hidden_target.py --master-jsonl /tmp/v7_single_master.jsonl`

## 7) v8_descriptive (double barrier causal gates)

Ce test atteste l autoreference au sens des tests par interventions sur le mediateur definies dans le pair eval.
Les causal gates sont la clause verifiee sur les paires image barrier.

Fichiers clefs
- train: `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v8_descriptive/aslmt_train_v8_double_barrier_hidden_target_seeded_pair_trainood_causalgate.py`
- verif: `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v8_descriptive/verify_aslmt_v8_double_barrier_hidden_target_pair_oodrequired_causalgate.py`

Definition barriere (diagonalisation protocolaire)

Image barrier et cue barrier sont verifiees sur les rendus:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v8_descriptive/aslmt_train_v8_double_barrier_hidden_target_seeded_pair_trainood_causalgate.py:85`
et
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v8_descriptive/aslmt_train_v8_double_barrier_hidden_target_seeded_pair_trainood_causalgate.py:93`.

Autoreference (ablation et swap sur le mediateur)

`ablated_forward` est utilise sur la paire image barrier:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v8_descriptive/aslmt_train_v8_double_barrier_hidden_target_seeded_pair_trainood_causalgate.py:122`.

`swap_forward` est utilise avec permutation, puis on mesure follow vs orig:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v8_descriptive/aslmt_train_v8_double_barrier_hidden_target_seeded_pair_trainood_causalgate.py:128`
et les criteres follow vs orig sont calcules:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v8_descriptive/aslmt_train_v8_double_barrier_hidden_target_seeded_pair_trainood_causalgate.py:157`.

Verif (clauses verrouillees, contrat strict 1.0)

Le verifieur causal gate exige:
- barrier ok
- A_img_min = 1.0, A_cue_min = 1.0
- A_abl_img_max = 0.0
- A_swap_follow_min = 1.0
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v8_descriptive/verify_aslmt_v8_double_barrier_hidden_target_pair_oodrequired_causalgate.py:34`.

Resultats (master jsonl existant)

`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v8_pair_oodrequired_causalgate_20260414_174655_217093f0f527/v8_master_20260414_174655_217093f0f527.jsonl`

Procedure de verification (a executer)

- `python3 -u /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v8_descriptive/verify_aslmt_v8_double_barrier_hidden_target_pair_oodrequired_causalgate.py --master-jsonl /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v8_pair_oodrequired_causalgate_20260414_174655_217093f0f527/v8_master_20260414_174655_217093f0f527.jsonl`

## 8) vN3b_descriptive (min lift + causal gates)

Ce test ajoute la quantification min lift via `z_classes` et la supervision explicite de `h -> z_logits`.
Il atteste l autoreference au sens des tests par ablation et swap definis dans le pair eval.

Fichiers clefs
- train: `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/vN3b_descriptive/aslmt_train_vN3b_minlift_double_barrier_seeded_pair_trainood.py`
- verif: `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/vN3b_descriptive/verify_aslmt_vN3b_minlift_double_barrier_pair_oodrequired.py`

Autoreference (ablation et swap, pair eval)

`ablated_forward` et `swap_forward` sont utilises dans le pair eval:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/vN3b_descriptive/aslmt_train_vN3b_minlift_double_barrier_seeded_pair_trainood.py:146`
et
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/vN3b_descriptive/aslmt_train_vN3b_minlift_double_barrier_seeded_pair_trainood.py:152`.

Min lift (supervision de `z_logits`)

`z_logits = modelA.z_logits(cue)` et `lossA_z = cross_entropy(z_logits, h mod z_classes)`:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/vN3b_descriptive/aslmt_train_vN3b_minlift_double_barrier_seeded_pair_trainood.py:274`.

Verif (clauses verrouillees)

Le verifieur regroupe par `z_classes` et impose:
ref (z = n) doit etre parfait sur barrier et causal gates, et tout z < n doit echouer sur image barrier:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/vN3b_descriptive/verify_aslmt_vN3b_minlift_double_barrier_pair_oodrequired.py:34`
et checks ref sur swap/ablation:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/vN3b_descriptive/verify_aslmt_vN3b_minlift_double_barrier_pair_oodrequired.py:122`.

Resultats (master jsonl existant)

`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_vN3b_minlift_20260414_210841_ec5fdeec7e43/vN3b_master_20260414_210841_ec5fdeec7e43.jsonl`

Procedure de verification (a executer)

- `python3 -u /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/vN3b_descriptive/verify_aslmt_vN3b_minlift_double_barrier_pair_oodrequired.py --master-jsonl /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_vN3b_minlift_20260414_210841_ec5fdeec7e43/vN3b_master_20260414_210841_ec5fdeec7e43.jsonl --n-classes 4 --profile solid --min-seeds 3`

## 9) v9_unified (double barrier + min lift n scalable)

Ce test est le witness unifie: double barriere, min lift, et causal gates.
Il atteste l autoreference au sens des tests par ablation et swap definis dans le pair eval.

Fichiers clefs
- train: `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v9_unified/aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood_posloss_pairrank_imgcuerank_nscalable_kdet_spaced2_64.py`
- verif: `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v9_unified/verify_aslmt_v9_unified_double_barrier_minlift_pair_oodrequired.py`

Barriere (diagonalisation protocolaire)

Image barrier et cue barrier sont verifiees dans le pair eval:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v9_unified/aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood_posloss_pairrank_imgcuerank_nscalable_kdet_spaced2_64.py:256`
et
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v9_unified/aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood_posloss_pairrank_imgcuerank_nscalable_kdet_spaced2_64.py:260`.

Autoreference (ablation et swap)

`ablated_forward` et `swap_forward` sont utilises dans le pair eval:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v9_unified/aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood_posloss_pairrank_imgcuerank_nscalable_kdet_spaced2_64.py:287`
et
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v9_unified/aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood_posloss_pairrank_imgcuerank_nscalable_kdet_spaced2_64.py:293`.

Min lift (supervision de `z_logits`)

`z_logits = modelA.z_logits(cue_xy)` puis `lossA_z = cross_entropy(z_logits, h mod z_classes)`:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v9_unified/aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood_posloss_pairrank_imgcuerank_nscalable_kdet_spaced2_64.py:457`.

Verif (clauses verrouillees)

Le verifieur regroupe par `z_classes` et impose:
ref (z = n) parfait sur barrier et causal gates, tout z < n echoue sur image barrier:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v9_unified/verify_aslmt_v9_unified_double_barrier_minlift_pair_oodrequired.py:34`
et checks swap/ablation:
`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v9_unified/verify_aslmt_v9_unified_double_barrier_minlift_pair_oodrequired.py:122`.

Resultats (master jsonl existant)

`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v9_unified_nscalable_posloss_pairrank_minlift_20260415_144920_a7b90d157360/v9_nscalable_posloss_pairrank_master_20260415_144920_a7b90d157360.jsonl`

Procedure de verification (a executer)

- `python3 -u /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v9_unified/verify_aslmt_v9_unified_double_barrier_minlift_pair_oodrequired.py --master-jsonl /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v9_unified_nscalable_posloss_pairrank_minlift_20260415_144920_a7b90d157360/v9_nscalable_posloss_pairrank_master_20260415_144920_a7b90d157360.jsonl --n-classes 5 --profile solid --min-seeds 3`
