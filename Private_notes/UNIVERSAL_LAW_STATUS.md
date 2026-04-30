# Loi universelle (statut) — clôture relative, pertes d’incidence, médiation

Date : 2026-04-29

Ce fichier fixe, **de manière explicite et falsifiable**, ce qui est déjà établi, ce qui est seulement candidat, et ce qui reste à fermer pour pouvoir dire “loi universelle” au sens du projet.

---

## 0) Résumé exécutif (sans rhétorique)

1) Le projet contient déjà une **loi candidate** stable (formalisable) : la vérité cible n’est pas une propriété “absolue”, elle est relative à une **interface** ; la résolution est un problème de **clôture** (factorisation) ; la médiation/query est un opérateur qui **étend** l’interface.

2) Le cœur mathématique du régime “multi-interface” est une identité d’incidence :

- conjonction de vues (meet) ⟶ **intersection** des pertes
- accessibilité conjointe ⟶ **union** des accessibilités
- clôture conjointe ⟷ **perte résiduelle nulle**

3) Les preuves Lean ferment des briques structurelles (no-go marginal, médiateur joint fini, minimalité, non-descente) et donnent une sémantique “quotient/partition” précise.

4) Les tests empiriques ferment un **contrat causal** : la réussite suit la médiation et s’effondre sous ablation/swap, avec barrières + baselines + IID/OOD + multi-seeds + vérifieurs stricts.

5) “Loi universelle” au sens fort (“fermée définitivement”) exige encore une clôture de portée : définir exactement la classe de cibles/interfaces autorisées, prouver les théorèmes au bon niveau d’abstraction, et exécuter une batterie de stress-tests (multi-familles + multi-n + OOD + seeds) qui interdit les lectures parasitaires.

---

## 1) Dictionnaire minimal : objets, interfaces, clôture

On travaille (dans les protocoles empiriques) sur des instances finies. Le vocabulaire ci-dessous est “sans perte” pour ce régime.

### 1.1 États latents, interface, vérité cible

- `X` : ensemble d’états latents.
- `O : X → V` : interface observable (“ce qui est vu”).
- `σ : X → Y` : signature / vérité cible (“ce qui doit être décidé”).

### 1.2 Partitions / relations d’équivalence

Une interface induit une partition :

- `E_O := Ker(O)` (relation : `x ~ x'` ssi `O(x)=O(x')`).

Une signature induit une partition dynamique :

- `E_σ := Ker(σ)` (mêmes signatures).

### 1.3 Clôture (définition structurelle)

Clôture de `σ` sur `O` :

- `σ` est fermée sur `O` ⟷ `E_O ⊆ E_σ`.

Lecture équivalente (factorisation) :

- `σ` est fermée sur `O` ⟷ il existe `f : V → Y` tel que `σ = f ∘ O`.

Non-clôture (témoin diagonal) :

- `E_O ⊄ E_σ` ⟷ il existe `x,x'` avec `O(x)=O(x')` mais `σ(x)≠σ(x')`.

Le témoin diagonal est le point qui rend l’objet **falsifiable** : il produit une obstruction explicite.

---

## 2) Algèbre des distinctions : pertes, accessibilités, incidence

Cette couche encode la “vraie arithmétique” du diagnostic de clôture : on calcule dans un espace de distinctions, puis on cardinalise à la fin.

### 2.1 Espace des distinctions

Pour `X` fini, poser :

- `ΔX := { {x,x'} | x ≠ x' }` (paires non ordonnées).

### 2.2 Distinctions requises par la signature

Poser :

- `R_σ := { {x,x'} ∈ ΔX | σ(x) ≠ σ(x') }`.

`R_σ` est le “total pertinent” : ce sont les distinctions qui comptent pour décider `σ`.

### 2.3 Confusions induites par une interface (partition)

Pour une partition `E` sur `X` :

- `C_E := { {x,x'} ∈ ΔX | x ~_E x' }` (distinctions confondues).
- `D_E := ΔX \ C_E` (distinctions accessibles par `E`).

### 2.4 Pertes relatives à `σ` et accessibilités relatives à `σ`

Perte requise par une interface `E` :

- `L_σ(E) := R_σ ∩ C_E`.

Accessibilité relative :

- `Acc_σ(E) := R_σ \ L_σ(E) = R_σ ∩ D_E`.

### 2.5 Invariant résiduel (quantité de non-clôture)

Pour une famille de vues (interfaces) `(E_i)`, poser :

- résidu des pertes : `L_res(I) := ⋂_{i∈I} L_σ(E_i)`,
- invariant résiduel : `ρ_σ(I) := # L_res(I)`.

Interprétation :

- `ρ_σ(I)` mesure la quantité de distinctions requises encore perdues après conjonction des vues dans `I`.

### 2.6 Loi d’incidence centrale (multi-interface)

Pour des partitions `E_i` :

- `L_σ(⋀_{i∈I} E_i) = ⋂_{i∈I} L_σ(E_i)`.
- `Acc_σ(⋀_{i∈I} E_i) = ⋃_{i∈I} Acc_σ(E_i)`.

Conséquence (critère de clôture conjointe) :

- `σ` est fermée sur `⋀_{i∈I} O_i` ⟷ `L_res(I)=∅` ⟷ `ρ_σ(I)=0`.

Cette identité est le cœur “arithmétique” : le meet des interfaces devient une intersection de pertes ; la décision est l’annulation de l’intersection.

---

## 3) Version dynamique : boucle de requêtes et contraction du résidu

### 3.1 Transcript et conjonction progressive

Dans une boucle active, on a une famille croissante de vues requêtées :

- `I_0 := {base}`
- `I_{t+1} := I_t ∪ {a_t}` (vue/action choisie à l’étape `t`)

### 3.2 Équation dynamique (forme exacte)

Le résidu se met à jour par :

- `L_res(I_{t+1}) = L_res(I_t) ∩ L_σ(E_{a_t})`.

Donc :

- `ρ_{t+1} = # (L_res(I_t) ∩ L_σ(E_{a_t}))`.

### 3.3 Gain marginal d’une requête (forme exacte)

Le gain d’une vue `j` relativement au résidu courant `I` :

- `Δ_j(I) := # (L_res(I) \ L_σ(E_j))`
- équivalent : `Δ_j(I) = # (L_res(I) ∩ Acc_σ(E_j))`.

La politique “idéale” maximise `Δ_j(I_t)` à chaque pas (règle greedy).

Dans les variantes STRONG, la règle correcte est “à horizon” (DP/planification) : le score local est insuffisant au premier pas parce que plusieurs vues ont le même gain local.

---

## 4) Ce que le projet appelle “médier / requêter”

### 4.1 Définition opérationnelle (sans proba)

Le solveur fonctionne en boucle :

1) une interface courante `O_t` ne clôture pas la cible (`E_{O_t} ⊄ E_σ`) ;
2) l’échec fournit un témoin (diagonalisation / séparation intra-fibre) ;
3) ce témoin prescrit une action/requête qui change l’accès (`O_{t+1} = O_t ∧ O_{a_t}`) ;
4) la décision est prise quand la clôture est atteinte (`ρ_t = 0`).

### 4.2 Causalité interne (rôle de `z`)

Le médiateur discret `z` est traité comme variable interventionnelle :

- ablation `z→0` : effondrement,
- swap `z` : l’action suit le `z` permuté, et la performance suit l’intervention,
- barrières + baselines : empêchent que la réussite vienne d’un canal visible-only ou cue-only.

Cela transforme un “score final” en **audit causal interne** : l’architecture doit réellement utiliser la boucle.

---

## 5) Ce qui est “fermé” par Lean (statut formel)

La couche Lean rend explicite :

1) **clôture = factorisation** (et non slogan),
2) **témoin diagonal** = obstruction constructible,
3) **médiation finie** = existence d’un médiateur discret `Fin n`,
4) **minimalité** = pas de médiateur plus petit,
5) **non-descente** = irréductibilité marginale.

Fichiers (références de lecture) :

- `/mnt/c/Users/frederick/Documents/forU2read/COFRS/Examples/ReferentialInduction.lean`
- `/mnt/c/Users/frederick/Documents/forU2read/COFRS/Examples/IndependenceRelationMediationChain.lean`
- `/mnt/c/Users/frederick/Documents/forU2read/COFRS/Dynamics.lean`
- `/mnt/c/Users/frederick/Documents/forU2read/COFRS/Examples/AutoreflexiveQueryArchitecture.lean`

Ce que Lean garantit ici : l’alignement “définitions ↔ théorèmes ↔ implications” est exact (pas seulement “ça compile”).

---

## 6) Ce qui est “fermé” empiriquement (statut expérimental)

### 6.1 Ce que veut dire “fermé” côté tests

Un protocole est fermé empiriquement (au standard du projet) quand :

- barrières : la base seule maintient l’ambiguïté,
- baselines : visible-only/cue-only restent à chance,
- ablation/swap : l’intervention sur `z` casse précisément la réussite,
- IID + OOD : le pattern survit à des shifts définis,
- multi-seeds : répétabilité,
- vérifieur strict : seuils + identité de protocole.

### 6.2 v18 strong v3 (run solid fermé)

Le run solid complet (n=64, seeds 0..4) est enregistré ici :

- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v18_algebra_multistep_64_strong_v3/README_aslmt_v18_algebra_multistep_64_strong_v3.md`

Run directory :

- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v18_algebra_multistep_64_strong_actionz_v3_solid_20260429_064727_e18711f98bbc`

Master JSONL :

- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v18_algebra_multistep_64_strong_actionz_v3_solid_20260429_064727_e18711f98bbc/v18_algebra_multistep_64_strong_actionz_v3_solid_master_20260429_064727_e18711f98bbc.jsonl`

Fait brut : `A_acc = 1.0` (IID+OOD, min-seeds=5), baselines ~chance, ablation/swap ~chance, follow-rate=1.0.

### 6.3 v19 universal v2 (objectif)

Le but de v19 n’est pas “un benchmark de plus”.
Le but est d’imposer une contrainte de portée : “stop-on-closure, multi-family, horizon-consistent”, et de conserver les audits.

Fichier :

- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v19_algebra_universal_v2/README_aslmt_v19_algebra_universal_v2.md`

### 6.3.1 v19 universal v2 (run solid terminé, n=64, seeds 0..4)

Run directory :

- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v19_algebra_universal_actionz_v2_solid_20260429_103226_a7792f68e826`

Master JSONL :

- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_v19_algebra_universal_actionz_v2_solid_20260429_103226_a7792f68e826/v19_algebra_universal_actionz_v2_solid_master_20260429_103226_a7792f68e826.jsonl`

Agrégats (5 seeds) :

```text
IID:
  A_acc  : min=1.0000 max=1.0000 mean=1.0000
  B_vis  : min=0.4775 max=0.5273 mean=0.4982
  B_cue  : min=0.5049 max=0.5518 mean=0.5256
  A_abl  : min=0.6631 max=0.6875 mean=0.6727
  A_swap : min=0.6660 max=0.6865 mean=0.6752
  follow : min=1.0000 max=1.0000 mean=1.0000

OOD:
  A_acc  : min=1.0000 max=1.0000 mean=1.0000
  B_vis  : min=0.4805 max=0.5400 mean=0.5068
  B_cue  : min=0.4961 max=0.5439 mean=0.5098
  A_abl  : min=0.6504 max=0.6748 mean=0.6617
  A_swap : min=0.6426 max=0.6631 mean=0.6539
  follow : min=1.0000 max=1.0000 mean=1.0000
```

### 6.3.2 Interprétation correcte (ce que v19 v2 valide / ne valide pas)

Ce run valide **fortement** :

- la construction “stop-on-closure” (candidat `F_τ` + `Amb_σ(F_τ)`),
- l’oracle horizon-aware (DP) comme supervision,
- la reproductibilité (multi-seeds + IID/OOD + vérifieur).

Mais v19 v2 ne ferme pas encore le “contrat causal z” au standard de v18 strong :

- `A_abl_acc` et `A_swap_acc` restent élevés (~0.65–0.69), donc l’intervention sur `z` ne casse pas jusqu’à la chance.

Raison structurelle (non polémique) :

- dans v19 v2, `modelA.logits_query` appelle directement l’oracle (features exactes),
- et `modelA.predict_y` est une référence constructive (calcul exact via masque candidat).

Donc v19 v2 est une **démonstration constructive oracle-wrapper** : elle prouve que le protocole et l’oracle pilotent correctement la fermeture, mais elle ne prouve pas encore que la politique “apprend la structure” ni que `z` est strictement nécessaire.

---

## 7) La loi universelle : ce que le projet vise exactement

### 7.1 Ce que “loi universelle” ne veut pas dire

“Loi universelle” ne veut pas dire “un solveur résout tous les problèmes”.
Le projet cible une universalité structurée : universalité sur une classe de problèmes définie par la clôture relative et la possibilité d’extension d’interface.

### 7.2 Ce que “loi universelle” veut dire (version falsifiable)

Une formulation correcte (au standard du projet) prend la forme :

1) **Classe d’objets** : cibles `σ`, interfaces `O_i`, opérations autorisées (meet/extension/query), témoins admissibles.
2) **Théorème de classification** : partition des régimes (clôture passive / non-clôture / clôture active / non-fermable).
3) **Invariants** : `L_σ`, `Acc_σ`, `ρ_σ`, `Δ`.
4) **Règle de résolution** : politique qui réduit `ρ` jusqu’à 0 (greedy ou horizon).
5) **Audits** : interdiction des canaux parasites + stabilité IID/OOD + multi-seeds.

### 7.3 Statut actuel

Le projet possède déjà :

- les définitions (clôture, témoin, médiateur, non-descente),
- l’algèbre des pertes/incidence (multi-interface),
- des protocoles empiriques fermés sur des familles synthétiques,
- un standard d’audit causal interne.

Ce que le projet ne possède pas encore au sens “fermé définitivement” :

- une statement unique qui fixe la portée finale (“universelle” relativement à quelle classe d’extensions ?),
- une preuve Lean au niveau d’abstraction final pour cette portée,
- une batterie empirique qui couvre plusieurs familles orthogonales + plusieurs tailles `n` + OOD + seeds, avec un vérifieur unique consolidé.

---

## 8) Check-list de clôture finale (sans ambiguïté)

Pour pouvoir écrire “loi universelle” sans contestation de périmètre, il faut produire un paquet final avec :

1) **Spécification** : définitions + portée + régimes (un fichier maître).
2) **Lean** : théorèmes au bon niveau (pas de glissement sémantique).
3) **Empirique** : suite de runs solid multi-familles + multi-n + OOD + seeds.
4) **Audit** : ablation/swap + barrières + baselines + identity checks dans les vérifieurs.
5) **Reproductibilité** : snapshots hashés + masters JSONL + commandes exactes.

---

## 9) Annexes : où lire le mécanisme “algèbre → architecture” (mermaid)

- `/mnt/c/Users/frederick/Documents/forU2read/Private_notes/ALGEBRA_SOLVER_MERMAID.md`
- `/mnt/c/Users/frederick/Documents/forU2read/Private_notes/ALGEBRA_SOLVER_MERMAID_EN.md`

Ces docs rendent explicite le pont :

```text
distinctions → pertes → incidence → ρ/Δ → oracle → supervision → policy → audits causaux
```

---

## 10) Conclusion nette

Le projet ne possède pas “la loi universelle” au sens **clôture totale et définitive**.

Le projet possède déjà une **loi candidate** formelle (clôture relative + algèbre d’incidence des pertes + dynamique de réduction du résidu) et des fermetures locales fortes (Lean + v18 strong v3 solid).

Le travail restant est une clôture de portée : statement final + preuves au bon niveau + batterie empirique consolidée.
