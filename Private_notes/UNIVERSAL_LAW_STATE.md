# État des lieux — Loi universelle (COFRS / Lean + ASLMT / Empirique)

But de cette note : établir un état des lieux précis, exhaustif, et structuré de (i) la **forme** de la loi universelle visée, (ii) ce qui est **déjà fermé** en Lean, (iii) ce qui est **déjà fermé** empiriquement, et (iv) la **visée** (ce qui compte comme fermeture complète).

Date : 2026-04-23

---

## 0) Vocabulaire minimal (référentiel / clôture / diagonale / médiation)

Un **référentiel** (au sens du projet) est un paquet :

- un espace `X` (domaine des états/objets),
- une interface visible `q : X → Q` (ce qui est tenu pour “même visible”),
- une vérité visée `T : X → Prop` (ou une cible décisionnelle équivalente).

Trois notions structurales :

1) **Clôture** (sur le visible)
   - `Closes(R)` : il existe `pred : Q → Prop` tel que `T x ↔ pred (q x)`.

2) **Témoin diagonal** (obstruction dans une fibre)
   - `DiagonalWitness(R)` : il existe `x ≠ x'` avec `q x = q x'` et `T x` diffère de `T x'`.

3) **Médiation finie**
   - `MediatesLe(R, n)` : il existe `σ : X → Fin n` et `predFin : Fin n → Prop` tels que `T x ↔ predFin (σ x)`.

Une notion de **descente** (réduction au visible) :

- `DescendsToQuot(R, σ)` : il existe `f : Q → Fin n` tel que `σ x = f (q x)`.

Une extension canonique :

- `extendQuot(R, σ)` : remplace `q` par `q' x := (q x, σ x)`.

---

## 1) Forme de la loi universelle (énoncé cible)

La loi universelle visée se formule comme une **loi de transition** entre référentiels.

### 1.1 Loi “pas” (réparation forcée)

Pour tout référentiel `R = (X, Q, q, T)` :

- `DiagonalWitness(R)` donne une obstruction de clôture (variation intra-fibre).
- Si une médiation finie correcte existe (`MediatesLe(R, n)` via un médiateur `σ`), alors :
  - `σ` porte une information intra-fibre : `¬ DescendsToQuot(R, σ)`,
  - et l’extension `extendQuot(R, σ)` ferme la vérité courante : `Closes(extendQuot(R, σ))`.

C’est la loi minimale : **obstruction diagonale + médiation correcte ⇒ non-descente + fermeture après extension**.

### 1.2 Loi “chaîne” (induction référentielle)

Une induction n’est pas une indexation par `Nat`/ordinaux ; c’est une **dérivation témoinée** :

- arrêt par clôture,
- continuation par un pas (obstruction + médiateur + preuve de médiation),
- re-ciblage (changement de vérité visée) sur le référentiel étendu,
- discipline du re-ciblage (preuve que la nouvelle cible utilise réellement l’extension).

Cette forme est celle qui se retrouve dans les définitions Lean (voir §2).

---

## 2) Fermeture Lean (structure + chaînes + discipline)

### 2.1 Fichier pivot : `COFRS/Examples/ReferentialInduction.lean`

Chemin : `/mnt/c/Users/frederick/Documents/forU2read/COFRS/Examples/ReferentialInduction.lean`

Ce fichier fixe la loi universelle dans sa forme constructive abstraite :

**(A) Obstruction ⇒ non-clôture**
- `not_closes_of_diagonalWitness : DiagonalWitness(R) → ¬ Closes(R)`

**(B) Obstruction + médiation ⇒ non-descente**
- `not_descends_of_diagonalWitness_of_mediatesLe`

**(C) Médiation ⇒ clôture après extension**
- `closes_extendQuot_of_mediatesLe`

**(D) Paquet “pas” (famille de témoins)**
- `InductionStep` et `InductionStepOn R` transportent explicitement :
  - `diag : DiagonalWitness(R)`,
  - `σ : X → Fin n`,
  - `mediates : ∀x, T x ↔ predFin (σ x)`.
- Les faits dérivés sont exposés :
  - `InductionStep.not_descends`,
  - `InductionStep.closes_extended`.

**(E) Chaîne “mono-cible”**
- `Derivation` : `stop` (par `Closes`) ou `next` (par `InductionStep`).

**(F) Chaîne re-ciblable**
- `StageTransition` : pas `I : InductionStep` + nouvelle cible `Tnext`.
- `ReferentialDerivation` : chaîne avec re-ciblage.

**(G) Discipline du stage suivant (usage effectif de l’extension)**
- `StageTransition.oldView` : l’ancienne vue (quotient ancien) équipée de `Tnext`.
- `UsesExtension` : un témoin diagonal de non-clôture dans `oldView`.
- `DisciplinedStageTransition` + `DisciplinedReferentialDerivation`.

**(H) Transition autoportante (re-ciblage + réparation suivante)**
- `DisciplinedStageTransitionWithRepair` :
  - `J : DisciplinedStageTransition`,
  - `next : InductionStepOn J.Rnext`,
  - lemmes : `next_not_descends`, `next_closes_extended`.

**Audit** : le fichier se termine par un bloc `AXIOM_AUDIT` (zéro axiome, zéro `Classical`).

### 2.2 Instanciation à `Dynamics` (Compatible / StepSeparatesFiber / Sig)

Toujours dans `ReferentialInduction.lean`, section `CompatibleInstantiation` :

- `compatibleProblem` instancie un `ReferentialProblem` à partir de :
  - `Compatible` et d’un `step : Path h k`,
  - sur le domaine fibre-local `FiberPt obs target_obs h`.

Chaîne de réduction principale (version canonique) :

- `StepSeparatesFiber` ⇒ `DiagonalWitness(compatibleProblem ...)`
- Couche `Sig` (médiateur canonique) :
  - `StepSeparatesFiber` interdit toute compression “obs-only” respectant `Sig`.
  - `CompatSigDimLe` ⇒ `RefiningLift` ⇒ données de lift ⇒ extraction d’un `InductionStep`.

Théorème clé :

- `inductionStep_of_compatSigDimLe_of_stepSeparatesFiber` :
  - à partir de `CompatSigDimLe` et `StepSeparatesFiber`,
  - on construit explicitement `∃ I : InductionStep, I.n = n`.

### 2.3 Cycles et terminalité (sans rank, sans well-founded)

Fichier : `/mnt/c/Users/frederick/Documents/forU2read/COFRS/Examples/DisciplinedChainsGlobal.lean`

Ce fichier fixe un cadre “projet” pour parler de chaînes entre référentiels via une relation un-pas :

- `Leadsto : R → R' → Prop` (existe un `DisciplinedStageTransitionWithRepair` qui relie `R` à `R'`).
- `Terminal(Cycle) R := R.Closes ∨ Cycle R`.

Ici, “cycle” est un concept terminal optionnel (p. ex. audit périodique), distinct d’une preuve de terminaison par rang.

---

## 3) Fermeture Lean (bridges vers autoreférence / autoreflexivité query)

La loi universelle a une lecture “architecture” : quand la clôture visible échoue, un régime avec médiation devient nécessaire.
La famille `AutoreflexiveQueryArchitecture` fixe le langage de cette lecture.

### 3.1 Signature query (côté architecture)

Fichier : `/mnt/c/Users/frederick/Documents/forU2read/COFRS/Examples/AutoreflexiveQueryArchitecture.lean`

Rôle :

- spécifier une boucle `preState → chosenAction → returnedResponseUnder → postStateUnder → runUnder`,
- fournir des notions d’effondrement (collapse) et des notions d’audit interventionnel,
- exposer une notion forte `QueryLoopOperationality` (profil audit).

### 3.2 Bridges “Independence → Query” (minimal / fort / retour Dynamics)

Ensemble de fichiers (Examples) :

- `IndependenceToAutoreflexiveQueryBridge.lean`
  - bridge minimal fibre-local : “réparation par seconde marge”.
- `IndependenceToAutoreflexiveQueryStrongBridge.lean`
  - bridge fort (famille de fibres) : fermeture du profil `QueryLoopOperationality`.
- `IndependenceToAutoreflexiveQueryRefiningLiftBridge.lean`
  - retour explicite vers `CompatDimEq / RefiningLift / Sig`, et lecture sur le post-state.

Rôle global :

- relier une obstruction `StepSeparatesFiber` (marge insuffisante) à :
  - une dynamique query (action→réponse conditionnée) et ses audits,
  - puis à une médiation finie canonique (`CompatDimEq`, `RefiningLift`, `CompatSigDimLe`).

---

## 4) Fermeture empirique (ASLMT) : invariants + critères DONE

Le plan empirique est fixé dans :

- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/UNIVERSALITY_PLAN.md`

Résumé opérationnel (critères DONE) :

- barrières structurelles (visible-only),
- capacité minimale (min-lift en variant `z`),
- causal gates (ablation/swap),
- verdict strict IID ∪ OOD et multi-seeds,
- traçabilité snapshot+hash.

### 4.1 Phase A1 / A2 (witness unifié n-scalable)

Références de runs et lecture (cf. `UNIVERSALITY_PLAN.md`) :

- A1 : `v10_phaseA1_*` (n ∈ {3,4,5,6}, seeds 0..4)
- A2 : `v15_phaseA2_*` (n ∈ {8,12,16}, seeds 0..4)

Ces phases visent la stabilité du pattern :

- réf `z=n` : fermeture stricte,
- sous-capacité `z<n` : échec strict,
- interventions : ablation/swap attestent la charge du médiateur.

### 4.2 Phase B (familles additionnelles)

Familles préparées :

- `v16_phaseB_temporal_zigzag_64`
- `v17_phaseB_symbolic_orbit_64`

Visée : ré-instancier le spine (barrières + min-lift + causal gates) sur plusieurs grammaires de mondes.

### 4.3 law_v3b (autoreflexivité + autoréférence en “boucle query”)

Protocole de référence (document) :

- `/mnt/c/Users/frederick/Documents/forU2read/Private_notes/LAW_V3B_PROTOCOL.md`

Objet : un test où l’action de requête est choisie à partir d’un état interne, puis conditionne causalement le flux d’information qui rend la décision possible, et où la charge du médiateur est auditée.

Variante qforced+zread (objectif : requête opérationnellement nécessaire + action lue depuis le médiateur interne) :

- scripts : `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b_unified_v2_strong_qforced_zquery/`
  - `aslmt_model_*_query_zread.py`
  - `aslmt_train_*_diag_zread.py`
  - `aslmt_campaign_*_zread_matrix_diagstop_v3.py`
  - `verify_*_qforced_matrix.py`

Run de référence (solid) au 2026-04-23 (matrice `z∈{n, ⌊n/2⌋, n-1}`) :

- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_law_v3b_unified_v2_strong_qforced_zread_solid_20260423_102039_9f958bfafaad/`
  - Référence `n=8, z=8, seed=0..4` : passes strictes sur IID ∪ OOD pour `q_acc/res_acc/z_acc` et pour les gates `pair_eval`
    (barrières valides, baselines à 0, ablation à 0, swap-follow à 1.0, swap-orig à 0.0, `query_action_rate` équilibré).
  - Les runs sous-capacité `z<n` font partie du même master JSONL (utilisés par le verifier `--z-policy A1`).

---

## 5) Visée : fermeture “universelle” (ce qui compte comme clôture complète)

La fermeture visée est une conjonction de trois fermetures, chacune avec son critère :

### 5.1 Fermeture (Lean) — loi abstraite + chaîne disciplinée

Critère : la loi existe comme mécanisme explicite, constructif, auditée (`AXIOM_AUDIT`) :

- pas (`InductionStep`) : obstruction → médiation → non-descente → clôture après extension,
- chaîne (`DisciplinedReferentialDerivation`) : re-ciblage + usage effectif de l’extension (`UsesExtension`),
- raccord à `Dynamics` via `Compatible` + `Sig`.

### 5.2 Fermeture (Empirique) — universalité contrôlée

Critère : un verifier strict binaire sur IID ∪ OOD + multi-seeds, stable quand on varie :

- `n` (et sous-capacités `z<n`),
- familles de tâches (Phase B),
- classes de solveurs (Phase C).

### 5.3 Fermeture (Bridge) — correspondance “structure ↔ comportement”

Critère : existence de bridges qui relient :

- obstruction `StepSeparatesFiber` + compressibilité (ou données de lift) →
  - médiation finie (`CompatDimEq`, `RefiningLift`, `CompatSigDimLe`) **et**
  - régime query opérationnel (`QueryLoopOperationality`),
- avec lecture explicite du médiateur (post-state) et audits interventionnels.

---

## 6) Checklist (lecture rapide)

Lean :
- `ReferentialProblem` + `InductionStep` + `DisciplinedReferentialDerivation` : OK.
- `Compatible` + `Sig` → extraction d’un `InductionStep` : OK.
- `Leadsto` + `Terminal(Closes ∨ Cycle)` : OK (sans rank / well-founded).
- Bridges vers query + retour Dynamics : présents (minimal / fort / refining lift).

Empirique :
- Phase A1 : voir `UNIVERSALITY_PLAN.md`.
- Phase A2 : voir `UNIVERSALITY_PLAN.md`.
- Phase B : outillage prêt (`v16`, `v17`).
- law_v3b : protocole + variante qforced+zread + run `solid` en cours.
