# Integrating COFRS-style closure/mediation into `HWM_PLDM-main`

This note is written against the code at:
`/mnt/c/Users/frederick/Documents/forU2read/HWM_PLDM-main`

Goal: identify **where** to inject the closure/mediation/causality stack so that HWM becomes an explicit **solver** (not only “planning with a latent world model”).

---

## 1) What this repo already provides (direct hook points)

### 1.1 Hierarchical world model

- The model is `HJEPA` with two levels: `level1` and `level2`.
  - `HJEPA` builds two `JEPA` instances and (optionally) a level-2 JEPA over level-1 representations.
  - File: `HWM_PLDM-main/pldm/models/hjepa.py`

### 1.2 Planning loop (already an autoreflexive substrate)

- Planning is done via MPC evaluators and planners:
  - `MPCEvaluator` builds planners and runs MPC (flat or hierarchical).
    - File: `HWM_PLDM-main/pldm/planning/mpc.py`
  - Hierarchical planning uses `TwoLvlPlanner`.
    - File: `HWM_PLDM-main/pldm/planning/planners/two_lvl_planner.py`
  - D4RL maze-specific evaluators:
    - flat: `MazeMPCEvaluator` (`.../planning/d4rl/mpc.py`)
    - hierarchical: `HierarchicalD4RLMPCEvaluator` (`.../planning/d4rl/hmpc.py`)

### 1.3 A “closure-like” mechanism already exists

`HierarchicalD4RLMPCEvaluator.determine_optimal_depths` probes multiple planning depths and picks a depth per environment based on distance-to-target in representation space.

That function is already structurally close to a **closure monitor**:
- it answers “how much horizon / how many macro-steps are required for this episode to become solvable with the current interface”.

File: `HWM_PLDM-main/pldm/planning/d4rl/hmpc.py`

### 1.4 An explicit “mediator” exists in the model stack

In the predictor stack, there is explicit latent machinery (`z_dim`, continuous prior/posterior models, deterministic mean used in current code path).

- `PredictorConfig` includes `z_dim`, `z_stochastic`, `z_discrete`.
  - File: `HWM_PLDM-main/pldm/models/predictors/enums.py`
- `SequencePredictor.forward_multiple` computes:
  - `prior_stats := prior_model(current_state)` then chooses `prior := mu` (deterministic path),
  - stores `priors` / `posteriors` in `PredictorOutput`.
  - File: `HWM_PLDM-main/pldm/models/predictors/sequence_predictor.py`

This is the natural place to name a mediator and to define intervention hooks (swap/ablation/forced-branch).

---

## 2) COFRS mapping (interface, truth, closure, mediation)

### 2.1 Interface (`q`)

In this repo there are multiple natural “interfaces”:

- `q₁(x)` = level-1 representation (encoder/backbone output used by L1 planner).
- `q₂(x)` = level-2 representation / macro-state used by L2 planner.
- `q_goal(x)` = target representation (objective’s target encoding) used as “truth proxy” during planning.

Concrete places:
- L1 interface: `self.model.level1.backbone(obs).encodings` (or obs_component when using proprio).
- L2 interface: `self.model.level2.backbone(l1_obs, ...)` then `enc2 := ...encodings`.

### 2.2 Truth (`T`)

For D4RL mazes, a clean operational truth is:
- `T(x)` = “episode succeeds (reaches goal within budget)”
or a richer `T` such as:
- “first decision/turn is correct”,
- “the next macro-action chosen is correct under optimal policy”.

This repo already measures success and steps-to-goal in reports.

### 2.3 Closure test (operational)

In planning, closure corresponds to:
- from the current interface alone, one can select actions that reliably achieve the target.

Operationally, closure can be tested by:
- whether the L1-only planner achieves success reliably at bounded cost,
- or by a depth probe that identifies when adding horizon/macro-step makes the target reachable in latent space.

The existing `determine_optimal_depths` is a strong starting point for a closure monitor, because it builds a per-episode “required depth” signal.

### 2.4 Mediation

In the repo, mediation can be made explicit as:
- (i) the latent `z` in the predictor stack (when `z_dim>0`), and/or
- (ii) the level-2 macro-state, which is an enrichment of the L1 interface.

COFRS-style requirement: when closure fails on `q₁`, any correct solver must route through a mediator that does not descend to `q₁`.

In this repo, the natural “forced mediator” candidate is: “use L2 (macro) planning + macro-state / latent action variables”.

---

## 3) What we should add (minimal code changes, maximal conceptual gain)

### 3.1 Add a first-class `ClosureMonitor` report during evaluation

Add an evaluation-time report that, for each episode:
- records whether L1-only planning succeeds,
- records the minimal depth found by `determine_optimal_depths` (or an equivalent probe),
- records the planning cost (number of replans, number of samples, runtime).

This yields a clean empirical stratification:
- “closed”: L1-only works at bounded cost.
- “non-closed”: L1-only fails or requires depth/horizon beyond threshold, while hierarchical works.

Where to implement:
- `HWM_PLDM-main/pldm/planning/d4rl/hmpc.py` (extend `determine_optimal_depths` outputs into the report),
- and/or `HWM_PLDM-main/pldm/planning/mpc.py` (central place to log).

### 3.2 Add mediator intervention audits (swap/ablation) at planning-time

We want interventions that are *about mechanism*, not only about score.

Two clean targets:

#### A) Latent mediator `z` in the predictor (when `z_dim>0`)

Add a wrapper around `SequencePredictor.forward_multiple` (or around `LearnedDynamics.__call__`) enabling:
- **ablation**: replace `prior` (or posterior) by zeros (or a constant) for all timesteps,
- **swap**: permute `prior` across batch items (keeping the same visible interface),
- **forced-branch**: run the same episode with two different planned “macro” variables (if those are treated as mediator).

Then measure:
- plan divergence in predicted trajectories,
- decision divergence (chosen first macro-action / subgoal),
- success-rate collapse under ablation,
- “swap-follow” (decision tracks swapped mediator).

Primary hook points:
- `HWM_PLDM-main/pldm/models/predictors/sequence_predictor.py`
- `HWM_PLDM-main/pldm/planning/planners/mppi_planner.py` / `LearnedDynamics` pipeline in that file.

#### B) Macro-state / hierarchical interface as mediator

This is the “visible enrichment” mediator:
- ablation = disable L2 planning (flat baseline),
- swap = swap the *subgoal* proposed by L2 between envs (then replan L1),
- forced-branch = force alternative subgoal choices and observe decision change.

Hook points:
- `TwoLvlPlanner.plan` where L2 predicted obs is used to reset L1 targets.

### 3.3 Add a minimal “diagonal witness” construction in Diverse Maze

We want an explicit demonstration of non-closure:
- two episodes/states that are indistinguishable under the chosen interface `q₁`,
- but require different solver behavior to achieve `T`.

In mazes, a clean way is to define an interface that drops global map information:
- interface = local patch or local proprio-only / partial observation,
- truth = reachability / correct turn choice.

This is the cleanest path to a real diagonal witness in this domain, because with a full top-down map as observation, many ambiguities disappear.

Where:
- `HWM_PLDM-main/pldm_envs/diverse_maze/wrappers.py` / rendering pipeline,
- add an “interface restriction” mode (local view / masked map) used only in the COFRS witness evaluation.

---

## 4) What “success” looks like for COFRS integration in this repo

You get a solver-level story with three measurable layers:

1) **Regime stratification** (closure monitor):
   - identify episodes where L1 closes vs doesn’t close.

2) **Forced mediation** (autoreferential layer):
   - show that in non-closed episodes, success depends on a mediator (z or hierarchical interface),
   - and that interventions on that mediator causally move decisions (swap-follow / ablation-drop).

3) **Autoreflexive behavior** (loop layer):
   - show that the solver’s behavior is organized as repeated reconfiguration (replan, macro-to-micro, subgoal reset),
   - and that this loop is operationally necessary in the non-closed regime.

---

## 5) Immediate next step (practical)

If we want a tight first milestone with minimal edits:

1. Add reporting of “required depth” + “hierarchy used” + “L1-only success” to hierarchical eval logs.
2. Implement one intervention:
   - swap the L2 subgoal between two envs before L1 planning,
   - log “swap-follow” at the behavior level (first action / success).

This already yields a clean mediator-audit with almost no model surgery.

