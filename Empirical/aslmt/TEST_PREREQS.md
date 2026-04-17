# Prerequisites and professional method for ASLMT tests

This file is the operational companion of `Empirical/aslmt/UNIVERSALITY_PLAN.md`.
Its purpose is to prevent wasted multi hour runs by enforcing the plan's constraints: traceability, strict verification, valid geometry, and diagnostics.

If a run does not satisfy the prerequisites below, it is not a scientific run. Do not launch it.

## 1) Scope and alignment with `UNIVERSALITY_PLAN.md`

This document does not change the plan. It operationalizes it.

It enforces:

- Plan section 0 and 1: what counts as a claim, what counts as DONE
- Plan section 1.2 and 5: reproducibility and governance rules
- Plan section 3: phase order and phase specific requirements
- Plan section 4: required artifacts and outputs to cite a result

## 2) Claims allowed per run (no mixing)

Every campaign run must target exactly one plan phase and state the claim explicitly:

- Phase A1: stability in `n` for `n in {3,4,5,6}`
- Phase A2: scale up in `n` for `n in {8,12,16}`
- Phase B: multiple task families
- Phase B': negative controls
- Phase C: multiple solver classes
- Phase D: abstract characterization (Lean side)

A run that mixes claims is invalid for closure. If it is useful, it must be labeled as a smoke run.

## 3) What DONE means (closure criteria)

A phase is only DONE if a strict verifier returns a binary verdict on IID and OOD, with multi seeds and auditability.

### 3.1 DONE(A1)

DONE(A1) requires, for all `n in {3,4,5,6}`:

- Matrix:
  - `seed = 0..4`
  - `z in {n, n-1, floor(n/2)}`
- For the reference group `z=n`:
  - PASS under `profile=solid` on IID and OOD
  - barriers pass, baselines are 0, causal gates pass
- For at least two under capacity groups `z<n`:
  - FAIL under `profile=solid` on IID and OOD by failing the image barrier prediction, while keeping barriers valid

### 3.2 DONE(A2)

DONE(A2) requires the A1 pattern to remain stable on `n in {8,12,16}`.

Minimum acceptable closure statement:

- The pattern `z=n` PASS and `z<n` FAIL remains stable on at least two values of `n >= 8` under the same strict contract, with `seed=0..4`, IID and OOD, and the same matrix policy `z in {n, n-1, floor(n/2)}`.

A run is not allowed to claim DONE(A2) from a single `n` value.

### 3.3 DONE(B)

DONE(B) requires the Phase A closure pattern to be reproduced on at least 2 additional task families that are genuinely different, each with:

- explicit barrier checks
- geometry validity argument and enforcement by construction
- strict verifier and multi seed auditability

### 3.4 DONE(B')

DONE(B') requires negative controls that must FAIL under the same strict verifier, reproducibly (multi seeds), including at least:

- cue broken or removed
- image broken or removed
- random permutation of the mediator
- baseline capacity increased without the mediator
- randomized symbol to target mapping

### 3.5 DONE(C)

DONE(C) requires robustness over solver classes. For each family, test at least:

- `S_det` (reference witness solver)
- `S_learned` (learned extractor)
- `S_alt` (alternative architecture)

The same strict verifier applies. The claim cannot be carried by one solver alone.

### 3.6 DONE(D)

DONE(D) is on the Lean side. It requires:

- an abstract class specification, with no benchmark implementation details
- at least one partial converse or normal form result

## 4) Non negotiable reproducibility and governance (Plan section 1.2 and 5)

### 4.1 Never edit historical scripts

No Python script that produced a cited result is edited.
Any change is a new file with a new name.

### 4.2 Snapshot discipline (timestamp plus hash)

Every scientific run must execute a frozen snapshot:

- the campaign copies all used scripts into `Empirical/aslmt/runs/snapshots/<run_id>/`
- the snapshot includes a manifest with per file hashes
- the run directory encodes a timestamp plus a bundle hash

Hard rule:

- training and verification must run from the snapshot directory, not from the editable source directory

### 4.3 Output discipline

Every scientific run must write:

- one master JSONL file (append only)
- per job logs that begin with the full command line
- a verifier output file that begins with the full verifier command line

A partial run must never be rewritten.

## 5) Geometry validity is a prerequisite (Plan section 3 Phase A precondition)

Geometry is not a debugging step. It is a prerequisite.

Before training is considered meaningful, the witness must be structurally valid for the targeted domain `(n, img_size, stride, IID and OOD)`.

The witness must guarantee by construction:

- barrier validity: the barrier pairs are genuinely indistinguishable at the intended interface, while the dynamic truth differs
- injectivity: the hidden class to target mapping does not collide when `n` increases

### 5.1 Spaced witness validity condition

For a spaced witness with stride `POS_STRIDE = stride`, the inner available length is:

- IID: `L = 2*occ_half - 6`
- OOD: `L = 2*occ_half - 8`

Required length:

```
needed = stride*(n - 1) + 1
```

Validity requirement:

```
Lx >= needed and Ly >= needed
```

Additionally:

- the occluder must fit inside the image with the chosen margins
- the sampled center range must be non empty

### 5.2 Enforced by construction

The dataset must enforce a minimum `occ_half` derived from `needed`, and must sample centers conditionally so the occluder never exceeds image bounds.

If validity is not guaranteed by construction, the campaign is invalid.

## 6) Verifier contract (strict means strict)

A scientific run must define and use a strict verifier that returns a binary pass or fail, with the contract written in verifier terms.

### 6.1 Solid verifier semantics

`profile=solid` is strict. It is written as equalities on minima and maxima over seeds.

Reference group (`z=n`) must satisfy, on IID and OOD:

- barrier checks pass for every seed
- `A_both_image_pair_rate` minimum over seeds equals `1.0`
- `A_both_cue_pair_rate` minimum over seeds equals `1.0`
- `A_swap_follow_image_pair_rate` minimum over seeds equals `1.0`
- `A_swap_orig_both_image_pair_rate` maximum over seeds equals `0.0`
- `A_ablated_both_image_pair_rate` maximum over seeds equals `0.0`
- baselines remain at `0.0`

Under capacity group (`z<n`) must satisfy, on IID and OOD:

- barriers remain valid
- `A_both_image_pair_rate` minimum over seeds is strictly less than `1.0`

### 6.2 Immediate consequence (min and max are irreversible)

If any completed seed in the reference group has:

- a value below `1.0` for any required `*_min == 1.0` gate, or
- a value above `0.0` for any required `*_max == 0.0` gate,

then the block cannot pass `solid`, regardless of remaining seeds.

## 7) Stop rules (prevent wasted multi hour runs)

### 7.1 Mandatory early stop for solid closure attempts

For each `(n, z)` block, as soon as the reference group has one finished seed:

- run the verifier in partial mode (minimum seeds set to 1)
- if any required reference gate is already violated, stop the campaign and fix the issue

### 7.2 Diagnostic requirement before launching multi seeds

Every new training variant intended for `solid` must provide a diagnostic path that can, for a fixed `(n, z, seed)`:

- save a checkpoint at the end of training
- dump the failing contexts for any strict gate miss, including:
  - context parameters
  - pair type (image barrier or cue barrier)
  - both targets used by the pair score
  - overlap scores and the decision margins

If a variant cannot produce this information, it is not ready for a multi seed solid campaign.

### 7.3 Mandatory preflight smoke run

Before any multi seed campaign, run one seed for `z=n` on a representative `n`, then run the verifier on that single entry.

Smoke runs must write to `/tmp` or explicitly named `*_smoke_*` outputs and must never overwrite reference run directories.

## 8) Required artifacts per test version (Plan section 4)

For every new version folder (v11, v12, v13, and so on), the version is considered run ready only if it provides:

- a `README_*.md` stating:
  - the targeted phase claim
  - exact command lines
  - acceptance criteria in verifier terms
- a strict verifier `verify_*.py` returning a binary pass or fail for the targeted phase
- a campaign runner `aslmt_campaign_*.py` writing:
  - a master JSONL
  - per job logs
- a results document `RESULTS_AND_INTERPRETATION_*.md` that:
  - points to the run directories under `Empirical/aslmt/runs/`
  - contains a table of minima and maxima over seeds for the strict gates

For every run directory cited as closure evidence, it must contain:

- `*_master_*.jsonl` (append only)
- `train_*.txt` beginning with the full command line, environment, and script hash
- `verify_*.txt` beginning with the full verifier command line and script hash

If any of these artifacts are missing, the run is not allowed to be cited as a closure result.

## 9) Environment prerequisites (GPU)

Before launching any long campaign:

- confirm CUDA is available
- confirm the intended GPU is visible

Example commands:

```
nvidia-smi
/home/frederick/.venvs/cofrs-gpu/bin/python3 -c "import torch; print(torch.cuda.is_available()); print(torch.cuda.get_device_name(0) if torch.cuda.is_available() else 'no cuda')"
```

If CUDA is not available, do not start a run expected to take hours.

## 10) Review checklist (before running)

1. The run targets exactly one plan phase and states the claim.
2. Snapshot policy is in place and the campaign executes from the snapshot.
3. Geometry validity is guaranteed by construction for targeted `(n, IID and OOD)` and `img_size`.
4. The verifier contract is explicit and matches the intended claim.
5. A partial verifier run exists to stop early on reference failures.
6. A diagnostic path exists for post mortem of any strict gate miss.
7. The campaign enumerates exactly the intended `(n, z, seed)` matrix and nothing else.
8. The required artifacts are present for the version and for the run outputs.
