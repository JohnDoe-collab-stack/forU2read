# LAW_V3B protocol and architecture (ASLMT)

This note is an exhaustive, code anchored description of the `law_v3b` test protocol and of the architecture it attests.

Scope:
- Describe exactly what the task is, how IID and OOD are generated, what the models see, and how success is measured.
- Describe the query loop (autoreflexivity) and the mediation audit (autoreferentiality via ablation and swap).
- Describe the reproducibility mechanics (snapshot plus hash) and the verification guardrails.

Repository locations (source of truth):
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_env_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py`
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_model_law_v3b_memory.py`
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py`
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_campaign_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py`
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/verify_aslmt_campaign_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py`
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/README_aslmt_law_v3b_hard_ood_masks_balanced_split.md`

## 1) The task in one sentence

At each episode:
- the world hides a binary vector `H` and an index `i`
- the goal is to output the bit `H[i]`
- but you only get the bit if you first query the correct hidden class `hi = hi_class(i)`

In other words: the agent must infer `hi` from parity constraints (views), use it to query, then use the query response to decide the final bit.

### 1.1 World variables and derived classes

World sampling happens in `sample_batch`:
- `H` is sampled as a random bit matrix shape `[B, n_bits]` (env: line 259)
- `i` is sampled as a random index in `[0, n_bits)` (env: line 260)
- `hi = hi_class(i)` and `lo = lo_class(i)` (env: lines 261 to 263)

Code:
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_env_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:252`
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_env_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:69`

Interpretation:
- `hi` is the hidden query class that must be recovered
- `lo` is the visible class token available at query time
- by construction, `hi` and `lo` partition the `n_index_bits` of the index `i` (env: line 58)

### 1.2 Action spaces and outputs

Query action:
- `a_hi` is a categorical action in `{0, 1, ..., 2^n_hi_bits - 1}`
  - the action space size is `cfg.n_queries = 2^n_hi_bits` (env: line 66)
  - `a_hi` is sampled or chosen greedily from `logits_q`, whose last dimension is `cfg.n_queries` (train: lines 60 to 65)
- it is intended to match `hi_true = hi_class(i)` (env: line 284)

Output action:
- `out` is a categorical action in `{0, 1}` (model: out head ends in 2 logits, model: line 46)
- it is intended to match the bit `H[i]` (env: line 286)

Success requires both:
- the query was correct
- and the output equals the bit

Code:
- reward definition in both rollouts:
  - `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:88`

## 2) The interface: what is visible when

### 2.1 Query time visible token

At query time, the *visible* interface is only `lo_tok`:
- `lo_tok = LO_BASE + lo` (env: lines 16 to 18, 76 to 78, 264 to 265)

Code:
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_env_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:16`
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_env_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:264`

This is deliberately insufficient: `lo` is only the low bits of the index, while `hi` are the high bits (env: lines 69 to 74).

### 2.2 Views before query (the parity constraint stream)

Before querying, the agent receives `view_seq`, a token stream encoding parity constraints over `hi`.

Each view is a mask row `mask_int` in `{1..2^n_hi_bits - 1}`, and contributes:
- `n_hi_bits` tokens that encode each mask bit (0 or 1) (env: lines 223 to 230)
- 1 token that encodes the parity of `mask_int & hi` (env: lines 231 to 236)

Interleaving is:
- for each view v: emit all `maskbit(j)` tokens for `j=0..n_hi-1`, then emit `parity` token (env: lines 238 to 248)

Code:
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_env_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:211`
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_env_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:238`

Token ids:
- mask bit tokens: `MASKBIT_BASE + (j*2 + bit)` (env: lines 19 to 21)
- parity tokens: `PARITY_BASE + parity_bit` (env: lines 22 to 23)

### 2.3 Result token after query

After the query action `a_hi` is chosen, the environment produces `res_tok`:
- if `a_hi == hi_true`, then `res_tok` reveals the final bit (`RES_BIT0` or `RES_BIT1`)
- else `res_tok` is `RES_MISS`

Code:
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_env_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:283`

## 3) IID vs OOD: what shifts, and what does not

The task and vocabulary are held fixed.
OOD is made hard by changing the distribution of view mask blocks, plus longer delays.

### 3.1 Full rank blocks over GF(2)

`law_v3b` precomputes ordered tuples of masks that form a full rank matrix over GF(2):
- enumerates ordered `n_hi_bits` tuples of distinct nonzero masks
- filters those with GF(2) rank equal to `n_hi_bits`

Code:
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_env_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:91`

### 3.2 Hard OOD split at the block level

Masks for *all* views are drawn by concatenating full rank blocks from a pool.
IID and OOD use disjoint pools, defined at the index level of the full rank set list:
- disjointness is enforced for blocks (tuples), not necessarily for individual atomic masks
- the OOD shift is therefore a shift in the composition and ordering of constraint blocks

Code:
- `_sample_masks_all` docstring and implementation:
  - `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_env_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:143`

Special case for `n_hi_bits == 2`:
- explicit balanced 3/3 split to avoid enumeration artifacts (env: lines 163 to 180)

General case for `n_hi_bits >= 3`:
- deterministic shuffle with seed `1337 + n_hi`
- alternate indices IID vs OOD (env: lines 182 to 191)

Number of blocks per sample:
- `n_blocks = ceil(n_views / n_hi_bits)` (env: line 194)
- blocks are flattened then sliced to `n_views` masks (env: lines 204 to 208)

### 3.3 Delay shift

In addition to the mask distribution shift, delays are sampled differently in OOD:
- IID: `d1, d2` sampled uniformly in `[0, iid_delay_max]` (env: lines 273 to 275)
- OOD: `d1, d2` sampled uniformly in `[ood_delay_min, ood_delay_max]` (env: lines 276 to 278)

This makes OOD harder without changing the core task.

## 4) The two policies: A (memory) vs B (visible only)

### 4.1 Policy A (memory, state locked)

`LawV3MemoryPolicyV1`:
- embedding
- GRUCell memory `mem`
- heads read only `mem`

Code:
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_model_law_v3b_memory.py:21`

Relevant methods:
- `step_mem` integrates a token into memory (model: lines 57 to 59)
- `logits_query(mem)` produces query logits (model: lines 61 to 63)
- `logits_out(mem)` produces output logits (model: lines 64 to 66)

### 4.2 Policy B (visible only baseline)

`LawV3VisibleOnlyPolicyV1`:
- no memory
- query logits depend only on `lo_tok` (model: lines 107 to 110)
- output logits depend only on `res_tok` (model: lines 111 to 114)

Code:
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_model_law_v3b_memory.py:77`

## 5) The query loop rollout (autoreflexivity)

### 5.1 Memory rollout A: exact sequence of computations

Rollout A is `_rollout_memory_policy`:
1) initialize `mem` (train: line 43)
2) integrate all view tokens (train: lines 45 to 48)
3) apply delay `d1` via repeated `DELAY` token updates, masked per sample (train: lines 49 to 55)
4) critical anti bypass: do not inject `lo_tok` into memory before query (train: lines 56 to 57)
5) choose query action `a_hi` from `mem_for_query` (train: lines 59 to 66)
6) environment returns `(correct, bit, res_tok)` (train: line 68)
7) apply delay `d2` similarly (train: lines 70 to 76)
8) integrate `res_tok` (train: line 77)
9) choose final output `out` from `mem_for_out` (train: lines 79 to 86)
10) reward is `1` iff query is correct and output equals `bit` (train: line 88)

Code:
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:25`

This is an explicit loop:
`(view stream) -> internal state -> action -> env response -> updated state -> decision`.

### 5.2 Visible only rollout B: what is allowed

Rollout B `_rollout_visible_only`:
- query uses only `lo_tok` (train: line 99)
- output uses only `res_tok` (train: line 109)
- reward is defined in the same way (train: line 117)

Code:
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:93`

## 6) The mediation audit (autoreferentiality via interventions)

### 6.1 What the audit stores as the mediator

The memory rollout returns detached mediator tensors:
- `mem_query` (the memory used to choose the query)
- `mem_out` (the memory used to choose the output)

Code:
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:90`

### 6.2 Ablation

In `_audit_causal_memory`, ablation is defined by forcing:
- `mem_for_query = 0`
- `mem_for_out = 0`

and measuring the success drop:
- `ablation_drop = base_success - ablate_success`

Code:
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:141`

### 6.3 Swap (and swap vs perm)

Swap is performed by permuting `mem_out` across the batch:
- `mem_out_swapped = base["mem_out"][perm]` (train: line 145)

Then:
- `swap_vs_orig` evaluates the swapped mediator against the original `(H, i)` labels (train: lines 150 to 152)
- `swap_vs_perm` evaluates the swapped mediator against permuted labels (train: lines 154 to 158)

Interpretation:
- if `mem_out` carries the decision relevant information, swapping it should break correctness on original labels (low `swap_vs_orig`)
- but swapping it should preserve correctness relative to swapped labels (high `swap_vs_perm`)

Code:
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:135`

## 7) Training protocol (what is optimized)

### 7.1 Two models trained side by side

In `_train_one`, both models are trained in the same loop:
- `modelA` memory policy
- `modelB` visible only policy

Code:
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:179`

### 7.2 Hyperparameters by profile

For `profile == "solid"`:
- `steps = 30000` (train: line 195)
- `batch_size = 512` (train: line 196)
- `eval_batch = 4096` (train: line 197)
- `lr = 1.5e-3` (train: line 198)
- `d_embed = 128`, `d_mem = 256` (train: lines 199 to 200)
- `ent_coef = 0.01`, `v_coef = 0.25` (train: lines 201 to 202)

### 7.3 Update rule (policy gradient plus value plus entropy)

Both A and B are updated via:
- `loss_pg` using advantage terms for both query and output logprobs
- `loss_v` on the output value head
- `loss_ent` for entropy regularization

Code:
- `update_memory` definition:
  - `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:212`
- `update_visible` definition:
  - `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:227`

Progress logging:
- logs at step 1, every 1000 steps, and at the end (train: line 253)

## 8) Evaluation protocol (what is reported in master.jsonl)

For each config and seed:
- evaluate A and B in IID and OOD with greedy rollouts (train: lines 257 to 260)
- compute audit dict in IID and OOD for A (train: lines 261 to 262)
- append one JSON line per (cfg, seed) to the master jsonl (train: lines 264 to 266)

The emitted row schema is:
- `iid.A_success`, `iid.B_success`, `iid.audit`
- `ood.A_success`, `ood.B_success`, `ood.audit`

Code:
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:264`

## 9) Reproducibility protocol (snapshot plus hash)

The campaign runner:
- hashes the env, model, and train scripts into a bundle hash (campaign: lines 39 to 45, 122 to 133)
- copies those files into a snapshot directory
- renames the train script to include timestamp plus hash (campaign: lines 59 to 62)
- writes `manifest.json` with sha256 per file (campaign: lines 63 to 74)
- runs training from the snapshot directory (campaign: line 109)

Code:
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_campaign_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:51`

Outputs:
- snapshot dir: `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/snapshots/aslmt_law_v3b_<TS>_<HASH12>/`
- run dir: `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_law_v3b_<TS>_<HASH12>/`
- master jsonl: `master_<TS>_<HASH12>.jsonl` (campaign: line 82)
- log txt per cfg and seed: `log_<TS>_<HASH12>_<cfg>_seed<seed>.txt` (campaign: line 83)

## 10) Verification guardrails (what it means for a run to "pass")

The verify script enforces:
- strict schema (kind, cfg set, unique (cfg, seed), single profile, contiguous seeds)
- strict expected row count: 3 cfgs times number of seeds (verify: lines 35 to 89)

Then it checks OOD thresholds per cfg, taking mins or maxes across seeds:
- `min_A_ood >= 0.90` (verify: lines 91, 153 to 155)
- `max_B_ood <= 0.35` (verify: lines 92, 156 to 158)
- `min_ablation_drop >= 0.25` (verify: lines 93, 159 to 161)
- `max_swap_vs_orig <= 0.70` (verify: lines 94, 162 to 164)
- `min_swap_vs_perm >= 0.80` (verify: lines 95, 165 to 167)

Code:
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/verify_aslmt_campaign_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:35`

## 11) What `law_v3b` attests, in project language

### 11.1 Autoreflexivity (operational)

It is present if:
- there exists an internal state that determines an action
- forcing a different action would change the response stream
- the decision is made after incorporating the response

In `law_v3b`, this is witnessed by the explicit computation chain in `_rollout_memory_policy` (train: lines 43 to 88).

### 11.2 Autoreferentiality (mediator audit)

It is present if:
- correctness depends on an internal mediator (ablation drops performance)
- swapping the mediator changes correctness relative to the swap

In `law_v3b`, this is witnessed by:
- `ablation_drop`
- `swap_vs_orig` and `swap_vs_perm`

Code:
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:135`

## 12) A minimal run recipe (exact commands)

The README gives a canonical run (solid, seeds 0..4, CUDA) and a canonical verification call:
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/README_aslmt_law_v3b_hard_ood_masks_balanced_split.md:1`

For reference, the runner accepts either a single seed or a seed range (campaign: lines 135 to 146).

## 13) Notes for using `law_v3b` as a protocol template

If other tests adopt `law_v3b` as a base protocol, the invariants that matter are:
- explicit visible only insufficiency plus a visible only baseline
- explicit anti bypass at the critical boundary (before query, before decision, or both)
- an internal mediator that can be ablated and swapped, with both swap_vs_orig and swap_vs_perm
- OOD shift that changes structure without changing vocabulary or task target
- snapshot plus hash, and a strict verifier that rejects partial or ambiguous runs

## Appendix A) Config family (C0, C1, C2)

The training script instantiates three configs by name (campaign: line 140):
- `C0_16b_4i_2hi`
- `C1_64b_6i_3hi`
- `C2_128b_7i_4hi`

Config parameters depend on `profile` (smoke vs solid) in `_make_cfg_by_name`:
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/law_v3b/aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py:163`

For `profile == "smoke"`:
- `C0_16b_4i_2hi`: `n_bits=16`, `n_index_bits=4`, `n_hi_bits=2`, `n_lo_bits=2`, `n_views=6`, `iid_delay_max=1`, `ood_delay_min=2`, `ood_delay_max=4` (train: line 166)
- `C1_64b_6i_3hi`: `n_bits=64`, `n_index_bits=6`, `n_hi_bits=3`, `n_lo_bits=3`, `n_views=8`, `iid_delay_max=1`, `ood_delay_min=2`, `ood_delay_max=5` (train: line 170)
- `C2_128b_7i_4hi`: `n_bits=128`, `n_index_bits=7`, `n_hi_bits=4`, `n_lo_bits=3`, `n_views=10`, `iid_delay_max=1`, `ood_delay_min=2`, `ood_delay_max=6` (train: line 174)

For `profile == "solid"`:
- `C0_16b_4i_2hi`: `n_views=8`, `iid_delay_max=2`, `ood_delay_min=3`, `ood_delay_max=6` (train: line 167)
- `C1_64b_6i_3hi`: `n_views=10`, `iid_delay_max=2`, `ood_delay_min=3`, `ood_delay_max=7` (train: line 171)
- `C2_128b_7i_4hi`: `n_views=12`, `iid_delay_max=2`, `ood_delay_min=3`, `ood_delay_max=8` (train: line 175)
