# v7 conformity to COFRS (protocol-grade)

This note records the *in-repo* correspondence between the v7 empirical witness and the COFRS spine.

## What v7 defines (structure)

- Decision-time observable `obs` corresponds to the final visible image `image` (scaffold + occluder).
- For each fixed context `ctx`, the pair rendering produces two states with:
  - identical decision-time observation (`image`), and
  - different hidden targets (`hidden_target`).

This is audited in code by `pair_eval.*.obs_barrier_ok`.

## Protocol-grade criterion

The protocol-grade requirement is *pair-grade* (binary): for a list of contexts, the model must be correct on **both** members of every pair.

The strict verifier used by the “OOD-required” campaign enforces:

- IID: `A_both_correct_rate = 1.0`, `B_both_correct_rate = 0.0`, `obs_barrier_ok = True`.
- OOD: `A_both_correct_rate = 1.0`, `B_both_correct_rate = 0.0`, `obs_barrier_ok = True`.

## Where it lives in this repo

- Campaign runner (snapshot + hash): `Empirical/aslmt/v7_descriptive/aslmt_campaign_v7_perfect_amodal_hidden_target_pair_oodrequired_v2.py`
- Training + pair-eval writer: `Empirical/aslmt/v7_descriptive/aslmt_train_v7_perfect_amodal_hidden_target_seeded_pair_trainood.py`
- Strict verifier: `Empirical/aslmt/v7_descriptive/verify_aslmt_v7_perfect_amodal_hidden_target_pair_oodrequired.py`
- Run artifacts: `Empirical/aslmt/runs/` (each run contains `v7_master_*.jsonl` plus `train_*.txt` and `verify_*.txt`).

## COFRS-level reading (minimal)

- `obs_barrier_ok=True` is the empirical analogue of a fiber witness: same `obs`, incompatible truths.
- Passing the strict verifier on IID ∪ OOD exhibits an empirical “lift exists” result under the declared training protocol.
