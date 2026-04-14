## ASLMT law-v3b: Hard OOD on Mask/View Distribution (Balanced Split; Same Task, Same Vocabulary)

Goal: keep the *task* identical (query must recover hidden `hi` class; final output must recover the bit),
but make OOD harder than a delay/length shift by changing the **distribution of views**.

Key design:
- Each view explicitly encodes a GF(2) mask over `hi` bits (as tokens) and the parity `mask · hi`.
- The query-time visible remains `lo_tok` (structurally insufficient).
- IID and OOD use the same token vocabulary, but draw their mask-sets from disjoint subsets of the same full-rank pool.
- In this v3b, **all views** follow this rule (no "extra views" from a shared distribution).

Note on what is (and is not) disjoint in OOD:
- The disjointness is enforced at the level of **full-rank blocks** (ordered tuples of masks) drawn from disjoint index ranges.
- Individual atomic masks may still appear on both sides; what differs IID→OOD is the **composition/ordering of constraint blocks**.

This tests: can the model generalize the *inference mechanism* from parity constraints, rather than memorize one fixed mask schedule.

Interpretation of outcomes:
If a run shows strong causal dependence on memory, for example a large ablation drop and swap consistency, but still fails under hard OOD masks, the correct conclusion is not that mediation is absent.
The correct conclusion is that the mediator exists and is causally used, but the mediator is not yet stable enough as an invariant under the harder structural OOD.
This is the specific separation that `law_v3b` is meant to detect without changing the task or the token vocabulary.

Split note (why v3b exists):
- For C0 (`n_hi_bits=2`), the full-rank pool has only 6 tuples, so a contiguous index cut can induce biased marginals and make C0 sensitive to enumeration artifacts.
- v3b uses an explicit balanced 3/3 split for C0:
  IID={(1,2),(2,3),(3,1)}, OOD={(1,3),(2,1),(3,2)}.
- For `n_hi_bits >= 3`, v3b uses a deterministic seed-shuffled alternation IID/OOD instead of a contiguous index cut.

### Run (solid, seeds 0..4, CUDA)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u law_v3b/aslmt_campaign_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py \
  --profile solid --seed-from 0 --seed-to 4 --device cuda

python3 -u law_v3b/verify_aslmt_campaign_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py \
  --master-jsonl runs/<RUN_DIR>/master_<TS>_<HASH>.jsonl
```
