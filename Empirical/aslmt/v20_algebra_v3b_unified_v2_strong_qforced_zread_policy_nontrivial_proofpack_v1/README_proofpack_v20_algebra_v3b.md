# v20 algebra v3b — Proof Pack (structural counterexamples)

This proofpack turns the v20 v3b algebra test into a **zero-counterexample** demonstration.

Unlike v19, the object here is not an episode transcript `F_τ`. The proof object is a set of
**structural counterexamples** for the mechanistic chain:

```text
cue → zread(detach) → action → res_bit(qforced) → target
```

## Claim (what is proved when it passes)

For both IID and OOD splits, the certifier enumerates a seeded family of paired contexts and checks:

- **Barrier (anti-shortcut):**
  - image must not depend on `h` when `k` is fixed,
  - cue must not depend on `k` when `h` is fixed.
- **Gate correctness (modelA):**
  - image-gate paired discrimination succeeds,
  - cue-gate paired discrimination succeeds.
- **Negative controls:**
  - image-only baseline must *not* succeed,
  - cue-only baseline must *not* succeed,
  - z-ablated modelA must *not* succeed,
  - swap(z) must follow the swapped target and must not keep the original target.

The certifier emits every failure as a per-context counterexample record.

The verifier passes iff **there are zero counterexamples**.

## Files

- Train (original v20): `aslmt_train_v20_algebra_v3b_seeded_pair_trainood_poswtdice_contractrank_diag_zread_policy_nontrivial.py`
- Certifier (proofpack): `certify_struct_aslmt_v20_algebra_v3b_proofpack.py`
- Verifier (proofpack): `verify_struct_aslmt_v20_algebra_v3b_proofpack.py`
- Campaign (snapshot+hash, autonomous): `aslmt_campaign_v20_algebra_v3b_proofpack.py`

## Run (single seed, n=8, z=8)

```bash
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v20_algebra_v3b_unified_v2_strong_qforced_zread_policy_nontrivial_proofpack_v1/aslmt_campaign_v20_algebra_v3b_proofpack.py \
  --python /home/frederick/.venvs/cofrs-gpu/bin/python3 \
  --device cuda \
  --profile solid \
  --seed-from 0 --seed-to 0 \
  --n-classes-list 8 \
  --z-classes-list 8 \
  --episodes 64 --seed-base 0 \
  --pair-n-ctx 64
```

Artifacts are written under:

`Empirical/aslmt/runs/aslmt_v20_algebra_v3b_proofpack_<ts>_<hash>/`

and the frozen sources under:

`Empirical/aslmt/runs/snapshots/aslmt_v20_algebra_v3b_proofpack_<ts>_<hash>/`

