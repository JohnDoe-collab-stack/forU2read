# v20 algebra v3b — Proof Pack v5 (structural counterexamples + marginal no-go + minproof sweep; hardened image-gate)

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

## Marginal no-go add-on (environment-only)

v3 adds an environment-only proof object aligned with the “two marginals do not have access, but the joint does” spine:

- **image-only no-go:** for fixed `(ctx, k)`, varying `h` changes the hidden target while keeping `image` identical.
- **cue-only no-go:** for fixed `(ctx, h)`, varying `k` changes the hidden target while keeping `cue_image` identical.

The verifier passes iff there are **zero counterexamples** for these two no-go checks (IID and OOD).

## Minproof add-on (finite mediator collision witnesses)

In addition to the structural counterexample suite, v2 adds a second proof object:

- a **minproof certificate** that searches for a concrete `h0≠h1` such that `argmax(z_logits(h0)) = argmax(z_logits(h1))`,
  and then exhibits a **forced paired-discrimination failure** under fixed `(image, k)` because the decoder input is identical
  (`image + one_hot(z) + one_hot(k)`).

This is intended to align the experimental story with the “minimal finite mediator” spine (finite supplement + no smaller compression),
by producing explicit collision witnesses when `z_classes` is too small.

## Files

- Train (original v20): `aslmt_train_v20_algebra_v3b_seeded_pair_trainood_poswtdice_contractrank_diag_zread_policy_nontrivial.py`
- Certifier (proofpack): `certify_struct_aslmt_v20_algebra_v3b_proofpack.py`
- Verifier (proofpack): `verify_struct_aslmt_v20_algebra_v3b_proofpack.py`
- Certifier (marginal no-go): `certify_marginal_nogo_aslmt_v20_algebra_v3b_proofpack.py`
- Verifier (marginal no-go): `verify_marginal_nogo_aslmt_v20_algebra_v3b_proofpack.py`
- Certifier (minproof): `certify_minproof_aslmt_v20_algebra_v3b_proofpack.py`
- Verifier (minproof): `verify_minproof_aslmt_v20_algebra_v3b_proofpack.py`
- Campaign (snapshot+hash, autonomous): `aslmt_campaign_v20_algebra_v3b_proofpack.py`

## Run (single seed, n=8, z=8)

```bash
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v20_algebra_v3b_unified_v2_strong_qforced_zread_policy_nontrivial_proofpack_v5/aslmt_campaign_v20_algebra_v3b_proofpack.py \
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

`Empirical/aslmt/runs/aslmt_v20_algebra_v3b_proofpack_v5_<ts>_<hash>/`

and the frozen sources under:

`Empirical/aslmt/runs/snapshots/aslmt_v20_algebra_v3b_proofpack_v5_<ts>_<hash>/`
