# v20 algebra v3b — Proof Pack v6

Structural counterexamples + marginal no-go + strengthened minproof sweep.

v6 fixes two proofpack hygiene issues from v5:

- structural baseline controls now use the **trained image-only and cue-only baselines saved in the checkpoint**;
- the minproof verifier now enforces the finite lower-bound obligation: when `z_classes < n_classes`,
  every certified context must carry a verified `h0≠h1` collision witness.
- the image/cue ranking losses now mirror the structural verifier's actual witnesses:
  fixed visible image, deterministic `h→h+1`, fixed `k`, verifier-distributed IID/OOD contexts,
  and swap(z) without swapping the environment `res_bit`.

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

In addition to the structural counterexample suite, the minproof certificate checks:

- a **minproof certificate** that searches for a concrete `h0≠h1` such that `argmax(z_logits(h0)) = argmax(z_logits(h1))`,
  and then exhibits a **forced paired-discrimination failure** under fixed `(image, k)` because the decoder input is identical
  (`image + one_hot(z) + one_hot(k)`).

In v6, this is no longer merely “accept whatever collisions were emitted”: if `z_classes < n_classes`, the verifier
requires a re-verified collision witness for every context. This is still an empirical finite certificate, not the
Lean theorem `CompatDimEq`; the intended alignment is:

```text
finite pigeonhole/collision witness in v6
≈ experimental lower-bound certificate for the finite mediator

CompatDimEq in Lean
= universal constructive theorem-level minimality statement
```

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
  /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v20_algebra_v3b_unified_v2_strong_qforced_zread_policy_nontrivial_proofpack_v6/aslmt_campaign_v20_algebra_v3b_proofpack.py \
  --python /home/frederick/.venvs/cofrs-gpu/bin/python3 \
  --device cuda \
  --profile solid \
  --seed-from 0 --seed-to 0 \
  --n-classes-list 8 \
  --z-classes-list 8 \
  --episodes 64 --seed-base 0 \
  --pair-n-ctx 64 \
  --rank-n-ctx 64
```

Artifacts are written under:

`Empirical/aslmt/runs/aslmt_v20_algebra_v3b_proofpack_v6_<ts>_<hash>/`

and the frozen sources under:

`Empirical/aslmt/runs/snapshots/aslmt_v20_algebra_v3b_proofpack_v6_<ts>_<hash>/`
