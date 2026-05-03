## ASLMT v20 (algebra) — v3b architecture (zread, qforced, policy_nontrivial)

This `v20` bundle is the **algebra test** implemented with the **strict v3b architecture** (no simplifications).

### What is the algebra here?

We work on a finite latent space whose relevant open branch is the bit `k ∈ {0,1}` after reading the cue.

- The cue reveals `h` (position class), but not `k`.
- The image is occluded: image-only cannot reveal the hidden target.
- A query selects an interface `a ∈ {0,1}`.
- The response bit is action-dependent:
  - if `a = policy(h)`, then `res_bit = k` (informative),
  - else `res_bit` is non-informative about `k`.

So the residual ambiguity over the target branch (`k`) contracts exactly when the correct interface is selected.

### Architecture invariants (must hold)

1) `cue_image → z_logits → z_hard` where `z_hard` is straight-through one-hot.

2) **zread**:

`query_logits := f(one_hot(argmax(z_logits.detach())))`

So query supervision does not backprop into `z_mlp`.

3) `action := argmax(query_logits)` (two actions / two interfaces).

4) `res_bit := env_res_bit(h,k,action)` follows the v3b law above.

5) Decoder predicts the hidden target by conditioning on `(image, z, res_bit)` via a U-Net.

### Files

- Renderer: `render_aslmt_v20_algebra_v3b_paired_ctx_nscalable_spaced2_64.py`
- Dataset/env: `aslmt_env_v20_algebra_v3b_nscalable_spaced2_64.py`
- Model: `aslmt_model_v20_algebra_v3b_query_zread.py`
- Trainer: `aslmt_train_v20_algebra_v3b_seeded_pair_trainood_poswtdice_contractrank_diag_zread_policy_nontrivial.py`
- Independent algebra audit: `audit_aslmt_v20_algebra_v3b.py`
- Strict verifier: `verify_aslmt_v20_algebra_v3b_matrix.py`
- Campaign (snapshot+hash): `aslmt_campaign_v20_algebra_v3b_matrix.py`

### Smoke run

```bash
python3 -u aslmt_campaign_v20_algebra_v3b_matrix.py \
  --profile smoke \
  --device cuda \
  --python /home/frederick/.venvs/cofrs-gpu/bin/python3 \
  --seed-from 0 --seed-to 0 \
  --n-classes-list 8 \
  --z-policy explicit --z-classes-list 8
```

### Solid run

```bash
python3 -u aslmt_campaign_v20_algebra_v3b_matrix.py \
  --profile solid \
  --device cuda \
  --python /home/frederick/.venvs/cofrs-gpu/bin/python3 \
  --seed-from 0 --seed-to 4 \
  --n-classes-list 8 \
  --z-policy A1
```

