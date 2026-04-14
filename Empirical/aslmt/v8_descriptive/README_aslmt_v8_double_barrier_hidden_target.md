# ASLMT v8 — Double-Barrier (Image-only + Cue-only) Hidden-Target Witness

V8 generalizes v7 by enforcing a **double structural barrier**:

1. `image` alone is insufficient,
2. `cue_image` alone is insufficient,
3. `(cue_image, image)` together are sufficient.

The intended read is: the correct hidden completion is not carried by the decision-time visible interface alone,
and it is not carried by the cue alone; correctness requires a mediated composition of past and present.

## Core property (double structural barrier)

We introduce two independent bits:

- `h` (hidden / past bit), carried only by `cue_image`.
- `k` (present bit), carried only by `image`.

The hidden-only target inside the occluder depends on both bits via XOR:

- `target = PLUS` iff `h XOR k = 0`
- `target = RING` iff `h XOR k = 1`

Therefore:

- Holding `(k, scaffold, occluder)` fixed and flipping `h` yields **same image, different target**.
- Holding `(h, scaffold, occluder)` fixed and flipping `k` yields **same cue, different target**.

## Files

- `aslmt_env_v8_double_barrier_hidden_target.py`
- `aslmt_model_v8_double_barrier_jepa.py`
- `render_v8_paired_ctx.py`

Pair-grade (canonical objective: universal image-only no-go + universal cue-only no-go + sufficiency, OOD-required):

- `aslmt_campaign_v8_double_barrier_hidden_target_pair_oodrequired_v1.py`
- `aslmt_train_v8_double_barrier_hidden_target_seeded_pair_trainood.py`
- `verify_aslmt_v8_double_barrier_hidden_target_pair_oodrequired.py`

Pair-grade + causal gates (recommended for the COFRS “mediation is testable” clause):

- `aslmt_campaign_v8_double_barrier_hidden_target_pair_oodrequired_causalgate.py`
- `aslmt_train_v8_double_barrier_hidden_target_seeded_pair_trainood_causalgate.py`
- `verify_aslmt_v8_double_barrier_hidden_target_pair_oodrequired_causalgate.py`

## Run

```bash
cd /mnt/c/Users/frederick/Documents/Compatibility_Obstructions_in_Fibered_Relational_Systems/Python/private/aslmt
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u v8_descriptive/aslmt_campaign_v8_double_barrier_hidden_target_pair_oodrequired_v1.py \
  --train-script aslmt_train_v8_double_barrier_hidden_target_seeded_pair_trainood.py \
  --train-ood-ratio 0.5 \
  --steps 3000 \
  --device cuda \
  --seed 0
```

## Run (causal-gated reference)

```bash
cd /mnt/c/Users/frederick/Documents/Compatibility_Obstructions_in_Fibered_Relational_Systems/Python/private/aslmt
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u v8_descriptive/aslmt_campaign_v8_double_barrier_hidden_target_pair_oodrequired_causalgate.py \
  --profile solid \
  --seed 0 \
  --device cuda
```

## Reference run ([OK], causal-gated)

Run directory:

- `runs/aslmt_v8_pair_oodrequired_causalgate_20260414_174655_217093f0f527`

Re-verify from the frozen snapshot:

```bash
cd /mnt/c/Users/frederick/Documents/Compatibility_Obstructions_in_Fibered_Relational_Systems/Python/private/aslmt
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  runs/snapshots/aslmt_v8_pair_oodrequired_causalgate_20260414_174655_217093f0f527/verify_aslmt_v8_double_barrier_hidden_target_pair_oodrequired_causalgate.py \
  --master-jsonl runs/aslmt_v8_pair_oodrequired_causalgate_20260414_174655_217093f0f527/v8_master_20260414_174655_217093f0f527.jsonl
```

## Goal gates (pair-grade)

The strict verifier checks, on both IID and OOD paired contexts:

- `obs_image_barrier_ok == true`
- `obs_cue_barrier_ok == true`
- `A_both_image_pair_rate == 1.0`
- `A_both_cue_pair_rate == 1.0`
- `B_image_only_both_rate == 0.0` (on the image-barrier pair)
- `B_cue_only_both_rate == 0.0` (on the cue-barrier pair)
