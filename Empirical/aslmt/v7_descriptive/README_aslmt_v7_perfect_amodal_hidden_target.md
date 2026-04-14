# ASLMT v7 — Perfect Amodal (Hidden-Target) Witness

This version fixes the main design flaw of v6:
in v6 the segmentation objective and IoU metric were dominated by the visible scaffold,
so a visible-only baseline could score high without resolving the hidden completion.

V7 makes the target explicitly be the **hidden completion inside the occluder**.
This forces the evaluation to measure the barrier we actually care about:
can a stateful model carry the cue forward and reconstruct the hidden content,
while a visible-only model (final image only) cannot.

## Core property (structural visible-only barrier)

- The final visible image is identical for both hidden classes once scaffold+occluder are fixed.
- The earlier cue frame reveals which hidden completion is correct.
- Therefore any policy that decides from the final visible image alone is structurally insufficient.

## Files

- `aslmt_env_v7_perfect_amodal_hidden_target.py`
- `aslmt_model_v7_perfect_jepa.py`
- `render_v7_paired_ctx.py` (paired witness: `image_equal=true`, `hidden_target_equal=false`)

Pair-grade (canonical objective: universal obs-only no-go + minimal lift, OOD-required):

- `aslmt_campaign_v7_perfect_amodal_hidden_target_pair_oodrequired_v2.py` (recommended; hygiene fix: deduplicated `manifest.files`)
- `aslmt_campaign_v7_perfect_amodal_hidden_target_pair_oodrequired.py` (legacy runner; kept to avoid rewriting historical artifacts)
- `aslmt_train_v7_perfect_amodal_hidden_target_seeded_pair_trainood.py`
- `verify_aslmt_v7_perfect_amodal_hidden_target_pair_oodrequired.py`

Optional / diagnostic:

- Pair (non OOD-required) + IID-only variants (not canonical): see `variants/pair/`
- IoU diagnostic pipeline (not canonical): see `variants/single/`
- Context-failure audit (adds `A_fail_ctxs` under `pair_eval` in the master JSONL; verifier ignores it):
  - `variants/pair/aslmt_train_v7_perfect_amodal_hidden_target_seeded_pair_trainood_ctxaudit.py`

## Run

```bash
cd /mnt/c/Users/frederick/Documents/Compatibility_Obstructions_in_Fibered_Relational_Systems/Python/private/aslmt
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u v7_descriptive/aslmt_campaign_v7_perfect_amodal_hidden_target_pair_oodrequired_v2.py \
  --train-script aslmt_train_v7_perfect_amodal_hidden_target_seeded_pair_trainood.py \
  --train-ood-ratio 0.5 \
  --steps 3000 \
  --device cuda \
  --seed 0
```

## Run (ctx-audit variant)

This produces the usual `v7_master_*.jsonl` plus a list of the IID contexts where A fails the both-correct condition:
`pair_eval.iid.A_fail_ctxs`.

```bash
cd /mnt/c/Users/frederick/Documents/Compatibility_Obstructions_in_Fibered_Relational_Systems/Python/private/aslmt
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u v7_descriptive/aslmt_campaign_v7_perfect_amodal_hidden_target_pair_oodrequired_v2.py \
  --train-script variants/pair/aslmt_train_v7_perfect_amodal_hidden_target_seeded_pair_trainood_ctxaudit.py \
  --train-ood-ratio 1.0 \
  --steps 3000 \
  --device cuda \
  --seed 0
```

## Interpretation of the ctx-audit (what it establishes)

Under `train_ood_ratio=1.0` (OOD-only training), we repeatedly observe:

- `pair_eval.ood.A_both_correct_rate = 1.0` (perfect on OOD contexts),
- but `pair_eval.iid.A_both_correct_rate < 1.0` (fails the protocol-grade requirement on IID).

The ctx-audit pinpoints *where* IID fails: in a representative run, all IID failures concentrated on
the *frontier* context parameters `occ_half=5` and `t=2`, and all failures were on the RING member of the pair
(PLUS remained correct). This turns “OOD-only breaks IID” into an auditable statement about minimal family coverage.

## Next study: minimal training coverage for protocol-grade perfection (IID ∪ OOD)

Goal: find the largest `train_ood_ratio` that still yields `[OK]` under the strict OOD-required verifier
(i.e. minimal IID coverage that closes IID ∪ OOD).

Recommended sweep (each point produces a snapshot+hash run dir and runs the strict verifier):

```bash
cd /mnt/c/Users/frederick/Documents/Compatibility_Obstructions_in_Fibered_Relational_Systems/Python/private/aslmt

for r in 0.50 0.75 0.90 0.95 0.99 1.00; do
  /home/frederick/.venvs/cofrs-gpu/bin/python3 -u v7_descriptive/aslmt_campaign_v7_perfect_amodal_hidden_target_pair_oodrequired_v2.py \
    --train-script variants/pair/aslmt_train_v7_perfect_amodal_hidden_target_seeded_pair_trainood_ctxaudit.py \
    --train-ood-ratio "$r" \
    --steps 3000 \
    --device cuda \
    --seed 0
done
```

This folder is the only entrypoint for the “Descriptive v7” witness. Do not run the legacy `v7/` scripts.
