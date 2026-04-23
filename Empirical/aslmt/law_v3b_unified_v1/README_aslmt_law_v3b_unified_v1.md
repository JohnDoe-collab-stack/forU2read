# ASLMT law_v3b_unified_v1

This folder defines a new, autonomous v3b-style solver over the unified double-barrier, min-lift witness
with strict pair-grade closure on a 64-context contract (IID and OOD).

Scope

- Keep the v3b spine: internal state, query action, action-conditioned response, post-query state, decision.
- Keep the existing empirical contracts: barrier validity, strict closure at 1.0, min-lift, and causal gates (ablation and swap).
- Keep traceability: snapshot plus hash, execution from snapshot, diagstop, checkpoint and faildump on any strict miss.

Files

- `render_law_v3b_unified_v1_paired_ctx_nscalable_spaced2_64.py`
  - n-scalable spaced2_64 renderer with contract-preserving OOD cue corruption.
- `aslmt_env_law_v3b_unified_v1_nscalable_spaced2_64.py`
  - dataset wrapper over the renderer.
- `aslmt_model_law_v3b_unified_v1_query.py`
  - model A with a v3b-style query step:
    - query action is computed from cue-only internal state
    - response is action-conditioned (image visible channel is zeroed when action=0)
    - decision is decoded from post-query state
  - baselines B image-only and cue-only.
- `aslmt_train_law_v3b_unified_v1_seeded_pair_trainood_poswtdice_contractrank_diag.py`
  - training, pair-grade eval, ablation and swap gates, checkpoint saving, and faildump writing.
- `verify_aslmt_law_v3b_unified_v1_matrix.py`
  - strict matrix verifier for the master JSONL.
- `aslmt_campaign_law_v3b_unified_v1_matrix_diagstop.py`
  - snapshot plus hash campaign runner (diagstop on strict reference miss).
- `aslmt_postmortem_law_v3b_unified_v1_from_ckpt_dump.py`
  - postmortem dumper from a saved checkpoint and snapshot dir.

Run (solid, CUDA)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  law_v3b_unified_v1/aslmt_campaign_law_v3b_unified_v1_matrix_diagstop.py \
  --profile solid \
  --device cuda \
  --seed-from 0 --seed-to 4 \
  --n-classes-list 8,12,16 \
  --steps 9000 \
  --w-z 5.0 --w-k 0.0 \
  --w-pos 0.25 \
  --w-rank-img 0.25 --w-rank-cue 0.25 \
  --rank-n-ctx 8 --rank-margin 1.0 --rank-ood-ratio 0.5 \
  --w-dice 0.25 --w-bce 1.0 --bce-pos-weight batch
```

Run (smoke)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

python3 -u law_v3b_unified_v1/aslmt_campaign_law_v3b_unified_v1_matrix_diagstop.py \
  --profile smoke \
  --device cpu \
  --seed-from 0 --seed-to 0 \
  --n-classes-list 8 \
  --w-z 5.0 --w-k 0.0 \
  --w-pos 0.25 \
  --w-rank-img 0.25 --w-rank-cue 0.25 \
  --rank-n-ctx 1 --rank-margin 1.0 --rank-ood-ratio 0.5 \
  --w-dice 0.25 --w-bce 1.0 --bce-pos-weight batch
```
