# law_v3b_unified_v2_strong_qforced_zread_policy_nontrivial

Goal: add an orthogonal v3b axis where the **correct query interface** is selected by a **non-trivial policy**
`policy(h) ∈ {0,1}` (deterministic bit-mixing), rather than the simple parity rule `h % 2`.

This keeps the core qforced_zread protocol unchanged:
- same witness geometry (double barrier),
- same action-conditioned response bit (`k` if action is correct, else `0`),
- same discrete mediator `z`,
- same ablation/swap causal gates and strict verifier.

Only the supervised query target changes from `h % 2` to `policy(h)`.

## Run (solid)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  law_v3b_unified_v2_strong_qforced_zread_policy_nontrivial/aslmt_campaign_law_v3b_unified_v2_strong_qforced_zread_policy_nontrivial_matrix_diagstop_v1.py \
  --profile solid \
  --device cuda \
  --seed-from 0 --seed-to 4 \
  --n-classes-list 8 \
  --steps 9000
```

## Results (solid)

Run directory:
- `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_law_v3b_unified_v2_strong_qforced_zread_policy_nontrivial_solid_20260427_141932_8eec3ea2e04e`

Artifacts:
- `master.jsonl`:
  - `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_law_v3b_unified_v2_strong_qforced_zread_policy_nontrivial_solid_20260427_141932_8eec3ea2e04e/law_v3b_unified_v2_strong_qforced_zread_policy_nontrivial_solid_master_20260427_141932_8eec3ea2e04e.jsonl`
- `verify.txt`:
  - `/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/runs/aslmt_law_v3b_unified_v2_strong_qforced_zread_policy_nontrivial_solid_20260427_141932_8eec3ea2e04e/verify_20260427_141932_8eec3ea2e04e.txt`

Verifier status:
- `[OK] law_v3b_unified_v2_strong matrix checks passed.`

Matrix executed (A1 z-policy):
- `n=8`, seeds `0..4`, `z ∈ {8, 7, 4}`.

### Ref gate (z = n = 8): strict causal signature over IID+OOD

The verifier enforces the full law_v3b causal signature at `z=n` (exact equalities over all seeds):
- barriers ok (`obs_image_barrier_ok=true` and `obs_cue_barrier_ok=true`)
- `A_both_image_pair_rate = 1.0`
- `A_both_cue_pair_rate = 1.0`
- `A_swap_follow_image_pair_rate = 1.0`
- `A_swap_orig_both_image_pair_rate = 0.0`
- `A_ablated_both_image_pair_rate = 0.0`
- `B_image_only_both_rate = 0.0`
- `B_cue_only_both_rate = 0.0`
- plus balance constraints: `q_acc ≥ 0.90`, `res_acc ≥ 0.90`, and `query_action_rate` bounded away from 0/1.

Empirical minima/maxima over seeds (both IID and OOD):
- IID:
  - `A_img_min=1.0`, `A_cue_min=1.0`, `swap_follow_min=1.0`, `swap_orig_max=0.0`, `abl_img_max=0.0`
  - `Bimg_max=0.0`, `Bcue_max=0.0`
  - `q_acc_min=1.0`, `res_acc_min=1.0`, `query_action_rate ∈ [0.4795, 0.5205]`
- OOD:
  - `A_img_min=1.0`, `A_cue_min=1.0`, `swap_follow_min=1.0`, `swap_orig_max=0.0`, `abl_img_max=0.0`
  - `Bimg_max=0.0`, `Bcue_max=0.0`
  - `q_acc_min=1.0`, `res_acc_min=1.0`, `query_action_rate ∈ [0.4971, 0.5107]`

### Subcapacity diagnostic (z ∈ {7, 4})

For `z<n`, this matrix verifier keeps the task validity checks (barriers) and enforces a single diagnostic:
the ref-gate signature is not reproduced at lower capacity. Concretely, it checks `A_both_image_pair_rate < 1.0`
over IID+OOD.

Observed minima over seeds:
- `z=7`:
  - IID `A_img_min=0.875`, OOD `A_img_min=0.90625`
- `z=4`:
  - IID `A_img_min=0.765625`, OOD `A_img_min=0.71875`
