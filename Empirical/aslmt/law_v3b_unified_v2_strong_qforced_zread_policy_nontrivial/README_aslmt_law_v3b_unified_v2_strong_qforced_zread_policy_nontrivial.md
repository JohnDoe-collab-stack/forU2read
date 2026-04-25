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

