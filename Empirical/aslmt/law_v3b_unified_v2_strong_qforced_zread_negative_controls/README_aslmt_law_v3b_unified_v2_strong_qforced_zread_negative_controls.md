# law_v3b_unified_v2_strong_qforced_zread_negative_controls

Goal: close **v3b negative controls** for the `qforced_zread` protocol with a small, self-contained pack.

Each negative control is designed to violate a specific part of the strict verifier contract, while keeping the rest
of the protocol unchanged.

This folder contains:
- local copies of the `qforced_zread` model/env/render/verifier (so the run snapshots are self-contained),
- three negative-control variants,
- a pack campaign runner that expects the strict verifier to **fail** for each negative control.

## Negative controls in this pack

1. `forced_action0`:
   the query action is forced to constant `0` (so `q_acc` and action-rate constraints fail in `solid`).

2. `cue_zero`:
   `cue_image` is zeroed at render time (so the mediator `z` is not learnable and query becomes ungrounded).

3. `leak_h_to_image`:
   `h` is leaked into `image` (image barrier fails: `obs_image_barrier_ok = false`).

## Run (recommended: solid, 1 seed)

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt

/home/frederick/.venvs/cofrs-gpu/bin/python3 -u \
  law_v3b_unified_v2_strong_qforced_zread_negative_controls/aslmt_campaign_law_v3b_unified_v2_strong_qforced_zread_negative_controls_pack_v1.py \
  --profile solid \
  --device cuda \
  --seed-from 0 --seed-to 0 \
  --n-classes 8 \
  --steps 9000
```

The campaign writes verifier output for each variant and checks that the verifier **returns non-zero**.
If the verifier unexpectedly passes for any negative control, the campaign aborts with exit code 2.

