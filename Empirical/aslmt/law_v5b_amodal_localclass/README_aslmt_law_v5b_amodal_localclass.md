# ASLMT law-v5b (amodal, local-class) — latent `z` vs a *class* of local *observable-only* baselines

This is a **v5b** variant of the v5 amodal completion witness.

What changes vs v5:
- v5 compared A against a *single* local FCN baseline B.
- v5b compares A against a **small declared class** of local *observable-only* baselines:
  - B1: local FCN (shallow)
  - B2: local FCN (much wider) with **the same fixed receptive-field bound** as B1 (RF=9), using extra 1x1 capacity without expanding locality
  - B3: window-local MLP (no cross-window communication)

What stays the same:
- same task + same environment family `C0_hard / C1_mid / C2_soft`
- A is state-locked: the head reads **only** a global latent `z`
- same OOD shift: large central occluder
- same causal audits on `z`: ablation (z=0) + swap (z permuted)

Claim scope:
- this remains a **locality ceiling** claim relative to the declared baseline class.
- closure gates are `C1_mid` and `C2_soft`; `C0_hard` is diagnostic.
 - precision on the input: baselines are "observable-only" in the sense "depend only on the current observable image". In v5b, that observable is the composite image `clamp(amodal + occluder, 0, 1)` (object ∪ occluder), not a masked "visible-only pixels" image.

## Run

Smoke (writes to `runs/*_smoke_*`):
```bash
cd /mnt/c/Users/frederick/Documents/Compatibility_Obstructions_in_Fibered_Relational_Systems/Python/private/aslmt
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u law_v5b_amodal_localclass/aslmt_campaign_law_v5b_amodal_localclass_family.py --profile smoke --seed 0 --device cuda
RUN_DIR="$(ls -td runs/aslmt_law_v5b_amodal_localclass_smoke_* | head -1)"
MASTER="$(ls "$RUN_DIR"/master_*.jsonl | head -1)"
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u law_v5b_amodal_localclass/verify_aslmt_campaign_law_v5b_amodal_localclass_family_strict_refgate.py --master-jsonl "$MASTER"
```

Solid multi-seeds:
```bash
cd /mnt/c/Users/frederick/Documents/Compatibility_Obstructions_in_Fibered_Relational_Systems/Python/private/aslmt
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u law_v5b_amodal_localclass/aslmt_campaign_law_v5b_amodal_localclass_family.py --profile solid --seed-from 0 --seed-to 4 --device cuda
RUN_DIR="$(ls -td runs/aslmt_law_v5b_amodal_localclass_* | head -1)"
MASTER="$(ls "$RUN_DIR"/master_*.jsonl | head -1)"
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u law_v5b_amodal_localclass/verify_aslmt_campaign_law_v5b_amodal_localclass_family_strict_refgate.py --master-jsonl "$MASTER"
```
