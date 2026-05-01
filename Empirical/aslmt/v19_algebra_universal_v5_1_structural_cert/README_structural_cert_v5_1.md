# v19 universal v5.1 — Structural Certificate Test (threshold-free)

This folder contains a **certificate-based** empirical test of the claim:

> An agent performs **controlled closure** (objective `Amb_σ(F_τ)=1` at STOP) and then **reads the unique branch**.

Acceptance is **not** by aggregate score thresholds. Instead, we produce episode-level JSONL certificates and run an
independent structural verifier that searches for counterexamples to P1–P5.

Files:

- `certify_struct_aslmt_v19_algebra_universal_v5_1.py`:
  Generates per-episode certificates for a frozen benchmark (`iid` / `ood`).
- `verify_struct_aslmt_v19_algebra_universal_v5_1.py`:
  Verifies P1–P5 exactly from each certificate; exits non-zero if any counterexample exists.
- `aslmt_campaign_v19_algebra_universal_v5_1_structural.py`:
  Snapshots the scripts (timestamp+hash), generates certificates, and verifies them.

Notes:

- This folder intentionally **vendors** (`copies`) the v5.1 environment / oracle / model modules so that snapshot runs
  are self-contained and import-stable.

