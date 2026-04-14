import argparse
import json
import sys


def verify(master_jsonl: str) -> None:
    with open(master_jsonl, "r", encoding="utf-8") as f:
        rows = [json.loads(line) for line in f if line.strip()]
    if not rows:
        print("No lines found in master jsonl.")
        sys.exit(1)

    # Strict: OOD must be present and perfect.
    min_pair_iid_n = 10**9
    min_pair_iid_obs_barrier_ok = True
    min_pair_iid_A_both = 1.0
    max_pair_iid_B_both = 0.0

    min_pair_ood_n = 10**9
    min_pair_ood_obs_barrier_ok = True
    min_pair_ood_A_both = 1.0
    max_pair_ood_B_both = 0.0

    for r in rows:
        pair = r.get("pair_eval", {})
        iid = pair.get("iid", {})
        ood = pair.get("ood", {})

        if not iid:
            print("pair_eval.iid missing in a master jsonl row")
            sys.exit(1)
        if not ood:
            print("pair_eval.ood missing in a master jsonl row (OOD is required)")
            sys.exit(1)

        min_pair_iid_n = min(min_pair_iid_n, int(iid["n_ctx"]))
        min_pair_iid_obs_barrier_ok = bool(min_pair_iid_obs_barrier_ok and bool(iid["obs_barrier_ok"]))
        min_pair_iid_A_both = min(min_pair_iid_A_both, float(iid["A_both_correct_rate"]))
        max_pair_iid_B_both = max(max_pair_iid_B_both, float(iid["B_both_correct_rate"]))

        min_pair_ood_n = min(min_pair_ood_n, int(ood["n_ctx"]))
        min_pair_ood_obs_barrier_ok = bool(min_pair_ood_obs_barrier_ok and bool(ood["obs_barrier_ok"]))
        min_pair_ood_A_both = min(min_pair_ood_A_both, float(ood["A_both_correct_rate"]))
        max_pair_ood_B_both = max(max_pair_ood_B_both, float(ood["B_both_correct_rate"]))

    errors = []

    if not min_pair_iid_obs_barrier_ok:
        errors.append("pair_eval.iid.obs_barrier_ok is false in some row")
    if min_pair_iid_A_both < 1.0:
        errors.append(f"pair_eval.iid.A_both_correct_rate min={min_pair_iid_A_both:.4f} < 1.0000")
    if max_pair_iid_B_both > 0.0:
        errors.append(f"pair_eval.iid.B_both_correct_rate max={max_pair_iid_B_both:.4f} > 0.0000")

    if not min_pair_ood_obs_barrier_ok:
        errors.append("pair_eval.ood.obs_barrier_ok is false in some row")
    if min_pair_ood_A_both < 1.0:
        errors.append(f"pair_eval.ood.A_both_correct_rate min={min_pair_ood_A_both:.4f} < 1.0000")
    if max_pair_ood_B_both > 0.0:
        errors.append(f"pair_eval.ood.B_both_correct_rate max={max_pair_ood_B_both:.4f} > 0.0000")

    print(
        "[V7 Pair-Grade OOD-Required] "
        f"iid(n_ctx_min={min_pair_iid_n}, obs_barrier_ok={min_pair_iid_obs_barrier_ok}, "
        f"A_both_min={min_pair_iid_A_both:.4f}, B_both_max={max_pair_iid_B_both:.4f}) | "
        f"ood(n_ctx_min={min_pair_ood_n}, obs_barrier_ok={min_pair_ood_obs_barrier_ok}, "
        f"A_both_min={min_pair_ood_A_both:.4f}, B_both_max={max_pair_ood_B_both:.4f})"
    )

    if errors:
        print("\n[FAIL] V7 pair-grade OOD-required checks did not pass:")
        for e in errors:
            print(f" - {e}")
        sys.exit(1)

    print("\n[OK] V7 pair-grade OOD-required checks passed.")
    sys.exit(0)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--master-jsonl", type=str, required=True)
    args = parser.parse_args()
    verify(args.master_jsonl)

