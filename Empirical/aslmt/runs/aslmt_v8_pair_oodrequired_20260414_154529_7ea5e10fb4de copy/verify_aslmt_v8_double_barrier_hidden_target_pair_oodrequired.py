import argparse
import json
import sys


def verify(master_jsonl: str) -> None:
    with open(master_jsonl, "r", encoding="utf-8") as f:
        rows = [json.loads(line) for line in f if line.strip()]
    if not rows:
        print("No lines found in master jsonl.")
        sys.exit(1)

    # Strict: OOD must be present and perfect for both barriers.
    min_iid_n = 10**9
    iid_img_barrier_ok = True
    iid_cue_barrier_ok = True
    iid_A_img_min = 1.0
    iid_A_cue_min = 1.0
    iid_B_img_max = 0.0
    iid_B_cue_max = 0.0

    min_ood_n = 10**9
    ood_img_barrier_ok = True
    ood_cue_barrier_ok = True
    ood_A_img_min = 1.0
    ood_A_cue_min = 1.0
    ood_B_img_max = 0.0
    ood_B_cue_max = 0.0

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

        min_iid_n = min(min_iid_n, int(iid["n_ctx"]))
        iid_img_barrier_ok = bool(iid_img_barrier_ok and bool(iid["obs_image_barrier_ok"]))
        iid_cue_barrier_ok = bool(iid_cue_barrier_ok and bool(iid["obs_cue_barrier_ok"]))
        iid_A_img_min = min(iid_A_img_min, float(iid["A_both_image_pair_rate"]))
        iid_A_cue_min = min(iid_A_cue_min, float(iid["A_both_cue_pair_rate"]))
        iid_B_img_max = max(iid_B_img_max, float(iid["B_image_only_both_rate"]))
        iid_B_cue_max = max(iid_B_cue_max, float(iid["B_cue_only_both_rate"]))

        min_ood_n = min(min_ood_n, int(ood["n_ctx"]))
        ood_img_barrier_ok = bool(ood_img_barrier_ok and bool(ood["obs_image_barrier_ok"]))
        ood_cue_barrier_ok = bool(ood_cue_barrier_ok and bool(ood["obs_cue_barrier_ok"]))
        ood_A_img_min = min(ood_A_img_min, float(ood["A_both_image_pair_rate"]))
        ood_A_cue_min = min(ood_A_cue_min, float(ood["A_both_cue_pair_rate"]))
        ood_B_img_max = max(ood_B_img_max, float(ood["B_image_only_both_rate"]))
        ood_B_cue_max = max(ood_B_cue_max, float(ood["B_cue_only_both_rate"]))

    errors = []

    if not iid_img_barrier_ok:
        errors.append("pair_eval.iid.obs_image_barrier_ok is false in some row")
    if not iid_cue_barrier_ok:
        errors.append("pair_eval.iid.obs_cue_barrier_ok is false in some row")
    if iid_A_img_min < 1.0:
        errors.append(f"pair_eval.iid.A_both_image_pair_rate min={iid_A_img_min:.4f} < 1.0000")
    if iid_A_cue_min < 1.0:
        errors.append(f"pair_eval.iid.A_both_cue_pair_rate min={iid_A_cue_min:.4f} < 1.0000")
    if iid_B_img_max > 0.0:
        errors.append(f"pair_eval.iid.B_image_only_both_rate max={iid_B_img_max:.4f} > 0.0000")
    if iid_B_cue_max > 0.0:
        errors.append(f"pair_eval.iid.B_cue_only_both_rate max={iid_B_cue_max:.4f} > 0.0000")

    if not ood_img_barrier_ok:
        errors.append("pair_eval.ood.obs_image_barrier_ok is false in some row")
    if not ood_cue_barrier_ok:
        errors.append("pair_eval.ood.obs_cue_barrier_ok is false in some row")
    if ood_A_img_min < 1.0:
        errors.append(f"pair_eval.ood.A_both_image_pair_rate min={ood_A_img_min:.4f} < 1.0000")
    if ood_A_cue_min < 1.0:
        errors.append(f"pair_eval.ood.A_both_cue_pair_rate min={ood_A_cue_min:.4f} < 1.0000")
    if ood_B_img_max > 0.0:
        errors.append(f"pair_eval.ood.B_image_only_both_rate max={ood_B_img_max:.4f} > 0.0000")
    if ood_B_cue_max > 0.0:
        errors.append(f"pair_eval.ood.B_cue_only_both_rate max={ood_B_cue_max:.4f} > 0.0000")

    print(
        "[V8 Pair-Grade OOD-Required] "
        f"iid(n_ctx_min={min_iid_n}, img_barrier_ok={iid_img_barrier_ok}, cue_barrier_ok={iid_cue_barrier_ok}, "
        f"A_img_min={iid_A_img_min:.4f}, A_cue_min={iid_A_cue_min:.4f}, "
        f"B_img_max={iid_B_img_max:.4f}, B_cue_max={iid_B_cue_max:.4f}) | "
        f"ood(n_ctx_min={min_ood_n}, img_barrier_ok={ood_img_barrier_ok}, cue_barrier_ok={ood_cue_barrier_ok}, "
        f"A_img_min={ood_A_img_min:.4f}, A_cue_min={ood_A_cue_min:.4f}, "
        f"B_img_max={ood_B_img_max:.4f}, B_cue_max={ood_B_cue_max:.4f})"
    )

    if errors:
        print("\n[FAIL] V8 pair-grade OOD-required checks did not pass:")
        for e in errors:
            print(f" - {e}")
        sys.exit(1)

    print("\n[OK] V8 pair-grade OOD-required checks passed.")
    sys.exit(0)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--master-jsonl", type=str, required=True)
    args = parser.parse_args()
    verify(args.master_jsonl)
