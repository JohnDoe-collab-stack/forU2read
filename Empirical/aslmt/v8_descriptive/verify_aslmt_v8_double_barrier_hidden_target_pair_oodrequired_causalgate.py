import argparse
import json


def _read_jsonl(path: str) -> list[dict]:
    rows = []
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            rows.append(json.loads(line))
    return rows


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--master-jsonl", type=str, required=True)
    args = p.parse_args()

    rows = _read_jsonl(args.master_jsonl)
    if not rows:
        raise SystemExit("empty master jsonl")

    errors: list[str] = []

    iid_n_min = 10**9
    ood_n_min = 10**9
    iid_img_bar_ok = True
    iid_cue_bar_ok = True
    ood_img_bar_ok = True
    ood_cue_bar_ok = True

    iid_A_img_min = 1.0
    iid_A_cue_min = 1.0
    iid_B_img_max = 0.0
    iid_B_cue_max = 0.0
    iid_A_abl_img_max = 0.0
    iid_A_swap_follow_min = 1.0
    iid_A_swap_orig_max = 0.0

    ood_A_img_min = 1.0
    ood_A_cue_min = 1.0
    ood_B_img_max = 0.0
    ood_B_cue_max = 0.0
    ood_A_abl_img_max = 0.0
    ood_A_swap_follow_min = 1.0
    ood_A_swap_orig_max = 0.0

    for r in rows:
        pair = r.get("pair_eval", {})
        iid = pair.get("iid", {})
        ood = pair.get("ood", {})
        if not iid:
            errors.append("pair_eval.iid missing in a master jsonl row")
            continue
        if not ood:
            errors.append("pair_eval.ood missing in a master jsonl row (OOD is required)")
            continue

        iid_n_min = min(iid_n_min, int(iid["n_ctx"]))
        ood_n_min = min(ood_n_min, int(ood["n_ctx"]))

        iid_img_bar_ok = bool(iid_img_bar_ok and bool(iid["obs_image_barrier_ok"]))
        iid_cue_bar_ok = bool(iid_cue_bar_ok and bool(iid["obs_cue_barrier_ok"]))
        ood_img_bar_ok = bool(ood_img_bar_ok and bool(ood["obs_image_barrier_ok"]))
        ood_cue_bar_ok = bool(ood_cue_bar_ok and bool(ood["obs_cue_barrier_ok"]))

        iid_A_img_min = min(iid_A_img_min, float(iid["A_both_image_pair_rate"]))
        iid_A_cue_min = min(iid_A_cue_min, float(iid["A_both_cue_pair_rate"]))
        iid_B_img_max = max(iid_B_img_max, float(iid["B_image_only_both_rate"]))
        iid_B_cue_max = max(iid_B_cue_max, float(iid["B_cue_only_both_rate"]))
        iid_A_abl_img_max = max(iid_A_abl_img_max, float(iid["A_ablated_both_image_pair_rate"]))
        iid_A_swap_follow_min = min(iid_A_swap_follow_min, float(iid["A_swap_follow_image_pair_rate"]))
        iid_A_swap_orig_max = max(iid_A_swap_orig_max, float(iid["A_swap_orig_both_image_pair_rate"]))

        ood_A_img_min = min(ood_A_img_min, float(ood["A_both_image_pair_rate"]))
        ood_A_cue_min = min(ood_A_cue_min, float(ood["A_both_cue_pair_rate"]))
        ood_B_img_max = max(ood_B_img_max, float(ood["B_image_only_both_rate"]))
        ood_B_cue_max = max(ood_B_cue_max, float(ood["B_cue_only_both_rate"]))
        ood_A_abl_img_max = max(ood_A_abl_img_max, float(ood["A_ablated_both_image_pair_rate"]))
        ood_A_swap_follow_min = min(ood_A_swap_follow_min, float(ood["A_swap_follow_image_pair_rate"]))
        ood_A_swap_orig_max = max(ood_A_swap_orig_max, float(ood["A_swap_orig_both_image_pair_rate"]))

    if iid_n_min < 64 or ood_n_min < 64:
        errors.append(f"n_ctx too small (iid_min={iid_n_min}, ood_min={ood_n_min}) < 64")

    if not (iid_img_bar_ok and iid_cue_bar_ok and ood_img_bar_ok and ood_cue_bar_ok):
        errors.append("barrier ok flags contain false")

    if iid_A_img_min < 1.0:
        errors.append(f"pair_eval.iid.A_both_image_pair_rate min={iid_A_img_min:.4f} < 1.0000")
    if iid_A_cue_min < 1.0:
        errors.append(f"pair_eval.iid.A_both_cue_pair_rate min={iid_A_cue_min:.4f} < 1.0000")
    if iid_B_img_max > 0.0:
        errors.append(f"pair_eval.iid.B_image_only_both_rate max={iid_B_img_max:.4f} > 0.0000")
    if iid_B_cue_max > 0.0:
        errors.append(f"pair_eval.iid.B_cue_only_both_rate max={iid_B_cue_max:.4f} > 0.0000")
    if iid_A_abl_img_max > 0.0:
        errors.append(f"pair_eval.iid.A_ablated_both_image_pair_rate max={iid_A_abl_img_max:.4f} > 0.0000")
    if iid_A_swap_follow_min < 1.0:
        errors.append(f"pair_eval.iid.A_swap_follow_image_pair_rate min={iid_A_swap_follow_min:.4f} < 1.0000")
    if iid_A_swap_orig_max >= 1.0:
        errors.append("pair_eval.iid.A_swap_orig_both_image_pair_rate is 1.0000 in some row (unexpected)")

    if ood_A_img_min < 1.0:
        errors.append(f"pair_eval.ood.A_both_image_pair_rate min={ood_A_img_min:.4f} < 1.0000")
    if ood_A_cue_min < 1.0:
        errors.append(f"pair_eval.ood.A_both_cue_pair_rate min={ood_A_cue_min:.4f} < 1.0000")
    if ood_B_img_max > 0.0:
        errors.append(f"pair_eval.ood.B_image_only_both_rate max={ood_B_img_max:.4f} > 0.0000")
    if ood_B_cue_max > 0.0:
        errors.append(f"pair_eval.ood.B_cue_only_both_rate max={ood_B_cue_max:.4f} > 0.0000")
    if ood_A_abl_img_max > 0.0:
        errors.append(f"pair_eval.ood.A_ablated_both_image_pair_rate max={ood_A_abl_img_max:.4f} > 0.0000")
    if ood_A_swap_follow_min < 1.0:
        errors.append(f"pair_eval.ood.A_swap_follow_image_pair_rate min={ood_A_swap_follow_min:.4f} < 1.0000")
    if ood_A_swap_orig_max >= 1.0:
        errors.append("pair_eval.ood.A_swap_orig_both_image_pair_rate is 1.0000 in some row (unexpected)")

    print(
        "[V8 Pair-Grade OOD-Required + Causal] "
        f"iid(n_ctx_min={iid_n_min}, img_barrier_ok={iid_img_bar_ok}, cue_barrier_ok={iid_cue_bar_ok}, "
        f"A_img_min={iid_A_img_min:.4f}, A_cue_min={iid_A_cue_min:.4f}, "
        f"B_img_max={iid_B_img_max:.4f}, B_cue_max={iid_B_cue_max:.4f}, "
        f"A_abl_img_max={iid_A_abl_img_max:.4f}, A_swap_follow_min={iid_A_swap_follow_min:.4f}, A_swap_orig_max={iid_A_swap_orig_max:.4f}) | "
        f"ood(n_ctx_min={ood_n_min}, img_barrier_ok={ood_img_bar_ok}, cue_barrier_ok={ood_cue_bar_ok}, "
        f"A_img_min={ood_A_img_min:.4f}, A_cue_min={ood_A_cue_min:.4f}, "
        f"B_img_max={ood_B_img_max:.4f}, B_cue_max={ood_B_cue_max:.4f}, "
        f"A_abl_img_max={ood_A_abl_img_max:.4f}, A_swap_follow_min={ood_A_swap_follow_min:.4f}, A_swap_orig_max={ood_A_swap_orig_max:.4f})"
    )

    if errors:
        print("\n[FAIL] V8 pair-grade OOD-required + causal checks did not pass:")
        for e in errors:
            print(" - " + str(e))
        raise SystemExit(1)

    print("\n[OK] V8 pair-grade OOD-required + causal checks passed.")


if __name__ == "__main__":
    main()

