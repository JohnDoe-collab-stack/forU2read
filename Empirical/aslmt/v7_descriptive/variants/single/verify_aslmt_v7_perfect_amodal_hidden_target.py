import argparse
import json
import sys


def verify(master_jsonl: str) -> None:
    with open(master_jsonl, "r", encoding="utf-8") as f:
        rows = [json.loads(line) for line in f if line.strip()]
    if not rows:
        print("No lines found in master jsonl.")
        sys.exit(1)

    min_A_ood = 1.0
    max_B_ood = 0.0
    min_gap_ood = 1.0
    min_ablation_drop = 1.0
    max_swap_vs_orig = 0.0
    min_swap_vs_perm = 1.0
    min_jepa_margin = 1.0

    for r in rows:
        ood = r["ood"]
        A_ood = float(ood["A_IoU"])
        B_ood = float(ood["B_IoU"])
        aud = ood["audit"]
        min_A_ood = min(min_A_ood, A_ood)
        max_B_ood = max(max_B_ood, B_ood)
        min_gap_ood = min(min_gap_ood, A_ood - B_ood)
        min_ablation_drop = min(min_ablation_drop, float(aud["ablation_drop"]))
        max_swap_vs_orig = max(max_swap_vs_orig, float(aud["swap_vs_orig"]))
        min_swap_vs_perm = min(min_swap_vs_perm, float(aud["swap_vs_perm"]))
        min_jepa_margin = min(min_jepa_margin, float(aud["jepa_match_orig"]) - float(aud["jepa_match_perm"]))

    # Conservative thresholds for the hidden-only target.
    req_A_ood = 0.75
    req_B_ood = 0.35
    req_gap_ood = 0.30
    req_ablation_drop = 0.40
    req_swap_vs_orig = 0.35
    req_swap_vs_perm = 0.70
    req_jepa_margin = 0.10

    errors = []
    if min_A_ood < req_A_ood:
        errors.append(f"min_A_ood={min_A_ood:.4f} < {req_A_ood:.4f}")
    if max_B_ood > req_B_ood:
        errors.append(f"max_B_ood={max_B_ood:.4f} > {req_B_ood:.4f}")
    if min_gap_ood < req_gap_ood:
        errors.append(f"min_gap_ood={min_gap_ood:.4f} < {req_gap_ood:.4f}")
    if min_ablation_drop < req_ablation_drop:
        errors.append(f"min_ablation_drop={min_ablation_drop:.4f} < {req_ablation_drop:.4f}")
    if max_swap_vs_orig > req_swap_vs_orig:
        errors.append(f"max_swap_vs_orig={max_swap_vs_orig:.4f} > {req_swap_vs_orig:.4f}")
    if min_swap_vs_perm < req_swap_vs_perm:
        errors.append(f"min_swap_vs_perm={min_swap_vs_perm:.4f} < {req_swap_vs_perm:.4f}")
    if min_jepa_margin < req_jepa_margin:
        errors.append(f"min_jepa_margin={min_jepa_margin:.4f} < {req_jepa_margin:.4f}")

    print(f"[V7 Perfect Amodal Hidden-Target] min_A_ood={min_A_ood:.4f} max_B_ood={max_B_ood:.4f} min_gap_ood={min_gap_ood:.4f}")
    print(f"[V7 Perfect Amodal Hidden-Target] min_ablation_drop={min_ablation_drop:.4f} max_swap_vs_orig={max_swap_vs_orig:.4f} min_swap_vs_perm={min_swap_vs_perm:.4f}")
    print(f"[V7 Perfect Amodal Hidden-Target] min_jepa_margin={min_jepa_margin:.4f}")

    if errors:
        print("\n[FAIL] V7 checks did not pass:")
        for e in errors:
            print(f" - {e}")
        sys.exit(1)

    print("\n[OK] V7 Perfect Amodal hidden-target checks passed.")
    sys.exit(0)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--master-jsonl", type=str, required=True)
    args = parser.parse_args()
    verify(args.master_jsonl)

