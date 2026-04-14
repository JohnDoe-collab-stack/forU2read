import argparse
import json
from collections import defaultdict


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
    p.add_argument("--n-classes", type=int, required=True)
    p.add_argument("--profile", type=str, default="solid", choices=["smoke", "solid"])
    p.add_argument("--min-seeds", type=int, default=3)
    args = p.parse_args()

    n_classes = int(args.n_classes)
    rows = _read_jsonl(args.master_jsonl)
    if not rows:
        raise SystemExit("empty master jsonl")

    by_z: dict[int, list[dict]] = defaultdict(list)
    for r in rows:
        by_z[int(r["z_classes"])].append(r)

    if n_classes not in by_z:
        raise SystemExit(f"missing z_classes==n_classes group: n_classes={n_classes}")

    errors: list[str] = []

    def _minmax_for_group(z: int):
        g = by_z[z]
        iid = [x["pair_eval"]["iid"] for x in g]
        ood = [x["pair_eval"]["ood"] for x in g]

        iid_img_bar = all(bool(x["obs_image_barrier_ok"]) for x in iid)
        iid_cue_bar = all(bool(x["obs_cue_barrier_ok"]) for x in iid)
        ood_img_bar = all(bool(x["obs_image_barrier_ok"]) for x in ood)
        ood_cue_bar = all(bool(x["obs_cue_barrier_ok"]) for x in ood)

        iid_A_img_min = min(float(x["A_both_image_pair_rate"]) for x in iid)
        iid_A_cue_min = min(float(x["A_both_cue_pair_rate"]) for x in iid)
        iid_B_img_max = max(float(x["B_image_only_both_rate"]) for x in iid)
        iid_B_cue_max = max(float(x["B_cue_only_both_rate"]) for x in iid)

        ood_A_img_min = min(float(x["A_both_image_pair_rate"]) for x in ood)
        ood_A_cue_min = min(float(x["A_both_cue_pair_rate"]) for x in ood)
        ood_B_img_max = max(float(x["B_image_only_both_rate"]) for x in ood)
        ood_B_cue_max = max(float(x["B_cue_only_both_rate"]) for x in ood)

        iid_A_abl_img_max = max(float(x["A_ablated_both_image_pair_rate"]) for x in iid)
        iid_A_swap_follow_min = min(float(x["A_swap_follow_image_pair_rate"]) for x in iid)
        iid_A_swap_orig_max = max(float(x["A_swap_orig_both_image_pair_rate"]) for x in iid)

        ood_A_abl_img_max = max(float(x["A_ablated_both_image_pair_rate"]) for x in ood)
        ood_A_swap_follow_min = min(float(x["A_swap_follow_image_pair_rate"]) for x in ood)
        ood_A_swap_orig_max = max(float(x["A_swap_orig_both_image_pair_rate"]) for x in ood)

        seeds = sorted(set(int(x["seed"]) for x in g))

        return dict(
            z=z,
            n_rows=len(g),
            seeds=seeds,
            iid_img_bar=iid_img_bar,
            iid_cue_bar=iid_cue_bar,
            ood_img_bar=ood_img_bar,
            ood_cue_bar=ood_cue_bar,
            iid_A_img_min=iid_A_img_min,
            iid_A_cue_min=iid_A_cue_min,
            iid_B_img_max=iid_B_img_max,
            iid_B_cue_max=iid_B_cue_max,
            ood_A_img_min=ood_A_img_min,
            ood_A_cue_min=ood_A_cue_min,
            ood_B_img_max=ood_B_img_max,
            ood_B_cue_max=ood_B_cue_max,
            iid_A_abl_img_max=iid_A_abl_img_max,
            iid_A_swap_follow_min=iid_A_swap_follow_min,
            iid_A_swap_orig_max=iid_A_swap_orig_max,
            ood_A_abl_img_max=ood_A_abl_img_max,
            ood_A_swap_follow_min=ood_A_swap_follow_min,
            ood_A_swap_orig_max=ood_A_swap_orig_max,
        )

    ref = _minmax_for_group(n_classes)
    print(
        f"[vN3b-REF] z={ref['z']} seeds={ref['seeds']} n_rows={ref['n_rows']} "
        f"iid(A_img_min={ref['iid_A_img_min']:.4f}, A_cue_min={ref['iid_A_cue_min']:.4f}, "
        f"abl_img_max={ref['iid_A_abl_img_max']:.4f}, swap_follow_min={ref['iid_A_swap_follow_min']:.4f}, "
        f"swap_orig_max={ref['iid_A_swap_orig_max']:.4f}) "
        f"ood(A_img_min={ref['ood_A_img_min']:.4f}, A_cue_min={ref['ood_A_cue_min']:.4f}, "
        f"abl_img_max={ref['ood_A_abl_img_max']:.4f}, swap_follow_min={ref['ood_A_swap_follow_min']:.4f}, "
        f"swap_orig_max={ref['ood_A_swap_orig_max']:.4f})"
    )

    if str(args.profile) == "solid":
        if len(ref["seeds"]) < int(args.min_seeds):
            errors.append(f"reference group z={n_classes} has only {len(ref['seeds'])} distinct seeds < {int(args.min_seeds)}")

    if not (ref["iid_img_bar"] and ref["iid_cue_bar"] and ref["ood_img_bar"] and ref["ood_cue_bar"]):
        errors.append("barrier checks failed in reference group")
    if str(args.profile) == "solid":
        if ref["iid_A_img_min"] < 1.0:
            errors.append(f"ref iid A_img_min={ref['iid_A_img_min']:.4f} < 1.0000")
        if ref["iid_A_cue_min"] < 1.0:
            errors.append(f"ref iid A_cue_min={ref['iid_A_cue_min']:.4f} < 1.0000")
        if ref["ood_A_img_min"] < 1.0:
            errors.append(f"ref ood A_img_min={ref['ood_A_img_min']:.4f} < 1.0000")
        if ref["ood_A_cue_min"] < 1.0:
            errors.append(f"ref ood A_cue_min={ref['ood_A_cue_min']:.4f} < 1.0000")
        if ref["iid_B_img_max"] > 0.0 or ref["iid_B_cue_max"] > 0.0 or ref["ood_B_img_max"] > 0.0 or ref["ood_B_cue_max"] > 0.0:
            errors.append("baseline both-rate is non-zero in reference group")

        if ref["iid_A_abl_img_max"] > 0.0:
            errors.append(f"ref iid ablation should break image barrier: abl_img_max={ref['iid_A_abl_img_max']:.4f} > 0.0000")
        if ref["ood_A_abl_img_max"] > 0.0:
            errors.append(f"ref ood ablation should break image barrier: abl_img_max={ref['ood_A_abl_img_max']:.4f} > 0.0000")
        if ref["iid_A_swap_follow_min"] < 1.0:
            errors.append(f"ref iid swap_follow_min={ref['iid_A_swap_follow_min']:.4f} < 1.0000")
        if ref["ood_A_swap_follow_min"] < 1.0:
            errors.append(f"ref ood swap_follow_min={ref['ood_A_swap_follow_min']:.4f} < 1.0000")
        if ref["iid_A_swap_orig_max"] >= 1.0:
            errors.append("ref iid swap still perfect w.r.t. original labels (unexpected)")
        if ref["ood_A_swap_orig_max"] >= 1.0:
            errors.append("ref ood swap still perfect w.r.t. original labels (unexpected)")

    if str(args.profile) == "solid":
        for z in sorted(by_z.keys()):
            if z >= n_classes:
                continue
            g = _minmax_for_group(z)
            print(f"[vN3b-<n] z={z} seeds={g['seeds']} iid_A_img_min={g['iid_A_img_min']:.4f} ood_A_img_min={g['ood_A_img_min']:.4f}")
            if g["iid_A_img_min"] >= 1.0 or g["ood_A_img_min"] >= 1.0:
                errors.append(f"z={z} unexpectedly achieved perfect image-barrier pair rate (iid_min={g['iid_A_img_min']:.4f}, ood_min={g['ood_A_img_min']:.4f})")

    if errors:
        print("\n[FAIL] vN3b minlift checks did not pass:")
        for e in errors:
            print(" - " + str(e))
        raise SystemExit(1)

    print("\n[OK] vN3b minlift checks passed.")


if __name__ == "__main__":
    main()

