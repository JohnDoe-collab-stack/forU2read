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


def _minmax_for_group(rows: list[dict]) -> dict:
    iid = [x["pair_eval"]["iid"] for x in rows]
    ood = [x["pair_eval"]["ood"] for x in rows]

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

    seeds = sorted(set(int(x["seed"]) for x in rows))

    return dict(
        n_rows=len(rows),
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


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--master-jsonl", type=str, required=True)
    p.add_argument("--profile", type=str, default="solid", choices=["smoke", "solid"])
    p.add_argument("--min-seeds", type=int, default=3)
    p.add_argument("--n-classes-list", type=str, required=True)
    p.add_argument("--z-policy", type=str, default="A1", choices=["A1", "explicit"])
    p.add_argument("--z-explicit", type=str, default="")
    args = p.parse_args()

    def parse_int_list(s: str) -> list[int]:
        out: list[int] = []
        for part in str(s).split(","):
            part = part.strip()
            if not part:
                continue
            out.append(int(part))
        if not out:
            raise SystemExit("empty list")
        return out

    n_list = parse_int_list(args.n_classes_list)
    rows = _read_jsonl(args.master_jsonl)
    if not rows:
        raise SystemExit("empty master jsonl")

    by_nz: dict[tuple[int, int], list[dict]] = defaultdict(list)
    for r in rows:
        by_nz[(int(r["n_classes"]), int(r["z_classes"]))].append(r)

    errors: list[str] = []

    def expected_zs_for_n(n: int) -> list[int]:
        if str(args.z_policy) == "explicit":
            zs = parse_int_list(args.z_explicit)
            return sorted(set(int(z) for z in zs))
        # A1 policy: z ∈ {n, n-1, floor(n/2)}
        zs = [int(n), int(n - 1), int(n // 2)]
        zs = [z for z in zs if z >= 2]
        return sorted(set(zs))

    for n in n_list:
        zs = expected_zs_for_n(int(n))
        if int(n) not in zs:
            errors.append(f"n={int(n)}: z-policy does not include z=n (zs={zs})")
            continue

        ref_rows = by_nz.get((int(n), int(n)), [])
        if not ref_rows:
            errors.append(f"missing reference group: n={int(n)} z={int(n)}")
            continue
        ref = _minmax_for_group(ref_rows)

        print(
            f"[v10-REF] n={int(n)} z={int(n)} seeds={ref['seeds']} n_rows={ref['n_rows']} "
            f"iid(bar_img={ref['iid_img_bar']}, bar_cue={ref['iid_cue_bar']}, A_img_min={ref['iid_A_img_min']:.4f}, A_cue_min={ref['iid_A_cue_min']:.4f}) "
            f"ood(bar_img={ref['ood_img_bar']}, bar_cue={ref['ood_cue_bar']}, A_img_min={ref['ood_A_img_min']:.4f}, A_cue_min={ref['ood_A_cue_min']:.4f})"
        )

        if str(args.profile) == "solid":
            if len(ref["seeds"]) < int(args.min_seeds):
                errors.append(f"n={int(n)} reference group has only {len(ref['seeds'])} distinct seeds < {int(args.min_seeds)}")

            if not (ref["iid_img_bar"] and ref["iid_cue_bar"] and ref["ood_img_bar"] and ref["ood_cue_bar"]):
                errors.append(f"n={int(n)}: barrier checks failed in reference group (must be true IID and OOD)")

            if ref["iid_A_img_min"] < 1.0:
                errors.append(f"n={int(n)} ref iid A_img_min={ref['iid_A_img_min']:.4f} < 1.0000")
            if ref["iid_A_cue_min"] < 1.0:
                errors.append(f"n={int(n)} ref iid A_cue_min={ref['iid_A_cue_min']:.4f} < 1.0000")
            if ref["ood_A_img_min"] < 1.0:
                errors.append(f"n={int(n)} ref ood A_img_min={ref['ood_A_img_min']:.4f} < 1.0000")
            if ref["ood_A_cue_min"] < 1.0:
                errors.append(f"n={int(n)} ref ood A_cue_min={ref['ood_A_cue_min']:.4f} < 1.0000")

            if ref["iid_B_img_max"] > 0.0 or ref["iid_B_cue_max"] > 0.0 or ref["ood_B_img_max"] > 0.0 or ref["ood_B_cue_max"] > 0.0:
                errors.append(f"n={int(n)} baseline both-rate is non-zero in reference group")

            if ref["iid_A_abl_img_max"] > 0.0:
                errors.append(f"n={int(n)} ref iid ablation should break image barrier: abl_img_max={ref['iid_A_abl_img_max']:.4f} > 0.0000")
            if ref["ood_A_abl_img_max"] > 0.0:
                errors.append(f"n={int(n)} ref ood ablation should break image barrier: abl_img_max={ref['ood_A_abl_img_max']:.4f} > 0.0000")
            if ref["iid_A_swap_follow_min"] < 1.0:
                errors.append(f"n={int(n)} ref iid swap_follow_min={ref['iid_A_swap_follow_min']:.4f} < 1.0000")
            if ref["ood_A_swap_follow_min"] < 1.0:
                errors.append(f"n={int(n)} ref ood swap_follow_min={ref['ood_A_swap_follow_min']:.4f} < 1.0000")
            if ref["iid_A_swap_orig_max"] >= 1.0:
                errors.append(f"n={int(n)} ref iid swap still perfect w.r.t. original labels (unexpected)")
            if ref["ood_A_swap_orig_max"] >= 1.0:
                errors.append(f"n={int(n)} ref ood swap still perfect w.r.t. original labels (unexpected)")

        if str(args.profile) == "solid":
            for z in zs:
                if int(z) >= int(n):
                    continue
                g_rows = by_nz.get((int(n), int(z)), [])
                if not g_rows:
                    errors.append(f"missing group: n={int(n)} z={int(z)}")
                    continue
                g = _minmax_for_group(g_rows)
                print(f"[v10-<n] n={int(n)} z={int(z)} seeds={g['seeds']} iid_A_img_min={g['iid_A_img_min']:.4f} ood_A_img_min={g['ood_A_img_min']:.4f}")
                if g["iid_A_img_min"] >= 1.0 or g["ood_A_img_min"] >= 1.0:
                    errors.append(f"n={int(n)} z={int(z)} unexpectedly achieved perfect image-barrier pair rate (iid_min={g['iid_A_img_min']:.4f}, ood_min={g['ood_A_img_min']:.4f})")

    if errors:
        print("\n[FAIL] v10 Phase A1 matrix checks did not pass:")
        for e in errors:
            print(" - " + str(e))
        raise SystemExit(1)

    print("\n[OK] v10 Phase A1 matrix checks passed.")


if __name__ == "__main__":
    main()

