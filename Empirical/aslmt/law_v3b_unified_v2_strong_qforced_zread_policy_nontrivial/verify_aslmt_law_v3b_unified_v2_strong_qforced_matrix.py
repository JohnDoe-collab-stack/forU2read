import argparse
import json
from pathlib import Path


def _parse_int_list(s: str) -> list[int]:
    out: list[int] = []
    for part in str(s).split(","):
        part = part.strip()
        if not part:
            continue
        out.append(int(part))
    if not out:
        raise ValueError("empty list")
    return out


def _zs_for_n_A1(n: int) -> list[int]:
    zs = [int(n), int(n - 1), int(n // 2)]
    zs = [z for z in zs if z >= 2]
    return sorted(set(zs))


def main() -> None:
    p = argparse.ArgumentParser(
        description="Strict verifier for ASLMT law_v3b_unified_v2_strong_qforced_zquery matrix runs."
    )
    p.add_argument("--master-jsonl", type=str, required=True)
    p.add_argument("--profile", type=str, default="solid", choices=["smoke", "solid"])
    p.add_argument("--min-seeds", type=int, default=3)
    p.add_argument("--n-classes-list", type=str, required=True)
    p.add_argument("--z-policy", type=str, default="A1", choices=["A1", "explicit"])
    p.add_argument("--z-classes-list", type=str, default="")
    args = p.parse_args()
    solid = str(args.profile) == "solid"

    master = Path(args.master_jsonl).expanduser().resolve()
    n_list = _parse_int_list(args.n_classes_list)
    if str(args.z_policy) == "explicit":
        if not str(args.z_classes_list).strip():
            raise SystemExit("--z-classes-list is required when --z-policy explicit")
        z_list = _parse_int_list(args.z_classes_list)
    else:
        z_list = []

    recs: dict[tuple[int, int, int], dict] = {}
    with open(master, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                r = json.loads(line)
            except Exception:
                continue
            n = r.get("n_classes")
            z = r.get("z_classes")
            seed = r.get("seed")
            if not all(isinstance(x, int) for x in (n, z, seed)):
                continue
            recs[(int(n), int(z), int(seed))] = r

    def split(r: dict, name: str) -> dict:
        pe = r.get("pair_eval", {})
        d = pe.get(name)
        if not isinstance(d, dict):
            return {}
        return d

    def metric_split(r: dict, name: str) -> dict:
        m = r.get("metrics", {})
        d = m.get(name)
        if not isinstance(d, dict):
            return {}
        return d

    failures: list[str] = []

    for n in n_list:
        if str(args.z_policy) == "explicit":
            zs = list(z_list)
        else:
            zs = _zs_for_n_A1(int(n))

        for z in zs:
            seeds = sorted({seed for (nn, zz, seed) in recs.keys() if nn == int(n) and zz == int(z)})
            if solid and len(seeds) < int(args.min_seeds):
                failures.append(f"n={n} z={z}: only {len(seeds)} seeds present (need >= {int(args.min_seeds)})")
                continue
            if (not solid) and (len(seeds) < 1):
                failures.append(f"n={n} z={z}: no seeds present")
                continue

            def _min_over_seeds(key: str, split_name: str) -> float:
                vals = []
                for seed in seeds:
                    r = recs[(int(n), int(z), int(seed))]
                    d = split(r, split_name)
                    if key in d:
                        vals.append(float(d[key]))
                return min(vals) if vals else float("nan")

            def _max_over_seeds(key: str, split_name: str) -> float:
                vals = []
                for seed in seeds:
                    r = recs[(int(n), int(z), int(seed))]
                    d = split(r, split_name)
                    if key in d:
                        vals.append(float(d[key]))
                return max(vals) if vals else float("nan")

            def _min_over_seeds_metric(key: str, split_name: str) -> float:
                vals = []
                for seed in seeds:
                    r = recs[(int(n), int(z), int(seed))]
                    d = metric_split(r, split_name)
                    if key in d:
                        vals.append(float(d[key]))
                return min(vals) if vals else float("nan")

            def _max_over_seeds_metric(key: str, split_name: str) -> float:
                vals = []
                for seed in seeds:
                    r = recs[(int(n), int(z), int(seed))]
                    d = metric_split(r, split_name)
                    if key in d:
                        vals.append(float(d[key]))
                return max(vals) if vals else float("nan")

            def _all_barriers_ok(split_name: str) -> bool:
                ok = True
                for seed in seeds:
                    r = recs[(int(n), int(z), int(seed))]
                    d = split(r, split_name)
                    ok = ok and bool(d.get("obs_image_barrier_ok", False)) and bool(d.get("obs_cue_barrier_ok", False))
                return bool(ok)

            if int(z) == int(n):
                for sp in ("iid", "ood"):
                    if not _all_barriers_ok(sp):
                        failures.append(f"ref n={n} z={z} {sp}: barrier checks failed")
                    A_img_min = _min_over_seeds("A_both_image_pair_rate", sp)
                    A_cue_min = _min_over_seeds("A_both_cue_pair_rate", sp)
                    swap_follow_min = _min_over_seeds("A_swap_follow_image_pair_rate", sp)
                    swap_orig_max = _max_over_seeds("A_swap_orig_both_image_pair_rate", sp)
                    abl_img_max = _max_over_seeds("A_ablated_both_image_pair_rate", sp)
                    Bimg_max = _max_over_seeds("B_image_only_both_rate", sp)
                    Bcue_max = _max_over_seeds("B_cue_only_both_rate", sp)

                    if solid:
                        if A_img_min != 1.0:
                            failures.append(f"ref n={n} z={z} {sp}: A_img_min={A_img_min} != 1.0")
                        if A_cue_min != 1.0:
                            failures.append(f"ref n={n} z={z} {sp}: A_cue_min={A_cue_min} != 1.0")
                        if swap_follow_min != 1.0:
                            failures.append(f"ref n={n} z={z} {sp}: swap_follow_min={swap_follow_min} != 1.0")
                        if swap_orig_max != 0.0:
                            failures.append(f"ref n={n} z={z} {sp}: swap_orig_max={swap_orig_max} != 0.0")
                        if abl_img_max != 0.0:
                            failures.append(f"ref n={n} z={z} {sp}: abl_img_max={abl_img_max} != 0.0")
                        if Bimg_max != 0.0:
                            failures.append(f"ref n={n} z={z} {sp}: Bimg_max={Bimg_max} != 0.0")
                        if Bcue_max != 0.0:
                            failures.append(f"ref n={n} z={z} {sp}: Bcue_max={Bcue_max} != 0.0")

                        q_acc_min = _min_over_seeds_metric("q_acc", sp)
                        res_acc_min = _min_over_seeds_metric("res_acc", sp)
                        action_rate_min = _min_over_seeds_metric("query_action_rate", sp)
                        action_rate_max = _max_over_seeds_metric("query_action_rate", sp)
                        if not (q_acc_min >= 0.90):
                            failures.append(f"ref n={n} z={z} {sp}: q_acc_min={q_acc_min} < 0.90")
                        if not (res_acc_min >= 0.90):
                            failures.append(f"ref n={n} z={z} {sp}: res_acc_min={res_acc_min} < 0.90")
                        if not (action_rate_min >= 0.05 and action_rate_max <= 0.95):
                            failures.append(
                                f"ref n={n} z={z} {sp}: query_action_rate not balanced (min={action_rate_min}, max={action_rate_max})"
                            )
            else:
                for sp in ("iid", "ood"):
                    if not _all_barriers_ok(sp):
                        failures.append(f"sub n={n} z={z} {sp}: barrier checks failed (task invalid)")
                    if solid:
                        A_img_min = _min_over_seeds("A_both_image_pair_rate", sp)
                        if not (A_img_min < 1.0):
                            failures.append(f"sub n={n} z={z} {sp}: A_img_min={A_img_min} not < 1.0")

    if failures:
        print("\n[FAIL] law_v3b_unified_v2_strong matrix checks did not pass:")
        for s in failures:
            print("-", s)
        raise SystemExit(1)

    print("\n[OK] law_v3b_unified_v2_strong matrix checks passed.")


if __name__ == "__main__":
    main()
