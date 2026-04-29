import argparse
import json
import math
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


def main() -> None:
    p = argparse.ArgumentParser(description="Strict verifier for ASLMT v19 algebra universal v1 matrix runs.")
    p.add_argument("--master-jsonl", type=str, required=True)
    p.add_argument("--profile", type=str, default="solid", choices=["smoke", "solid"])
    p.add_argument("--min-seeds", type=int, default=5)
    p.add_argument("--n-states-list", type=str, required=True)
    p.add_argument("--max-steps", type=int, required=True)
    args = p.parse_args()
    solid = bool(str(args.profile) == "solid")

    master = Path(args.master_jsonl).expanduser().resolve()
    n_list = _parse_int_list(args.n_states_list)
    expected_kind = "aslmt_v19_algebra_universal_actionz_v1"

    recs: dict[tuple[int, int], dict] = {}
    dup: list[tuple[int, int]] = []
    with open(master, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                r = json.loads(line)
            except Exception:
                continue
            n = r.get("n_states")
            seed = r.get("seed")
            if not all(isinstance(x, int) for x in (n, seed)):
                continue
            key = (int(n), int(seed))
            if key in recs:
                dup.append(key)
            recs[key] = r

    failures: list[str] = []
    if dup:
        failures.append(f"duplicate (n_states,seed) rows: {sorted(set(dup))}")

    for n in n_list:
        seeds = sorted({seed for (nn, seed) in recs.keys() if nn == int(n)})
        if len(seeds) < int(args.min_seeds):
            failures.append(f"n={n}: only {len(seeds)} seeds present (need >= {int(args.min_seeds)})")
            continue

        # identity checks
        for seed in seeds:
            r = recs[(int(n), int(seed))]
            if r.get("kind") != expected_kind:
                failures.append(f"n={n} seed={seed}: kind mismatch")
            if r.get("profile") != str(args.profile):
                failures.append(f"n={n} seed={seed}: profile mismatch")
            if int(r.get("max_steps", -1)) != int(args.max_steps):
                failures.append(f"n={n} seed={seed}: max_steps mismatch")

        def _min(metric: str, split: str) -> float:
            vals = []
            for seed in seeds:
                d = recs[(int(n), int(seed))].get("metrics", {}).get(split, {})
                if metric in d:
                    vals.append(float(d[metric]))
            return min(vals) if vals else float("nan")

        def _max(metric: str, split: str) -> float:
            vals = []
            for seed in seeds:
                d = recs[(int(n), int(seed))].get("metrics", {}).get(split, {})
                if metric in d:
                    vals.append(float(d[metric]))
            return max(vals) if vals else float("nan")

        for sp in ("iid", "ood"):
            A_min = _min("A_acc", sp)
            Bvis_max = _max("B_vis_acc", sp)
            Bcue_max = _max("B_cue_acc", sp)
            Abl_max = _max("A_abl_acc", sp)
            Swap_max = _max("A_swap_acc", sp)
            follow_min = _min("swap_action_follow_rate", sp)

            if solid:
                if not (A_min >= 0.85):
                    failures.append(f"n={n} {sp}: A_acc(min)={A_min} < 0.85")
                if not (Bvis_max <= 0.60):
                    failures.append(f"n={n} {sp}: B_vis_acc(max)={Bvis_max} > 0.60")
                if not (Bcue_max <= 0.60):
                    failures.append(f"n={n} {sp}: B_cue_acc(max)={Bcue_max} > 0.60")
                if not (Abl_max <= 0.70):
                    failures.append(f"n={n} {sp}: A_abl_acc(max)={Abl_max} > 0.70")
                if not (Swap_max <= 0.70):
                    failures.append(f"n={n} {sp}: A_swap_acc(max)={Swap_max} > 0.70")
                if not (follow_min >= 0.60):
                    failures.append(f"n={n} {sp}: swap_action_follow_rate(min)={follow_min} < 0.60")
            else:
                for name, v in [
                    ("A_acc", A_min),
                    ("B_vis_acc", Bvis_max),
                    ("B_cue_acc", Bcue_max),
                    ("A_abl_acc", Abl_max),
                    ("A_swap_acc", Swap_max),
                    ("swap_action_follow_rate", follow_min),
                ]:
                    if not math.isfinite(float(v)):
                        failures.append(f"n={n} {sp}: missing metric {name}")

    if failures:
        print("\n[FAIL] v19 algebra universal v1 checks did not pass:")
        for s in failures:
            print("-", s)
        raise SystemExit(1)

    print("\n[OK] v19 algebra universal v1 checks passed.")


if __name__ == "__main__":
    main()

