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
    p = argparse.ArgumentParser(description="Strict verifier for ASLMT v19 algebra universal v4 matrix runs.")
    p.add_argument("--master-jsonl", type=str, required=True)
    p.add_argument("--profile", type=str, default="solid", choices=["smoke", "solid"])
    p.add_argument("--min-seeds", type=int, default=5)
    p.add_argument("--n-states-list", type=str, required=True)
    p.add_argument("--max-steps", type=int, required=True)
    args = p.parse_args()
    solid = bool(str(args.profile) == "solid")

    master = Path(args.master_jsonl).expanduser().resolve()
    n_list = _parse_int_list(args.n_states_list)
    expected_kind = "aslmt_v19_algebra_universal_actionz_v4"

    recs: dict[tuple[int, int], dict] = {}
    dup: list[tuple[int, int]] = []
    with open(master, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                r = json.loads(line)
            except Exception as e:
                failures.append(f"invalid json line in master: {e}")
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

        for seed in seeds:
            r = recs[(int(n), int(seed))]
            if r.get("kind") != expected_kind:
                failures.append(f"n={n} seed={seed}: kind mismatch")
            if r.get("profile") != str(args.profile):
                failures.append(f"n={n} seed={seed}: profile mismatch")
            if int(r.get("max_steps", -1)) != int(args.max_steps):
                failures.append(f"n={n} seed={seed}: max_steps mismatch")

        # Hyperparams must be identical across seeds for a given n.
        ref = recs[(int(n), int(seeds[0]))]
        for seed in seeds:
            r = recs[(int(n), int(seed))]
            for k in ("n_views", "y_classes", "obs_vocab"):
                if int(r.get(k, -1)) != int(ref.get(k, -1)):
                    failures.append(f"n={n} seed={seed}: {k} mismatch vs seed={seeds[0]}")

        required_metrics = [
            "A_acc",
            "B_vis_acc",
            "B_cue_acc",
            "A_abl_acc",
            "A_swap_acc",
            "swap_action_follow_rate",
        ]
        for seed in seeds:
            rr = recs[(int(n), int(seed))]
            if int(rr.get("n_views", -1)) < 0:
                failures.append(f"n={n} seed={seed}: missing n_views")
            if int(rr.get("y_classes", -1)) < 0:
                failures.append(f"n={n} seed={seed}: missing y_classes")
            if int(rr.get("obs_vocab", -1)) < 0:
                failures.append(f"n={n} seed={seed}: missing obs_vocab")
            for sp in ("iid", "ood"):
                d = rr.get("metrics", {}).get(sp, None)
                if not isinstance(d, dict):
                    failures.append(f"n={n} seed={seed} {sp}: missing split metrics")
                    continue
                for m in required_metrics:
                    if m not in d or not math.isfinite(float(d[m])):
                        failures.append(f"n={n} seed={seed} {sp}: missing metric {m}")

        def _min(metric: str, split: str) -> float:
            vals = []
            for seed in seeds:
                d = recs[(int(n), int(seed))]["metrics"][split]
                vals.append(float(d[metric]))
            return min(vals)

        def _max(metric: str, split: str) -> float:
            vals = []
            for seed in seeds:
                d = recs[(int(n), int(seed))]["metrics"][split]
                vals.append(float(d[metric]))
            return max(vals)

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
        print("\n[FAIL] v19 algebra universal v4 checks did not pass:")
        for s in failures:
            print("-", s)
        raise SystemExit(1)

    print("\n[OK] v19 algebra universal v4 checks passed.")


if __name__ == "__main__":
    main()
