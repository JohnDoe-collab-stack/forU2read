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
    p = argparse.ArgumentParser(
        description="Strict verifier for ASLMT v18 algebra multistep STRONG (64) matrix runs (v3 hardened generator/verifier)."
    )
    p.add_argument("--master-jsonl", type=str, required=True)
    p.add_argument("--profile", type=str, default="solid", choices=["smoke", "solid"])
    p.add_argument("--min-seeds", type=int, default=5)
    p.add_argument("--n-states-list", type=str, required=True)
    p.add_argument(
        "--expected-bundle-hash-prefix",
        type=str,
        default="",
        help="Optional: enforce that the master filename contains this bundle-hash prefix (e.g. 12 hex chars).",
    )
    args = p.parse_args()
    solid = bool(str(args.profile) == "solid")

    master = Path(args.master_jsonl).expanduser().resolve()
    n_list = _parse_int_list(args.n_states_list)

    recs: dict[tuple[int, int], dict] = {}
    dup_keys: list[tuple[int, int]] = []
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
                dup_keys.append(key)
            recs[key] = r

    failures: list[str] = []
    if str(args.expected_bundle_hash_prefix):
        pref = str(args.expected_bundle_hash_prefix)
        if pref not in master.name:
            failures.append(f"master filename does not contain expected bundle-hash prefix: {pref}")
    if dup_keys:
        failures.append(f"duplicate (n_states,seed) rows in master: {sorted(set(dup_keys))}")

    expected_kind = "aslmt_v18_algebra_multistep_64_strong_actionz_v3"
    for n in n_list:
        seeds = sorted({seed for (nn, seed) in recs.keys() if nn == int(n)})
        if len(seeds) < int(args.min_seeds):
            failures.append(f"n={n}: only {len(seeds)} seeds present (need >= {int(args.min_seeds)})")
            continue

        # Protocol identity checks: all seeds must share the same config for this n.
        first = recs[(int(n), int(seeds[0]))]
        def _get_int_field(r: dict, name: str) -> int:
            v = r.get(name)
            if not isinstance(v, int):
                raise KeyError(name)
            return int(v)

        def _get_str_field(r: dict, name: str) -> str:
            v = r.get(name)
            if not isinstance(v, str):
                raise KeyError(name)
            return str(v)

        try:
            base_kind = _get_str_field(first, "kind")
            base_profile = _get_str_field(first, "profile")
            base_n_views = _get_int_field(first, "n_views")
            base_y = _get_int_field(first, "y_classes")
            base_q = _get_int_field(first, "q_steps")
            base_obs_vocab = _get_int_field(first, "obs_vocab")
            base_z_classes = _get_int_field(first, "z_classes")
        except KeyError as e:
            failures.append(f"n={n}: missing required field {e}")
            continue

        if base_kind != expected_kind:
            failures.append(f"n={n}: kind={base_kind} != expected {expected_kind}")
        if base_profile != str(args.profile):
            failures.append(f"n={n}: profile={base_profile} != expected {str(args.profile)}")
        if base_z_classes != base_n_views:
            failures.append(f"n={n}: z_classes={base_z_classes} must equal n_views={base_n_views}")

        # Enforce config identity across seeds once.
        for seed in seeds:
            r = recs[(int(n), int(seed))]
            try:
                if _get_str_field(r, "kind") != expected_kind:
                    failures.append(f"n={n} seed={seed}: kind mismatch")
                if _get_str_field(r, "profile") != str(args.profile):
                    failures.append(f"n={n} seed={seed}: profile mismatch")
                if _get_int_field(r, "n_views") != base_n_views:
                    failures.append(f"n={n} seed={seed}: n_views mismatch")
                if _get_int_field(r, "y_classes") != base_y:
                    failures.append(f"n={n} seed={seed}: y_classes mismatch")
                if _get_int_field(r, "q_steps") != base_q:
                    failures.append(f"n={n} seed={seed}: q_steps mismatch")
                if _get_int_field(r, "obs_vocab") != base_obs_vocab:
                    failures.append(f"n={n} seed={seed}: obs_vocab mismatch")
                if _get_int_field(r, "z_classes") != base_z_classes:
                    failures.append(f"n={n} seed={seed}: z_classes mismatch")
            except KeyError as e:
                failures.append(f"n={n} seed={seed}: missing field {e}")

        def _min(metric: str, split: str) -> float:
            vals = []
            for seed in seeds:
                r = recs[(int(n), int(seed))]
                d = r.get("metrics", {}).get(split, {})
                if metric in d:
                    vals.append(float(d[metric]))
            return min(vals) if vals else float("nan")

        def _max(metric: str, split: str) -> float:
            vals = []
            for seed in seeds:
                r = recs[(int(n), int(seed))]
                d = r.get("metrics", {}).get(split, {})
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
                if not (A_min >= 0.90):
                    failures.append(f"n={n} {sp}: A_acc(min)={A_min} < 0.90")
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
        print("\n[FAIL] v18 algebra multistep STRONG matrix checks did not pass:")
        for s in failures:
            print("-", s)
        raise SystemExit(1)

    print("\n[OK] v18 algebra multistep STRONG matrix checks passed.")


if __name__ == "__main__":
    main()
