#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path


def _read_jsonl(path: Path) -> list[dict]:
    rows: list[dict] = []
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

    master = Path(args.master_jsonl)
    rows = _read_jsonl(master)
    if not rows:
        raise SystemExit("Empty master.jsonl")

    by_cfg: dict[str, list[dict]] = defaultdict(list)
    for r in rows:
        by_cfg[str(r["cfg_name"])].append(r)

    # Strict schema expectations (guardrails against partial/garbled runs).
    expected_kind = "aslmt_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split"
    expected_cfgs = {"C0_16b_4i_2hi", "C1_64b_6i_3hi", "C2_128b_7i_4hi"}

    # Enforce uniqueness of (cfg_name, seed) at the master level.
    pairs = [(str(r.get("cfg_name")), int(r.get("seed"))) for r in rows]
    if len(set(pairs)) != len(pairs):
        # Find duplicates for a readable error.
        seen = set()
        dups = []
        for p2 in pairs:
            if p2 in seen:
                dups.append(p2)
            else:
                seen.add(p2)
        raise SystemExit(f"Duplicate (cfg,seed) rows found: {sorted(set(dups))}")

    kinds = {str(r.get("kind")) for r in rows}
    if kinds != {expected_kind}:
        raise SystemExit(f"Unexpected kind(s): {sorted(kinds)} (expected: {expected_kind})")

    profiles = {str(r.get("profile")) for r in rows}
    if len(profiles) != 1:
        raise SystemExit(f"Mixed profiles in master.jsonl: {sorted(profiles)}")
    (profile,) = tuple(profiles)
    if profile not in {"smoke", "solid"}:
        raise SystemExit(f"Unexpected profile={profile!r}")

    snapshot_tags = {str(r.get("snapshot_tag")) for r in rows}
    if len(snapshot_tags) != 1:
        raise SystemExit(f"Mixed snapshot_tag values: {sorted(snapshot_tags)}")

    seen_cfgs = set(by_cfg.keys())
    missing = expected_cfgs - seen_cfgs
    extra = seen_cfgs - expected_cfgs
    if missing:
        raise SystemExit(f"Missing cfg(s): {sorted(missing)}")
    if extra:
        raise SystemExit(f"Unexpected cfg(s): {sorted(extra)}")

    # Seed-set consistency across configs.
    seeds_all = sorted({int(r["seed"]) for r in rows})
    if not seeds_all:
        raise SystemExit("No seeds found")
    if seeds_all != list(range(min(seeds_all), max(seeds_all) + 1)):
        raise SystemExit(f"Non-contiguous seed set: {seeds_all}")
    if profile == "smoke" and len(seeds_all) != 1:
        raise SystemExit(f"Smoke profile expects exactly 1 seed, got: {seeds_all}")
    if profile == "solid" and len(seeds_all) < 3:
        raise SystemExit(f"Solid profile expects multi-seed (>=3) run, got: {seeds_all}")

    expected_rows = len(expected_cfgs) * len(seeds_all)
    if len(rows) != expected_rows:
        raise SystemExit(f"Unexpected row count: got {len(rows)}, expected {expected_rows} (= {len(expected_cfgs)} cfgs × {len(seeds_all)} seeds)")

    # Same spirit as v2/law_v1/law_v2.
    req_A_ood = 0.90
    req_B_ood = 0.35
    req_ablation_drop = 0.25
    req_swap_vs_orig = 0.70
    req_swap_vs_perm = 0.80

    ok = True
    failures: list[str] = []

    for cfg_name, rs in sorted(by_cfg.items(), key=lambda x: x[0]):
        seeds_cfg = sorted({int(r["seed"]) for r in rs})
        if seeds_cfg != seeds_all:
            raise SystemExit(f"Seed set mismatch for cfg={cfg_name}: got {seeds_cfg}, expected {seeds_all}")
        if len(rs) != len(seeds_all):
            raise SystemExit(f"Unexpected number of rows for cfg={cfg_name}: got {len(rs)}, expected {len(seeds_all)} (one per seed)")

        min_A_ood = 1.0
        max_B_ood = 0.0
        min_ablation_drop = 1.0
        max_swap_vs_orig = 0.0
        min_swap_vs_perm = 1.0

        for r in rs:
            # Minimal structural checks.
            if str(r.get("cfg_name")) != cfg_name:
                raise SystemExit("Internal error: cfg_name mismatch while grouping")
            if str(r.get("kind")) != expected_kind:
                raise SystemExit("Internal error: kind mismatch")
            if str(r.get("profile")) != profile:
                raise SystemExit("Internal error: profile mismatch")

            ood = r["ood"]
            min_A_ood = min(min_A_ood, float(ood["A_success"]))
            max_B_ood = max(max_B_ood, float(ood["B_success"]))
            aud = ood["audit"]
            min_ablation_drop = min(min_ablation_drop, float(aud["ablation_drop"]))
            max_swap_vs_orig = max(max_swap_vs_orig, float(aud["swap_vs_orig"]))
            min_swap_vs_perm = min(min_swap_vs_perm, float(aud["swap_vs_perm"]))

        summary = {
            "cfg": cfg_name,
            "min_A_ood": min_A_ood,
            "max_B_ood": max_B_ood,
            "min_ablation_drop": min_ablation_drop,
            "max_swap_vs_orig": max_swap_vs_orig,
            "min_swap_vs_perm": min_swap_vs_perm,
            "n_rows": len(rs),
        }
        print(
            "[OOD] "
            + " ".join(
                [
                    f"{k}={v}"
                    if k == "cfg"
                    else f"{k}={v:.4f}"
                    if isinstance(v, float)
                    else f"{k}={v}"
                    for k, v in summary.items()
                ]
            )
        )

        if min_A_ood < req_A_ood:
            ok = False
            failures.append(f"{cfg_name}: min_A_ood={min_A_ood:.4f} < {req_A_ood:.4f}")
        if max_B_ood > req_B_ood:
            ok = False
            failures.append(f"{cfg_name}: max_B_ood={max_B_ood:.4f} > {req_B_ood:.4f}")
        if min_ablation_drop < req_ablation_drop:
            ok = False
            failures.append(f"{cfg_name}: min_ablation_drop={min_ablation_drop:.4f} < {req_ablation_drop:.4f}")
        if max_swap_vs_orig > req_swap_vs_orig:
            ok = False
            failures.append(f"{cfg_name}: max_swap_vs_orig={max_swap_vs_orig:.4f} > {req_swap_vs_orig:.4f}")
        if min_swap_vs_perm < req_swap_vs_perm:
            ok = False
            failures.append(f"{cfg_name}: min_swap_vs_perm={min_swap_vs_perm:.4f} < {req_swap_vs_perm:.4f}")

    if ok:
        print("[OK] ASLMT law-v3 hard-OOD masks query-POMDP family checks passed.")
    else:
        print("[FAIL] ASLMT law-v3 hard-OOD masks query-POMDP family checks did not pass:")
        for f in failures:
            print(" - " + f)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
