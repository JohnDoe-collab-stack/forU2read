#!/usr/bin/env python3
from __future__ import annotations

"""
Strict reference-gate verifier for `aslmt_law_v5b_amodal_localclass`.

Adds:
- artifact hygiene checks (schema, duplicates, seed continuity, unique snapshot_tag, profile/steps coherence)
- v5-style reference-gate closure on C1/C2, but where B is a *class*:
  we use `ood.B_IoU` which is defined as `max_k ood.Bs_IoU[k]` (best local baseline).
"""

import argparse
import json
import math
import sys
from collections import Counter, defaultdict


def _read_jsonl(path: str) -> list[dict]:
    rows: list[dict] = []
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            obj = json.loads(line)
            if not isinstance(obj, dict):
                raise TypeError("jsonl line is not an object")
            rows.append(obj)
    return rows


def _fail(msg: str) -> None:
    print("[FAIL]", msg)
    sys.exit(1)


def _as_float(v: object, path: str) -> float:
    if not isinstance(v, (int, float)):
        _fail(f"non-numeric value at {path}: {type(v)}")
    vv = float(v)
    if not math.isfinite(vv):
        _fail(f"non-finite value at {path}: {vv}")
    return vv


def _get(d: dict, path: tuple[str, ...]) -> object:
    cur: object = d
    for k in path:
        if not isinstance(cur, dict) or k not in cur:
            _fail(f"missing key: {'.'.join(path)}")
        cur = cur[k]
    return cur


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--master-jsonl", required=True)
    args = ap.parse_args()

    rows = _read_jsonl(args.master_jsonl)
    if not rows:
        _fail("empty master jsonl")

    expected_kind = "aslmt_law_v5b_amodal_localclass"
    expected_cfgs = ["C0_hard", "C1_mid", "C2_soft"]
    closure_cfgs = ["C1_mid", "C2_soft"]

    # Same reference-gate thresholds as v5 (transport witness).
    req_A_ood_min = 0.50
    req_B_ood_max = 0.60
    req_ablation_drop = 0.40
    req_swap_perm_min = 0.50
    req_swap_orig_max = 0.35

    kinds = sorted({str(r.get("kind", "")) for r in rows})
    if kinds != [expected_kind]:
        _fail(f"unexpected kind set: {kinds} (expected: [{expected_kind}])")

    cfg_names = sorted({str(r.get("cfg_name", "")) for r in rows})
    if cfg_names != sorted(expected_cfgs):
        _fail(f"unexpected cfg_name set: {cfg_names} (expected: {sorted(expected_cfgs)})")

    snapshot_tags = sorted({str(r.get("snapshot_tag", "")) for r in rows})
    if len(snapshot_tags) != 1 or snapshot_tags[0] == "":
        _fail(f"expected a single non-empty snapshot_tag, got: {snapshot_tags}")

    profiles = sorted({str(r.get("profile", "")) for r in rows})
    if len(profiles) != 1 or profiles[0] == "":
        _fail(f"expected a single non-empty profile, got: {profiles}")
    profile = profiles[0]

    steps = sorted({int(r.get("steps")) for r in rows if "steps" in r})
    if len(steps) != 1:
        _fail(f"expected a single steps value, got: {steps}")
    steps0 = steps[0]

    expected_steps_by_profile = {"smoke": 2000, "solid": 30000}
    if profile in expected_steps_by_profile:
        exp = expected_steps_by_profile[profile]
        if steps0 != exp:
            _fail(f"profile={profile} expects steps={exp}, got steps={steps0}")

    # Required nested metrics exist and are numeric for every row.
    for i, r in enumerate(rows):
        _as_float(_get(r, ("iid", "A_IoU")), f"rows[{i}].iid.A_IoU")
        _as_float(_get(r, ("iid", "B_IoU")), f"rows[{i}].iid.B_IoU")
        bs_iid = _get(r, ("iid", "Bs_IoU"))
        if not isinstance(bs_iid, dict) or len(bs_iid) == 0:
            _fail(f"rows[{i}].iid.Bs_IoU must be a non-empty dict")
        for k, v in bs_iid.items():
            _as_float(v, f"rows[{i}].iid.Bs_IoU.{k}")

        _as_float(_get(r, ("ood", "A_IoU")), f"rows[{i}].ood.A_IoU")
        _as_float(_get(r, ("ood", "B_IoU")), f"rows[{i}].ood.B_IoU")
        bs_ood = _get(r, ("ood", "Bs_IoU"))
        if not isinstance(bs_ood, dict) or len(bs_ood) == 0:
            _fail(f"rows[{i}].ood.Bs_IoU must be a non-empty dict")
        for k, v in bs_ood.items():
            _as_float(v, f"rows[{i}].ood.Bs_IoU.{k}")

        _as_float(_get(r, ("ood", "audit", "ablation_drop")), f"rows[{i}].ood.audit.ablation_drop")
        _as_float(_get(r, ("ood", "audit", "swap_vs_perm")), f"rows[{i}].ood.audit.swap_vs_perm")
        _as_float(_get(r, ("ood", "audit", "swap_vs_orig")), f"rows[{i}].ood.audit.swap_vs_orig")

        # sanity: B_IoU equals max Bs_IoU (class best-case)
        bmax = max(float(x) for x in bs_ood.values())
        b = float(r["ood"]["B_IoU"])
        if abs(b - bmax) > 1e-6:
            _fail(f"rows[{i}].ood.B_IoU != max(ood.Bs_IoU): {b} vs {bmax}")

    # Seed hygiene
    pairs = [(str(r["cfg_name"]), int(r["seed"])) for r in rows]
    dup_pairs = [k for k, c in Counter(pairs).items() if c > 1]
    if dup_pairs:
        _fail(f"duplicate (cfg_name, seed) rows: {dup_pairs[:10]}")

    by_cfg: dict[str, list[dict]] = defaultdict(list)
    for r in rows:
        by_cfg[str(r["cfg_name"])].append(r)

    seed_sets = {cfg: sorted({int(x["seed"]) for x in rr}) for cfg, rr in by_cfg.items()}
    uniq_seed_sets = sorted({tuple(v) for v in seed_sets.values()})
    if len(uniq_seed_sets) != 1:
        _fail(f"seed sets differ across cfgs: {seed_sets}")
    seeds0 = list(uniq_seed_sets[0])

    if seeds0:
        expected = list(range(min(seeds0), max(seeds0) + 1))
        if seeds0 != expected:
            _fail(f"non-contiguous seeds: got {seeds0}, expected {expected}")

    expected_rows = len(expected_cfgs) * len(seeds0)
    if len(rows) != expected_rows:
        _fail(f"unexpected row count: got {len(rows)}, expected {expected_rows} (cfgs={len(expected_cfgs)} seeds={len(seeds0)})")

    # Config constancy per cfg_name (no per-seed drift)
    for cfg, rr in by_cfg.items():
        cfgs = [json.dumps(x["cfg"], sort_keys=True) for x in rr]
        if len(set(cfgs)) != 1:
            _fail(f"cfg dict differs across seeds for cfg_name={cfg}")

    # Apply closure gates on C1/C2 (min/max over seeds).
    for cfg in closure_cfgs:
        rr = by_cfg.get(cfg, [])
        if not rr:
            _fail(f"missing cfg {cfg}")

        A_ood = [_as_float(x["ood"]["A_IoU"], f"{cfg}.ood.A_IoU") for x in rr]
        B_ood = [_as_float(x["ood"]["B_IoU"], f"{cfg}.ood.B_IoU") for x in rr]
        abl = [_as_float(x["ood"]["audit"]["ablation_drop"], f"{cfg}.ood.audit.ablation_drop") for x in rr]
        swp = [_as_float(x["ood"]["audit"]["swap_vs_perm"], f"{cfg}.ood.audit.swap_vs_perm") for x in rr]
        swo = [_as_float(x["ood"]["audit"]["swap_vs_orig"], f"{cfg}.ood.audit.swap_vs_orig") for x in rr]

        min_A = min(A_ood)
        max_B = max(B_ood)
        min_abl = min(abl)
        min_swp = min(swp)
        max_swo = max(swo)

        # Also report per-baseline worst-case (across seeds).
        baseline_names = sorted(rr[0]["ood"]["Bs_IoU"].keys())
        per_base_max = {}
        for bn in baseline_names:
            per_base_max[bn] = max(float(x["ood"]["Bs_IoU"][bn]) for x in rr)

        print(
            f"[STRICT-REFGATE-V5B] cfg={cfg} min_A_ood={min_A:.4f} max_Bclass_ood={max_B:.4f} "
            f"min_ablation_drop={min_abl:.4f} min_swap_vs_perm={min_swp:.4f} max_swap_vs_orig={max_swo:.4f} n_rows={len(rr)}"
        )
        print("[STRICT-REFGATE-V5B] cfg=" + cfg + " per_baseline_max_ood=" + json.dumps(per_base_max, sort_keys=True))

        errors: list[str] = []
        if min_A < req_A_ood_min:
            errors.append(f"min_A_ood={min_A:.4f} < {req_A_ood_min:.4f}")
        if max_B > req_B_ood_max:
            errors.append(f"max_Bclass_ood={max_B:.4f} > {req_B_ood_max:.4f}")
        if min_abl < req_ablation_drop:
            errors.append(f"min_ablation_drop={min_abl:.4f} < {req_ablation_drop:.4f}")
        if min_swp < req_swap_perm_min:
            errors.append(f"min_swap_vs_perm={min_swp:.4f} < {req_swap_perm_min:.4f}")
        if max_swo > req_swap_orig_max:
            errors.append(f"max_swap_vs_orig={max_swo:.4f} > {req_swap_orig_max:.4f}")

        if errors:
            print(f"\n[FAIL] strict law_v5b_amodal_localclass refgate checks failed for cfg={cfg}:")
            for e in errors:
                print(" -", e)
            sys.exit(1)

    print("[OK] strict law_v5b_amodal_localclass checks passed (schema + C1/C2 refgate).")


if __name__ == "__main__":
    main()

