#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
import subprocess
import shutil
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


THIS_FILE = Path(__file__).resolve()
ALGEBRA_KERNEL = Path(os.environ.get("COMPATDIM_ALGEBRA_KERNEL", THIS_FILE.parent / "algebra_kernel"))
if str(ALGEBRA_KERNEL) not in sys.path:
    sys.path.insert(0, str(ALGEBRA_KERNEL))

from algebra_core import (  # noqa: E402
    Partition,
    confusions_of_partition,
    delta_gain,
    greedy_select,
    loss_set,
    required_distinctions,
    residual_loss,
    rho,
)


Pair = tuple[int, int]
Subset = tuple[int, ...]


@dataclass(frozen=True)
class ViewSpec:
    name: str
    labels: tuple[int, ...]


@dataclass(frozen=True)
class Scenario:
    name: str
    n_states: int
    sigma_labels: tuple[int, ...]
    views: tuple[ViewSpec, ...]
    description: str


def _normalize_labels(raw: list[Any]) -> tuple[int, ...]:
    remap: dict[Any, int] = {}
    out: list[int] = []
    nxt = 0
    for x in raw:
        if x not in remap:
            remap[x] = nxt
            nxt += 1
        out.append(remap[x])
    return tuple(out)


def _bits(x: int, n_bits: int) -> tuple[int, ...]:
    return tuple((int(x) >> b) & 1 for b in range(int(n_bits)))


def build_bits_scenario(*, n_bits: int, target: str, duplicate_first: bool, useless_view: bool) -> Scenario:
    if int(n_bits) <= 0:
        raise ValueError("n_bits must be positive")
    n_states = 1 << int(n_bits)
    states = list(range(n_states))

    if target == "full":
        sigma = tuple(states)
        desc_target = "full bit-vector target"
    elif target == "parity":
        sigma = tuple(sum(_bits(s, int(n_bits))) % 2 for s in states)
        desc_target = "parity target"
    elif target == "first-two":
        if int(n_bits) < 2:
            raise ValueError("target=first-two requires n_bits >= 2")
        sigma = _normalize_labels([_bits(s, int(n_bits))[:2] for s in states])
        desc_target = "first two bits target"
    else:
        raise ValueError(f"unknown target: {target}")

    views: list[ViewSpec] = []
    for b in range(int(n_bits)):
        labels = tuple(_bits(s, int(n_bits))[b] for s in states)
        views.append(ViewSpec(name=f"bit{b}", labels=labels))
    if duplicate_first:
        views.append(ViewSpec(name="bit0_duplicate", labels=views[0].labels))
    if useless_view:
        views.append(ViewSpec(name="constant_useless", labels=tuple(0 for _ in states)))

    return Scenario(
        name=f"bits_{target}",
        n_states=n_states,
        sigma_labels=tuple(int(x) for x in sigma),
        views=tuple(views),
        description=(
            f"Boolean cube with {n_bits} bits, {desc_target}; each base interface reveals one bit."
        ),
    )


def build_window_scenario(*, n_bits: int, window: int) -> Scenario:
    if int(n_bits) <= 1:
        raise ValueError("n_bits must be > 1")
    if int(window) <= 0 or int(window) >= int(n_bits):
        raise ValueError("window must satisfy 0 < window < n_bits")
    n_states = 1 << int(n_bits)
    states = list(range(n_states))
    sigma = tuple(states)
    views: list[ViewSpec] = []
    for start in range(int(n_bits)):
        positions = tuple((start + k) % int(n_bits) for k in range(int(window)))
        labels = _normalize_labels([tuple(_bits(s, int(n_bits))[p] for p in positions) for s in states])
        views.append(ViewSpec(name="window_" + "_".join(str(p) for p in positions), labels=labels))
    return Scenario(
        name=f"cyclic_windows_w{window}",
        n_states=n_states,
        sigma_labels=sigma,
        views=tuple(views),
        description=(
            f"Boolean cube with {n_bits} bits and cyclic {window}-bit interfaces against full target."
        ),
    )


def all_subsets(n: int) -> list[Subset]:
    out: list[Subset] = []
    for k in range(int(n) + 1):
        for xs in itertools.combinations(range(int(n)), k):
            out.append(tuple(int(x) for x in xs))
    return out


def proper_subsets(xs: Subset) -> list[Subset]:
    vals = tuple(int(x) for x in xs)
    out: list[Subset] = []
    for k in range(len(vals)):
        for ys in itertools.combinations(vals, k):
            out.append(tuple(int(y) for y in ys))
    return out


def subset_names(subset: Subset, view_names: list[str]) -> list[str]:
    return [view_names[int(j)] for j in subset]


def residual_for_subset(
    subset: Subset,
    *,
    losses_by_view: list[set[Pair]],
    R_sigma: set[Pair],
) -> set[Pair]:
    losses = [losses_by_view[int(j)] for j in subset]
    return residual_loss(losses=losses, R_sigma=R_sigma)


def pair_to_list(pair: Pair) -> list[int]:
    return [int(pair[0]), int(pair[1])]


def subset_record(
    subset: Subset,
    *,
    view_names: list[str],
    losses_by_view: list[set[Pair]],
    R_sigma: set[Pair],
) -> dict[str, Any]:
    res = residual_for_subset(subset, losses_by_view=losses_by_view, R_sigma=R_sigma)
    gains: dict[str, int] = {}
    for j, name in enumerate(view_names):
        if j not in subset:
            gains[name] = delta_gain(L_res=res, L_j=losses_by_view[j], R_sigma=R_sigma)
    return {
        "subset": list(subset),
        "names": subset_names(subset, view_names),
        "rho": rho(res),
        "closed": len(res) == 0,
        "candidate_gains": gains,
    }


def loss_profile_key(L: set[Pair]) -> tuple[Pair, ...]:
    return tuple(sorted((int(a), int(b)) for a, b in L))


def compute_audit(scenario: Scenario, *, max_exhaustive_views: int, include_pairs: bool) -> dict[str, Any]:
    n_views = len(scenario.views)
    if n_views > int(max_exhaustive_views):
        raise ValueError(
            f"exhaustive audit requested for {n_views} views, above max_exhaustive_views={max_exhaustive_views}"
        )

    sigma_by_state = tuple(int(x) for x in scenario.sigma_labels)
    R_sigma = required_distinctions(n=scenario.n_states, sigma=lambda i: sigma_by_state[int(i)])
    view_names = [v.name for v in scenario.views]

    partitions: list[Partition] = [Partition.from_labels(list(v.labels)) for v in scenario.views]
    confusions_by_view = [confusions_of_partition(p) for p in partitions]
    losses_by_view = [loss_set(R_sigma=R_sigma, C_E=C) for C in confusions_by_view]
    separated_by_view = [set(R_sigma.difference(L)) for L in losses_by_view]

    subsets = all_subsets(n_views)
    residuals_by_subset: dict[Subset, set[Pair]] = {
        I: residual_for_subset(I, losses_by_view=losses_by_view, R_sigma=R_sigma) for I in subsets
    }
    rho_by_subset: dict[Subset, int] = {I: rho(residuals_by_subset[I]) for I in subsets}

    minimal_closing: list[Subset] = []
    for I in subsets:
        if rho_by_subset[I] != 0:
            continue
        if all(rho_by_subset[K] > 0 for K in proper_subsets(I)):
            minimal_closing.append(I)

    full_subset = tuple(range(n_views))
    full_residual = residuals_by_subset[full_subset]

    greedy = greedy_select(R_sigma=R_sigma, losses_by_view=losses_by_view, max_steps=n_views)
    greedy_path: list[dict[str, Any]] = []
    cur: Subset = ()
    greedy_path.append(
        {"step": 0, "subset": [], "names": [], "rho": rho_by_subset[cur], "gain": 0}
    )
    for t, j in enumerate(greedy, start=1):
        before = rho_by_subset[cur]
        cur = tuple(sorted(set(cur).union({int(j)})))
        after = rho_by_subset[cur]
        greedy_path.append(
            {
                "step": int(t),
                "added": int(j),
                "added_name": view_names[int(j)],
                "subset": list(cur),
                "names": subset_names(cur, view_names),
                "rho": int(after),
                "gain": int(before - after),
            }
        )

    duplicate_loss_profiles: list[dict[str, Any]] = []
    grouped: dict[tuple[Pair, ...], list[int]] = {}
    for j, L in enumerate(losses_by_view):
        grouped.setdefault(loss_profile_key(L), []).append(int(j))
    for js in grouped.values():
        if len(js) > 1:
            duplicate_loss_profiles.append(
                {"views": js, "names": [view_names[j] for j in js], "loss_size": len(losses_by_view[js[0]])}
            )

    view_records: list[dict[str, Any]] = []
    for j, name in enumerate(view_names):
        alone = (int(j),)
        gain_empty = len(R_sigma) - rho_by_subset[alone]
        without_j = tuple(i for i in range(n_views) if i != j)
        with_all = rho_by_subset[full_subset]
        after_ablation = rho_by_subset[without_j]
        view_records.append(
            {
                "index": int(j),
                "name": name,
                "classes": len(set(scenario.views[j].labels)),
                "loss_count": len(losses_by_view[j]),
                "separation_count": len(separated_by_view[j]),
                "gain_from_empty": int(gain_empty),
                "useless_from_empty": int(gain_empty) == 0,
                "essential_in_full_closure": with_all == 0 and after_ablation > 0,
                "redundant_in_full_closure": with_all == 0 and after_ablation == 0,
                "rho_after_full_ablation": int(after_ablation),
            }
        )

    pair_incidence: list[dict[str, Any]] = []
    lost_count_hist: dict[str, int] = {}
    separated_count_hist: dict[str, int] = {}
    for pair in sorted(R_sigma):
        lost_by = [j for j, L in enumerate(losses_by_view) if pair in L]
        separated_by = [j for j, A in enumerate(separated_by_view) if pair in A]
        lost_count_hist[str(len(lost_by))] = lost_count_hist.get(str(len(lost_by)), 0) + 1
        separated_count_hist[str(len(separated_by))] = separated_count_hist.get(
            str(len(separated_by)), 0
        ) + 1
        if include_pairs:
            pair_incidence.append(
                {
                    "pair": pair_to_list(pair),
                    "sigma": [sigma_by_state[pair[0]], sigma_by_state[pair[1]]],
                    "lost_by": lost_by,
                    "lost_by_names": [view_names[j] for j in lost_by],
                    "separated_by": separated_by,
                    "separated_by_names": [view_names[j] for j in separated_by],
                }
            )

    subset_records = [
        subset_record(I, view_names=view_names, losses_by_view=losses_by_view, R_sigma=R_sigma)
        for I in subsets
    ]
    minimal_records: list[dict[str, Any]] = []
    for I in minimal_closing:
        ablations: list[dict[str, Any]] = []
        for j in I:
            K = tuple(x for x in I if x != j)
            ablations.append(
                {
                    "removed": int(j),
                    "removed_name": view_names[int(j)],
                    "rho_without": int(rho_by_subset[K]),
                    "essential": rho_by_subset[K] > 0,
                }
            )
        minimal_records.append(
            {
                "subset": list(I),
                "names": subset_names(I, view_names),
                "size": len(I),
                "ablations": ablations,
            }
        )

    classification: list[str] = []
    if rho_by_subset[full_subset] > 0:
        classification.append("residual_irreducible_under_available_views")
    if duplicate_loss_profiles:
        classification.append("redundance")
    if any(r["useless_from_empty"] for r in view_records):
        classification.append("interface_inutile")
    if minimal_closing:
        min_size = min(len(I) for I in minimal_closing)
        if min_size >= 2:
            classification.append("complementarite")
        if min_size == n_views and all(rho_by_subset[(j,)] > 0 for j in range(n_views)):
            classification.append("synergie_stricte_full_family")

    return {
        "audit": "compatdim_multiview_audit_v1",
        "scenario": {
            "name": scenario.name,
            "description": scenario.description,
            "n_states": scenario.n_states,
            "n_views": n_views,
            "view_names": view_names,
            "sigma_classes": len(set(sigma_by_state)),
        },
        "summary": {
            "required_distinctions": len(R_sigma),
            "rho_empty": int(rho_by_subset[()]),
            "rho_full": int(rho_by_subset[full_subset]),
            "closed_full": rho_by_subset[full_subset] == 0,
            "minimal_closing_count": len(minimal_closing),
            "minimal_closing_sizes": sorted({len(I) for I in minimal_closing}),
            "classification": sorted(set(classification)),
        },
        "views": view_records,
        "duplicate_loss_profiles": duplicate_loss_profiles,
        "minimal_closing_coalitions": minimal_records,
        "greedy": {
            "selected": list(greedy),
            "selected_names": [view_names[j] for j in greedy],
            "closed": rho_by_subset[tuple(sorted(greedy))] == 0,
            "path": greedy_path,
        },
        "incidence_histograms": {
            "lost_count": lost_count_hist,
            "separated_count": separated_count_hist,
        },
        "subfamilies": subset_records,
        "pair_incidence": pair_incidence,
        "residual_full_pairs": [pair_to_list(p) for p in sorted(full_residual)],
    }


def script_sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def write_outputs(
    result: dict[str, Any],
    *,
    out_dir: Path,
    command: list[str],
    source_path: Path,
    smoke: bool,
    frozen_prefix: str | None,
    frozen_source_sha: str | None,
) -> dict[str, str]:
    out_dir.mkdir(parents=True, exist_ok=True)
    sha = frozen_source_sha or script_sha(source_path)
    if frozen_prefix is None:
        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        prefix = f"compatdim_multiview_audit_v1_{stamp}_{sha[:12]}"
    else:
        prefix = frozen_prefix
        parts = prefix.split("_")
        stamp = parts[-2] if len(parts) >= 2 else "unknown"

    frozen_script = out_dir / f"{prefix}.py"
    out_jsonl = out_dir / f"{prefix}.jsonl"
    out_txt = out_dir / f"{prefix}.txt"
    if not smoke and source_path != frozen_script:
        shutil.copy2(source_path, frozen_script)
    else:
        frozen_script = source_path if not smoke else out_dir / f"{prefix}_smoke_copy_skipped.py"

    payload = dict(result)
    payload["provenance"] = {
        "script": str(source_path),
        "script_sha256": sha,
        "timestamp_utc": stamp,
        "command": command,
        "frozen_script": str(frozen_script),
        "smoke": bool(smoke),
    }

    out_jsonl.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")
    lines = [
        "compatdim_multiview_audit_v1",
        f"command: {' '.join(command)}",
        f"script: {source_path}",
        f"script_sha256: {sha}",
        f"timestamp_utc: {stamp}",
        f"frozen_script: {frozen_script}",
        f"smoke: {bool(smoke)}",
        "",
        json.dumps(payload["summary"], indent=2, sort_keys=True),
    ]
    out_txt.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return {
        "script_sha256": sha,
        "frozen_script": str(frozen_script),
        "out_jsonl": str(out_jsonl),
        "out_txt": str(out_txt),
    }


def build_scenario_from_args(args: argparse.Namespace) -> Scenario:
    if args.scenario == "bits":
        return build_bits_scenario(
            n_bits=args.n_bits,
            target=args.target,
            duplicate_first=args.duplicate_first,
            useless_view=args.useless_view,
        )
    if args.scenario == "windows":
        return build_window_scenario(n_bits=args.n_bits, window=args.window)
    raise ValueError(f"unknown scenario: {args.scenario}")


def parse_args(argv: list[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="Exact finite audit for multi-interface residual closure and minimal access coalitions."
    )
    p.add_argument("--scenario", choices=["bits", "windows"], default="bits")
    p.add_argument("--n-bits", type=int, default=3)
    p.add_argument("--target", choices=["full", "parity", "first-two"], default="full")
    p.add_argument("--window", type=int, default=2)
    p.add_argument("--duplicate-first", action="store_true")
    p.add_argument("--useless-view", action="store_true")
    p.add_argument("--max-exhaustive-views", type=int, default=12)
    p.add_argument("--include-pairs", action="store_true")
    p.add_argument(
        "--out-dir",
        type=Path,
        default=None,
        help="Write frozen-protocol outputs into this directory. Use /tmp or --smoke for quick tests.",
    )
    p.add_argument(
        "--smoke",
        action="store_true",
        help="Mark this as a smoke run. Outputs remain allowed, but the script copy is skipped.",
    )
    p.add_argument("--frozen-prefix", default=None, help=argparse.SUPPRESS)
    p.add_argument("--frozen-source-sha", default=None, help=argparse.SUPPRESS)
    return p.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    if argv is None:
        argv = sys.argv[1:]
    args = parse_args(argv)

    if args.out_dir is not None and not args.smoke and args.frozen_source_sha is None:
        out_dir = Path(args.out_dir)
        out_dir.mkdir(parents=True, exist_ok=True)
        sha = script_sha(THIS_FILE)
        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        prefix = f"compatdim_multiview_audit_v1_{stamp}_{sha[:12]}"
        frozen_script = out_dir / f"{prefix}.py"
        shutil.copy2(THIS_FILE, frozen_script)
        cmd = [
            sys.executable,
            str(frozen_script),
            *argv,
            "--frozen-prefix",
            prefix,
            "--frozen-source-sha",
            sha,
        ]
        env = dict(os.environ)
        env["COMPATDIM_ALGEBRA_KERNEL"] = str(ALGEBRA_KERNEL)
        completed = subprocess.run(cmd, check=False, env=env)
        return int(completed.returncode)

    scenario = build_scenario_from_args(args)
    result = compute_audit(
        scenario,
        max_exhaustive_views=args.max_exhaustive_views,
        include_pairs=args.include_pairs,
    )
    if args.out_dir is not None:
        outputs = write_outputs(
            result,
            out_dir=args.out_dir,
            command=[sys.executable, str(THIS_FILE), *argv],
            source_path=THIS_FILE,
            smoke=bool(args.smoke),
            frozen_prefix=args.frozen_prefix,
            frozen_source_sha=args.frozen_source_sha,
        )
        result["outputs"] = outputs
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
