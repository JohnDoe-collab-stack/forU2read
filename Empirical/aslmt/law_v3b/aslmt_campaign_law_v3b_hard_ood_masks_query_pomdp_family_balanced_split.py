#!/usr/bin/env python3
from __future__ import annotations

"""
ASLMT law-v3b runner: hard OOD on mask/view distribution, with a balanced split for C0 (n_hi_bits=2)
and a seed-shuffled alternating split for n_hi_bits>=3.

This variant exists to remove a potential C0 enumeration artifact while keeping the task and vocabulary identical.
"""

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path


HERE = Path(__file__).resolve().parent
ASLMT_ROOT = HERE.parent
RUNS_DIR = ASLMT_ROOT / "runs"
SNAP_DIR = ASLMT_ROOT / "snapshots"


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while True:
            b = f.read(1 << 20)
            if not b:
                break
            h.update(b)
    return h.hexdigest()


def _bundle_hash(paths: list[Path]) -> str:
    h = hashlib.sha256()
    for p in sorted(paths, key=lambda x: str(x)):
        h.update(str(p.name).encode("utf-8"))
        h.update(_sha256_file(p).encode("utf-8"))
    return h.hexdigest()


def _timestamp() -> str:
    return time.strftime("%Y%m%d_%H%M%S")


def _make_snapshot(*, ts: str, bundle_hash: str, src_files: list[Path]) -> dict:
    SNAP_DIR.mkdir(parents=True, exist_ok=True)
    snap_root = SNAP_DIR / f"aslmt_law_v3b_{ts}_{bundle_hash[:12]}"
    snap_root.mkdir(parents=True, exist_ok=False)

    for p in src_files:
        shutil.copy2(p, snap_root / p.name)

    train_src = snap_root / "aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py"
    train_dst = snap_root / f"aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split_{ts}_{bundle_hash[:12]}.py"
    train_src.replace(train_dst)

    manifest = {
        "ts": ts,
        "bundle_hash": bundle_hash,
        "bundle_hash_short": bundle_hash[:12],
        "snapshot_dir": str(snap_root),
        "train_script": str(train_dst),
        "files": [{"name": p.name, "sha256": _sha256_file(snap_root / p.name)} for p in src_files if p.name != "aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py"]
        + [{"name": train_dst.name, "sha256": _sha256_file(train_dst)}],
    }
    with open(snap_root / "manifest.json", "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2, sort_keys=True)
    return manifest


def _run_one(*, manifest: dict, seed: int, profile: str, device: str, cfg_name: str) -> dict:
    RUNS_DIR.mkdir(parents=True, exist_ok=True)
    run_root = RUNS_DIR / f"aslmt_law_v3b_{manifest['ts']}_{manifest['bundle_hash_short']}"
    run_root.mkdir(parents=True, exist_ok=True)

    out_jsonl = run_root / f"master_{manifest['ts']}_{manifest['bundle_hash_short']}.jsonl"
    out_txt = run_root / f"log_{manifest['ts']}_{manifest['bundle_hash_short']}_{cfg_name}_seed{seed}.txt"

    cmd = [
        sys.executable,
        manifest["train_script"],
        "--snapshot-tag",
        f"{manifest['ts']}_{manifest['bundle_hash_short']}",
        "--seed",
        str(int(seed)),
        "--profile",
        str(profile),
        "--device",
        str(device),
        "--cfg-name",
        str(cfg_name),
        "--out-jsonl",
        str(out_jsonl),
        "--out-txt",
        str(out_txt),
    ]

    with open(out_txt, "w", encoding="utf-8") as f:
        f.write("cmd: " + " ".join(cmd) + "\n")
        f.write("cwd: " + os.getcwd() + "\n")
        f.write("manifest: " + json.dumps(manifest, sort_keys=True) + "\n")

    subprocess.run(cmd, check=True, cwd=str(Path(manifest["snapshot_dir"])))
    return {"run_dir": str(run_root), "master_jsonl": str(out_jsonl), "log_txt": str(out_txt)}


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--profile", type=str, default="smoke", choices=["smoke", "solid"])
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--seed-from", type=int, default=None)
    p.add_argument("--seed-to", type=int, default=None)
    p.add_argument("--device", type=str, default="cpu")
    args = p.parse_args()

    src_files = [
        HERE / "aslmt_env_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py",
        HERE / "aslmt_model_law_v3b_memory.py",
        HERE / "aslmt_train_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split.py",
    ]
    for f in src_files:
        if not f.exists():
            raise FileNotFoundError(str(f))

    ts = _timestamp()
    bundle_hash = _bundle_hash(src_files)
    manifest = _make_snapshot(ts=ts, bundle_hash=bundle_hash, src_files=src_files)

    if args.seed_from is None or args.seed_to is None:
        seeds = [int(args.seed)]
    else:
        seeds = list(range(int(args.seed_from), int(args.seed_to) + 1))

    cfg_names = ["C0_16b_4i_2hi", "C1_64b_6i_3hi", "C2_128b_7i_4hi"]

    runs = []
    for cfg_name in cfg_names:
        for s in seeds:
            runs.append(_run_one(manifest=manifest, seed=int(s), profile=str(args.profile), device=str(args.device), cfg_name=str(cfg_name)))

    print(json.dumps({"manifest": manifest, "runs": runs}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
