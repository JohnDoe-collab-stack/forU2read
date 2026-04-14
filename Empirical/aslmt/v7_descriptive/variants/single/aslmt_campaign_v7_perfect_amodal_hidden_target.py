#!/usr/bin/env python3
from __future__ import annotations

"""
ASLMT v7 runner: Perfect Amodal (Hidden-Target) witness.
Creates a frozen snapshot (timestamp+sha256 bundle) and runs one or many seeds on CPU/CUDA.
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
RUNS_DIR = HERE.parent / "runs"
# Keep snapshots under runs/ so they are covered by runs/ ignore rules.
SNAP_DIR = RUNS_DIR / "snapshots"


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


def _make_snapshot(*, ts: str, bundle_hash: str, src_files: list[Path], train_script_name: str) -> dict:
    SNAP_DIR.mkdir(parents=True, exist_ok=True)
    snap_root = SNAP_DIR / f"aslmt_v7_{ts}_{bundle_hash[:12]}"
    snap_root.mkdir(parents=True, exist_ok=False)

    for p in src_files:
        shutil.copy2(p, snap_root / p.name)

    train_src = snap_root / train_script_name
    train_dst = snap_root / f"{Path(train_script_name).stem}_{ts}_{bundle_hash[:12]}.py"
    train_src.replace(train_dst)

    manifest = {
        "ts": ts,
        "bundle_hash": bundle_hash,
        "bundle_hash_short": bundle_hash[:12],
        "snapshot_dir": str(snap_root),
        "train_script": str(train_dst),
        "files": [{"name": p.name, "sha256": _sha256_file(snap_root / p.name)} for p in src_files if p.name != train_script_name]
        + [{"name": train_dst.name, "sha256": _sha256_file(train_dst)}],
    }
    with open(snap_root / "manifest.json", "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2, sort_keys=True)
    return manifest


def _run_one(*, manifest: dict, seed: int, device: str, steps: int, batch_size: int, lr: float, w_jepa: float) -> dict:
    RUNS_DIR.mkdir(parents=True, exist_ok=True)
    run_root = RUNS_DIR / f"aslmt_v7_{manifest['ts']}_{manifest['bundle_hash_short']}"
    run_root.mkdir(parents=True, exist_ok=True)

    out_jsonl = run_root / f"master_{manifest['ts']}_{manifest['bundle_hash_short']}.jsonl"
    out_txt = run_root / f"log_{manifest['ts']}_{manifest['bundle_hash_short']}_seed{seed}.txt"

    cmd = [
        sys.executable,
        manifest["train_script"],
        "--seed",
        str(int(seed)),
        "--steps",
        str(int(steps)),
        "--batch-size",
        str(int(batch_size)),
        "--lr",
        str(float(lr)),
        "--w-jepa",
        str(float(w_jepa)),
        "--device",
        str(device),
        "--out-jsonl",
        str(out_jsonl),
    ]

    with open(out_txt, "w", encoding="utf-8") as f:
        f.write("cmd: " + " ".join(cmd) + "\n")
        f.write("cwd: " + os.getcwd() + "\n")
        f.write("manifest: " + json.dumps(manifest, sort_keys=True) + "\n")

    subprocess.run(cmd, check=True, cwd=str(Path(manifest["snapshot_dir"])))
    return {"run_dir": str(run_root), "master_jsonl": str(out_jsonl), "log_txt": str(out_txt)}


def _run_verify(*, snapshot_dir: Path, master_jsonl: Path, out_txt: Path) -> int:
    verify_script = snapshot_dir / "verify_aslmt_v7_perfect_amodal_hidden_target.py"
    cmd = [sys.executable, str(verify_script), "--master-jsonl", str(master_jsonl)]
    with open(out_txt, "w", encoding="utf-8") as f:
        f.write("cmd: " + " ".join(cmd) + "\n")
        f.write("cwd: " + os.getcwd() + "\n")
    with open(out_txt, "a", encoding="utf-8") as f:
        p = subprocess.run(cmd, check=False, cwd=str(snapshot_dir), stdout=f, stderr=subprocess.STDOUT)
    return int(p.returncode)


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--seed-from", type=int, default=None)
    p.add_argument("--seed-to", type=int, default=None)
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--steps", type=int, default=3000)
    p.add_argument("--batch-size", type=int, default=128)
    p.add_argument("--lr", type=float, default=1e-3)
    p.add_argument("--w-jepa", type=float, default=0.1)
    p.add_argument(
        "--train-script",
        type=str,
        default="aslmt_train_v7_perfect_amodal_hidden_target_seeded.py",
        help="Must live in this directory; default is the seeded (reproducible) variant.",
    )
    args = p.parse_args()

    src_files = [
        HERE / "aslmt_env_v7_perfect_amodal_hidden_target.py",
        HERE / "aslmt_model_v7_perfect_jepa.py",
        HERE / "verify_aslmt_v7_perfect_amodal_hidden_target.py",
        HERE / str(args.train_script),
    ]
    for f in src_files:
        if not f.exists():
            raise FileNotFoundError(str(f))

    ts = _timestamp()
    bundle_hash = _bundle_hash(src_files)
    manifest = _make_snapshot(ts=ts, bundle_hash=bundle_hash, src_files=src_files, train_script_name=str(args.train_script))

    if args.seed_from is None or args.seed_to is None:
        seeds = [int(args.seed)]
    else:
        seeds = list(range(int(args.seed_from), int(args.seed_to) + 1))

    runs = []
    for s in seeds:
        runs.append(
            _run_one(
                manifest=manifest,
                seed=int(s),
                device=str(args.device),
                steps=int(args.steps),
                batch_size=int(args.batch_size),
                lr=float(args.lr),
                w_jepa=float(args.w_jepa),
            )
        )

    run_root = Path(runs[0]["run_dir"])
    master_jsonl = Path(runs[0]["master_jsonl"])
    verify_txt = run_root / f"verify_{manifest['ts']}_{manifest['bundle_hash_short']}.txt"
    verify_rc = _run_verify(snapshot_dir=Path(manifest["snapshot_dir"]), master_jsonl=master_jsonl, out_txt=verify_txt)
    print(
        json.dumps(
            {"manifest": manifest, "runs": runs, "verify_txt": str(verify_txt), "verify_rc": verify_rc},
            indent=2,
            sort_keys=True,
        )
    )
    raise SystemExit(verify_rc)


if __name__ == "__main__":
    main()
