import argparse
import hashlib
import json
import subprocess
import sys
from datetime import datetime
from pathlib import Path

"""
V2 campaign runner (frontier-injection variant).

This runner is identical to `aslmt_campaign_v7_perfect_amodal_hidden_target_pair_oodrequired_v2.py` except that it
supports an additional training flag: `--frontier-frac`, forwarded to the selected `--train-script`.

Per repo experiment rules, we do not edit historical runners already used for cited artifacts.
"""


HERE = Path(__file__).resolve().parent
ASLMT_DIR = HERE.parent
RUNS_DIR = ASLMT_DIR / "runs"
SNAP_DIR = RUNS_DIR / "snapshots"


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _bundle_hash(paths: list[Path]) -> str:
    h = hashlib.sha256()
    for p in sorted(paths, key=lambda x: x.name):
        h.update(_sha256_file(p).encode("utf-8"))
    return h.hexdigest()


def _timestamp() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def _make_snapshot(*, ts: str, bundle_hash: str, src_files: list[Path], train_script_name: str) -> dict:
    SNAP_DIR.mkdir(parents=True, exist_ok=True)
    snap_root = SNAP_DIR / f"aslmt_v7_pair_oodrequired_{ts}_{bundle_hash[:12]}"
    snap_root.mkdir(parents=True, exist_ok=False)

    train_src = HERE / train_script_name
    train_dst = snap_root / train_src.name
    train_dst.write_bytes(train_src.read_bytes())

    for p in src_files:
        # Avoid double-copy by filename; the train script is already copied to `train_dst`.
        if p.name == train_src.name:
            continue
        (snap_root / p.name).write_bytes(p.read_bytes())

    # Hygiene: compute manifest.files from what is actually present in the snapshot dir.
    copied = sorted(
        [p for p in snap_root.iterdir() if p.is_file() and p.name != "snapshot_manifest.json"],
        key=lambda x: x.name,
    )
    manifest = {
        "kind": "aslmt_v7_pair_oodrequired_snapshot",
        "ts": ts,
        "bundle_hash": bundle_hash,
        "bundle_hash_short": bundle_hash[:12],
        "snapshot_dir": str(snap_root),
        "train_script_name": str(train_src.name),
        "verify_script_name": "verify_aslmt_v7_perfect_amodal_hidden_target_pair_oodrequired.py",
        "files": [{"name": p.name, "sha256": _sha256_file(p)} for p in copied],
    }
    (snap_root / "snapshot_manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return manifest


def _run_one(
    *,
    manifest: dict,
    seed: int,
    device: str,
    steps: int,
    batch_size: int,
    lr: float,
    w_jepa: float,
    train_ood_ratio: float,
    frontier_frac: float,
) -> dict:
    run_root = RUNS_DIR / f"aslmt_v7_pair_oodrequired_{manifest['ts']}_{manifest['bundle_hash_short']}"
    run_root.mkdir(parents=True, exist_ok=False)

    master_jsonl = run_root / f"v7_master_{manifest['ts']}_{manifest['bundle_hash_short']}.jsonl"
    train_script = Path(manifest["snapshot_dir"]) / str(manifest["train_script_name"])

    # Force unbuffered output so progress logs appear promptly in train_*.txt.
    cmd = [
        sys.executable,
        "-u",
        str(train_script),
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
        "--train-ood-ratio",
        str(float(train_ood_ratio)),
        "--frontier-frac",
        str(float(frontier_frac)),
        "--device",
        str(device),
        "--out-jsonl",
        str(master_jsonl),
    ]
    out_txt = run_root / f"train_{manifest['ts']}_{manifest['bundle_hash_short']}.txt"
    with open(out_txt, "w", encoding="utf-8") as f:
        f.write("CMD: " + " ".join(cmd) + "\n")
        f.write("SNAPSHOT_DIR: " + str(manifest["snapshot_dir"]) + "\n")
        f.write("BUNDLE_HASH: " + str(manifest["bundle_hash"]) + "\n\n")
        rc = subprocess.call(cmd, stdout=f, stderr=subprocess.STDOUT, cwd=str(run_root))

    return {"run_dir": str(run_root), "master_jsonl": str(master_jsonl), "train_txt": str(out_txt), "train_rc": int(rc)}


def _run_verify(*, snapshot_dir: Path, master_jsonl: Path, out_txt: Path) -> int:
    verify_script = snapshot_dir / "verify_aslmt_v7_perfect_amodal_hidden_target_pair_oodrequired.py"
    cmd = [sys.executable, "-u", str(verify_script), "--master-jsonl", str(master_jsonl)]
    with open(out_txt, "w", encoding="utf-8") as f:
        f.write("CMD: " + " ".join(cmd) + "\n\n")
        return int(subprocess.call(cmd, stdout=f, stderr=subprocess.STDOUT))


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--steps", type=int, default=3000)
    p.add_argument("--batch-size", type=int, default=128)
    p.add_argument("--lr", type=float, default=1e-3)
    p.add_argument("--w-jepa", type=float, default=0.1)
    p.add_argument("--train-ood-ratio", type=float, default=1.0)
    p.add_argument("--frontier-frac", type=float, default=0.0)
    p.add_argument(
        "--train-script",
        type=str,
        default="variants/pair/aslmt_train_v7_perfect_amodal_hidden_target_seeded_pair_trainood_ctxaudit_frontier_inject.py",
        help="Must live in this directory; this campaign will execute exactly this file.",
    )
    args = p.parse_args()

    train_script = str(args.train_script)
    verify_script = "verify_aslmt_v7_perfect_amodal_hidden_target_pair_oodrequired.py"

    src_files = [
        HERE / "aslmt_env_v7_perfect_amodal_hidden_target.py",
        HERE / "aslmt_model_v7_perfect_jepa.py",
        HERE / "render_v7_paired_ctx.py",
        HERE / verify_script,
        HERE / train_script,
    ]
    for f in src_files:
        if not f.exists():
            raise FileNotFoundError(str(f))

    ts = _timestamp()
    bundle_hash = _bundle_hash(src_files)
    manifest = _make_snapshot(ts=ts, bundle_hash=bundle_hash, src_files=src_files, train_script_name=train_script)

    run = _run_one(
        manifest=manifest,
        seed=int(args.seed),
        device=str(args.device),
        steps=int(args.steps),
        batch_size=int(args.batch_size),
        lr=float(args.lr),
        w_jepa=float(args.w_jepa),
        train_ood_ratio=float(args.train_ood_ratio),
        frontier_frac=float(args.frontier_frac),
    )

    run_root = Path(run["run_dir"])
    master_jsonl = Path(run["master_jsonl"])
    verify_txt = run_root / f"verify_{manifest['ts']}_{manifest['bundle_hash_short']}.txt"
    verify_rc = _run_verify(snapshot_dir=Path(manifest["snapshot_dir"]), master_jsonl=master_jsonl, out_txt=verify_txt)
    print(json.dumps({"manifest": manifest, "run": run, "verify_txt": str(verify_txt), "verify_rc": verify_rc}, indent=2, sort_keys=True))
    raise SystemExit(verify_rc)


if __name__ == "__main__":
    main()

