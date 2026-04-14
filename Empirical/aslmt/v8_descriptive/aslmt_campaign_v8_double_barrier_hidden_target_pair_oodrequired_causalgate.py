import argparse
import hashlib
import json
import subprocess
import sys
from datetime import datetime
from pathlib import Path


ASLMT_DIR = Path(__file__).resolve().parents[1]
RUNS_DIR = ASLMT_DIR / "runs"
SNAP_DIR = RUNS_DIR / "snapshots"


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _bundle_hash(files: list[Path]) -> str:
    h = hashlib.sha256()
    for p in files:
        h.update(_sha256_file(p).encode("utf-8"))
    return h.hexdigest()


def _make_snapshot(*, ts: str, bundle_hash: str, src_files: list[Path], train_script_name: str) -> dict:
    snap_root = SNAP_DIR / f"aslmt_v8_pair_oodrequired_causalgate_{ts}_{bundle_hash[:12]}"
    snap_root.mkdir(parents=True, exist_ok=False)
    for p in src_files:
        (snap_root / p.name).write_text(p.read_text(encoding="utf-8"), encoding="utf-8")
    manifest = {
        "kind": "aslmt_v8_pair_oodrequired_causalgate_snapshot",
        "bundle_hash": bundle_hash,
        "bundle_hash_short": bundle_hash[:12],
        "files": [{"name": p.name, "sha256": _sha256_file(snap_root / p.name)} for p in src_files],
        "snapshot_dir": str(snap_root),
        "train_script_name": str(Path(train_script_name).name),
        "verify_script_name": "verify_aslmt_v8_double_barrier_hidden_target_pair_oodrequired_causalgate.py",
        "ts": ts,
    }
    (snap_root / "snapshot_manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return manifest


def _run_train(*, snapshot_dir: Path, out_jsonl: Path, out_txt: Path, seed: int, steps: int, device: str) -> int:
    train_script = snapshot_dir / "aslmt_train_v8_double_barrier_hidden_target_seeded_pair_trainood_causalgate.py"
    cmd = [
        sys.executable,
        "-u",
        str(train_script),
        "--snapshot-tag",
        snapshot_dir.name,
        "--seed",
        str(seed),
        "--steps",
        str(steps),
        "--batch-size",
        "128",
        "--lr",
        "0.001",
        "--w-jepa",
        "0.1",
        "--train-ood-ratio",
        "0.5",
        "--device",
        str(device),
        "--out-jsonl",
        str(out_jsonl),
    ]
    out_txt.write_text("CMD: " + " ".join(cmd) + "\n", encoding="utf-8")
    with open(out_txt, "a", encoding="utf-8") as f:
        p = subprocess.run(cmd, cwd=str(snapshot_dir), stdout=f, stderr=subprocess.STDOUT)
        return int(p.returncode)


def _run_verify(*, snapshot_dir: Path, master_jsonl: Path, out_txt: Path) -> int:
    verify_script = snapshot_dir / "verify_aslmt_v8_double_barrier_hidden_target_pair_oodrequired_causalgate.py"
    cmd = [sys.executable, "-u", str(verify_script), "--master-jsonl", str(master_jsonl)]
    out_txt.write_text("CMD: " + " ".join(cmd) + "\n", encoding="utf-8")
    with open(out_txt, "a", encoding="utf-8") as f:
        p = subprocess.run(cmd, cwd=str(snapshot_dir), stdout=f, stderr=subprocess.STDOUT)
        return int(p.returncode)


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--profile", type=str, default="smoke", choices=["smoke", "solid"])
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--device", type=str, default="cpu")
    args = p.parse_args()

    profile = str(args.profile)
    steps = 300 if profile == "smoke" else 3000

    src_files = [
        (Path(__file__).parent / "aslmt_env_v8_double_barrier_hidden_target.py").resolve(),
        (Path(__file__).parent / "aslmt_model_v8_double_barrier_jepa.py").resolve(),
        (Path(__file__).parent / "render_v8_paired_ctx.py").resolve(),
        (Path(__file__).parent / "verify_aslmt_v8_double_barrier_hidden_target_pair_oodrequired_causalgate.py").resolve(),
        (Path(__file__).parent / "aslmt_train_v8_double_barrier_hidden_target_seeded_pair_trainood_causalgate.py").resolve(),
    ]

    bundle_hash = _bundle_hash(src_files)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    manifest = _make_snapshot(ts=ts, bundle_hash=bundle_hash, src_files=src_files, train_script_name=str(src_files[-1]))

    run_dir = RUNS_DIR / f"aslmt_v8_pair_oodrequired_causalgate_{ts}_{bundle_hash[:12]}"
    run_dir.mkdir(parents=True, exist_ok=False)
    master_jsonl = run_dir / f"v8_master_{ts}_{bundle_hash[:12]}.jsonl"

    train_txt = run_dir / f"train_{ts}_{bundle_hash[:12]}.txt"
    train_rc = _run_train(snapshot_dir=Path(manifest["snapshot_dir"]), out_jsonl=master_jsonl, out_txt=train_txt, seed=int(args.seed), steps=int(steps), device=str(args.device))

    verify_txt = run_dir / f"verify_{ts}_{bundle_hash[:12]}.txt"
    if train_rc != 0 or (not master_jsonl.exists()):
        verify_txt.write_text(
            "SKIP VERIFY: training failed or master jsonl missing.\n"
            f"train_rc={train_rc}\n"
            f"master_jsonl={master_jsonl}\n",
            encoding="utf-8",
        )
        verify_rc = 1
    else:
        verify_rc = _run_verify(snapshot_dir=Path(manifest["snapshot_dir"]), master_jsonl=master_jsonl, out_txt=verify_txt)

    payload = {
        "manifest": manifest,
        "run": {"run_dir": str(run_dir), "master_jsonl": str(master_jsonl), "train_rc": int(train_rc), "verify_rc": int(verify_rc), "train_txt": str(train_txt), "verify_txt": str(verify_txt)},
    }
    print(json.dumps(payload, indent=2))
    raise SystemExit(int(verify_rc))


if __name__ == "__main__":
    main()
