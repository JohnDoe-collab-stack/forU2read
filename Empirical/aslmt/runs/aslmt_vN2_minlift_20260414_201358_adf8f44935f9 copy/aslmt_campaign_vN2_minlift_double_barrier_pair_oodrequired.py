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
    snap_root = SNAP_DIR / f"aslmt_vN2_minlift_{ts}_{bundle_hash[:12]}"
    snap_root.mkdir(parents=True, exist_ok=False)
    for p in src_files:
        (snap_root / p.name).write_text(p.read_text(encoding="utf-8"), encoding="utf-8")
    manifest = {
        "kind": "aslmt_vN2_minlift_snapshot",
        "bundle_hash": bundle_hash,
        "bundle_hash_short": bundle_hash[:12],
        "files": [{"name": p.name, "sha256": _sha256_file(snap_root / p.name)} for p in src_files],
        "snapshot_dir": str(snap_root),
        "train_script_name": str(Path(train_script_name).name),
        "verify_script_name": "verify_aslmt_vN2_minlift_double_barrier_pair_oodrequired.py",
        "ts": ts,
    }
    (snap_root / "snapshot_manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return manifest


def _run_train(
    *,
    snapshot_dir: Path,
    out_jsonl: Path,
    out_txt: Path,
    seed: int,
    steps: int,
    device: str,
    n_classes: int,
    z_classes: int,
    profile: str,
) -> int:
    train_script = snapshot_dir / "aslmt_train_vN2_minlift_double_barrier_seeded_pair_trainood.py"
    batch_size = 64 if profile == "smoke" else 128
    lr = 1e-3
    train_ood_ratio = 0.5
    pair_n_ctx = 32 if profile == "smoke" else 64
    w_z = 5.0
    cmd = [
        sys.executable,
        "-u",
        str(train_script),
        "--seed",
        str(seed),
        "--steps",
        str(steps),
        "--batch-size",
        str(batch_size),
        "--lr",
        str(lr),
        "--w-z",
        str(w_z),
        "--train-ood-ratio",
        str(train_ood_ratio),
        "--pair-n-ctx",
        str(pair_n_ctx),
        "--n-classes",
        str(n_classes),
        "--z-classes",
        str(z_classes),
        "--device",
        str(device),
        "--out-jsonl",
        str(out_jsonl),
    ]
    out_txt.write_text("CMD: " + " ".join(cmd) + "\n", encoding="utf-8")
    with open(out_txt, "a", encoding="utf-8") as f:
        p = subprocess.run(cmd, cwd=str(snapshot_dir), stdout=f, stderr=subprocess.STDOUT)
        return int(p.returncode)


def _run_verify(*, snapshot_dir: Path, master_jsonl: Path, out_txt: Path, n_classes: int, profile: str) -> int:
    verify_script = snapshot_dir / "verify_aslmt_vN2_minlift_double_barrier_pair_oodrequired.py"
    cmd = [sys.executable, "-u", str(verify_script), "--master-jsonl", str(master_jsonl), "--n-classes", str(n_classes), "--profile", str(profile)]
    out_txt.write_text("CMD: " + " ".join(cmd) + "\n", encoding="utf-8")
    with open(out_txt, "a", encoding="utf-8") as f:
        p = subprocess.run(cmd, cwd=str(snapshot_dir), stdout=f, stderr=subprocess.STDOUT)
        return int(p.returncode)


def _parse_z_list(s: str) -> list[int]:
    out = []
    for part in str(s).split(","):
        part = part.strip()
        if not part:
            continue
        out.append(int(part))
    if not out:
        raise ValueError("empty z-classes-list")
    return out


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--profile", type=str, default="smoke", choices=["smoke", "solid"])
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--seed-from", type=int, default=None)
    p.add_argument("--seed-to", type=int, default=None)
    p.add_argument("--n-classes", type=int, default=4)
    p.add_argument("--z-classes-list", type=str, default="")
    args = p.parse_args()

    profile = str(args.profile)
    steps = 300 if profile == "smoke" else 3000

    seeds: list[int]
    if args.seed_from is None or args.seed_to is None:
        seeds = [int(args.seed)]
    else:
        seeds = list(range(int(args.seed_from), int(args.seed_to) + 1))

    n_classes = int(args.n_classes)
    z_list = _parse_z_list(args.z_classes_list) if str(args.z_classes_list).strip() else list(range(1, n_classes + 1))

    src_files = [
        Path(__file__).resolve(),
        (Path(__file__).parent / "aslmt_env_vN2_minlift_double_barrier.py").resolve(),
        (Path(__file__).parent / "render_vN2_paired_ctx.py").resolve(),
        (Path(__file__).parent / "aslmt_model_vN2_minlift_double_barrier.py").resolve(),
        (Path(__file__).parent / "aslmt_train_vN2_minlift_double_barrier_seeded_pair_trainood.py").resolve(),
        (Path(__file__).parent / "verify_aslmt_vN2_minlift_double_barrier_pair_oodrequired.py").resolve(),
    ]
    bundle_hash = _bundle_hash(src_files)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    manifest = _make_snapshot(ts=ts, bundle_hash=bundle_hash, src_files=src_files, train_script_name=str(src_files[-2]))

    run_dir = RUNS_DIR / f"aslmt_vN2_minlift_{ts}_{bundle_hash[:12]}"
    run_dir.mkdir(parents=True, exist_ok=False)
    master_jsonl = run_dir / f"vN2_master_{ts}_{bundle_hash[:12]}.jsonl"

    for seed in seeds:
        for z_classes in z_list:
            log_txt = run_dir / f"train_{ts}_{bundle_hash[:12]}_n{n_classes}_z{z_classes}_seed{seed}.txt"
            rc = _run_train(
                snapshot_dir=Path(manifest["snapshot_dir"]),
                out_jsonl=master_jsonl,
                out_txt=log_txt,
                seed=int(seed),
                steps=int(steps),
                device=str(args.device),
                n_classes=int(n_classes),
                z_classes=int(z_classes),
                profile=profile,
            )
            if rc != 0:
                print(f"[FAIL] train rc={rc} for n={n_classes} z={z_classes} seed={seed}")

    verify_txt = run_dir / f"verify_{ts}_{bundle_hash[:12]}.txt"
    if not master_jsonl.exists():
        verify_txt.write_text(
            "SKIP VERIFY: master jsonl missing (all training runs failed before writing output).\n"
            f"master_jsonl={master_jsonl}\n",
            encoding="utf-8",
        )
        verify_rc = 1
    else:
        verify_rc = _run_verify(snapshot_dir=Path(manifest["snapshot_dir"]), master_jsonl=master_jsonl, out_txt=verify_txt, n_classes=n_classes, profile=profile)

    payload = {
        "manifest": manifest,
        "run": {"run_dir": str(run_dir), "master_jsonl": str(master_jsonl), "verify_rc": int(verify_rc), "verify_txt": str(verify_txt)},
    }
    print(json.dumps(payload, indent=2))
    raise SystemExit(int(verify_rc))


if __name__ == "__main__":
    main()

