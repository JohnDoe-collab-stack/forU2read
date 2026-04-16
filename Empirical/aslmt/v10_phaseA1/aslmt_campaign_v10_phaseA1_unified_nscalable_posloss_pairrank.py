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


def _zs_for_n_A1(n: int) -> list[int]:
    zs = [int(n), int(n - 1), int(n // 2)]
    zs = [z for z in zs if z >= 2]
    return sorted(set(zs))


def _make_snapshot(*, ts: str, bundle_hash: str, src_files: list[Path]) -> dict:
    snap_root = SNAP_DIR / f"aslmt_v10_phaseA1_unified_nscalable_posloss_pairrank_{ts}_{bundle_hash[:12]}"
    snap_root.mkdir(parents=True, exist_ok=False)
    for p in src_files:
        (snap_root / p.name).write_text(p.read_text(encoding="utf-8"), encoding="utf-8")
    manifest = {
        "kind": "aslmt_v10_phaseA1_unified_nscalable_posloss_pairrank_snapshot",
        "bundle_hash": bundle_hash,
        "bundle_hash_short": bundle_hash[:12],
        "files": [{"name": p.name, "sha256": _sha256_file(snap_root / p.name)} for p in src_files],
        "snapshot_dir": str(snap_root),
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
    w_z: float,
    w_k: float,
    w_pos: float,
    w_rank_img: float,
    rank_n_ctx: int,
    rank_ood_ratio: float,
) -> int:
    train_script = snapshot_dir / "aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood_posloss_pairrank_nscalable.py"
    batch_size = 64 if profile == "smoke" else 128
    lr = 1e-3
    train_ood_ratio = 0.5
    pair_n_ctx = 32 if profile == "smoke" else 64
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
        str(float(w_z)),
        "--w-k",
        str(float(w_k)),
        "--w-pos",
        str(float(w_pos)),
        "--w-rank-img",
        str(float(w_rank_img)),
        "--rank-n-ctx",
        str(int(rank_n_ctx)),
        "--rank-ood-ratio",
        str(float(rank_ood_ratio)),
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
    out_txt.write_text(out_txt.read_text(encoding="utf-8") + f"SCRIPT_SHA256: {_sha256_file(train_script)}\n", encoding="utf-8")
    with open(out_txt, "a", encoding="utf-8") as f:
        p = subprocess.run(cmd, cwd=str(snapshot_dir), stdout=f, stderr=subprocess.STDOUT)
        return int(p.returncode)


def _run_verify_matrix(*, snapshot_dir: Path, master_jsonl: Path, out_txt: Path, n_list: list[int], profile: str) -> int:
    verify_script = snapshot_dir / "verify_aslmt_v10_phaseA1_matrix.py"
    cmd = [
        sys.executable,
        "-u",
        str(verify_script),
        "--master-jsonl",
        str(master_jsonl),
        "--profile",
        str(profile),
        "--n-classes-list",
        ",".join(str(int(n)) for n in n_list),
        "--z-policy",
        "A1",
    ]
    out_txt.write_text("CMD: " + " ".join(cmd) + "\n", encoding="utf-8")
    out_txt.write_text(out_txt.read_text(encoding="utf-8") + f"SCRIPT_SHA256: {_sha256_file(verify_script)}\n", encoding="utf-8")
    with open(out_txt, "a", encoding="utf-8") as f:
        p = subprocess.run(cmd, cwd=str(snapshot_dir), stdout=f, stderr=subprocess.STDOUT)
        return int(p.returncode)


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--profile", type=str, default="smoke", choices=["smoke", "solid"])
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--seed-from", type=int, default=0)
    p.add_argument("--seed-to", type=int, default=0)
    p.add_argument("--steps", type=int, default=9000)
    p.add_argument("--n-classes-list", type=str, required=True)
    p.add_argument("--w-z", type=float, default=5.0)
    p.add_argument("--w-k", type=float, default=1.0)
    p.add_argument("--w-pos", type=float, default=0.25)
    p.add_argument("--w-rank-img", type=float, default=0.25)
    p.add_argument("--rank-n-ctx", type=int, default=8)
    p.add_argument("--rank-ood-ratio", type=float, default=0.5)
    args = p.parse_args()

    n_list = _parse_int_list(args.n_classes_list)
    seed_from = int(args.seed_from)
    seed_to = int(args.seed_to)
    if seed_to < seed_from:
        raise SystemExit("--seed-to must be >= --seed-from")

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")

    # Source bundle (frozen scripts copied into snapshot).
    v9_dir = ASLMT_DIR / "v9_unified"
    src_files = [
        v9_dir / "aslmt_model_v9_unified_double_barrier_minlift.py",
        v9_dir / "render_v9_unified_paired_ctx_nscalable.py",
        v9_dir / "aslmt_env_v9_unified_double_barrier_minlift_nscalable.py",
        v9_dir / "aslmt_train_v9_unified_double_barrier_minlift_seeded_pair_trainood_posloss_pairrank_nscalable.py",
        Path(__file__).resolve().parent / "verify_aslmt_v10_phaseA1_matrix.py",
    ]
    bundle_hash = _bundle_hash(src_files)
    manifest = _make_snapshot(ts=ts, bundle_hash=bundle_hash, src_files=src_files)
    snapshot_dir = Path(manifest["snapshot_dir"])

    run_dir = RUNS_DIR / f"aslmt_v10_phaseA1_unified_nscalable_posloss_pairrank_{ts}_{bundle_hash[:12]}"
    run_dir.mkdir(parents=True, exist_ok=False)

    master_jsonl = run_dir / f"v10_master_{ts}_{bundle_hash[:12]}.jsonl"
    master_jsonl.write_text("", encoding="utf-8")

    # Execute matrix.
    for n in n_list:
        zs = _zs_for_n_A1(int(n))
        for z in zs:
            for seed in range(seed_from, seed_to + 1):
                out_txt = run_dir / f"train_{ts}_{bundle_hash[:12]}_n{int(n)}_z{int(z)}_seed{int(seed)}.txt"
                rc = _run_train(
                    snapshot_dir=snapshot_dir,
                    out_jsonl=master_jsonl,
                    out_txt=out_txt,
                    seed=int(seed),
                    steps=int(args.steps),
                    device=str(args.device),
                    n_classes=int(n),
                    z_classes=int(z),
                    profile=str(args.profile),
                    w_z=float(args.w_z),
                    w_k=float(args.w_k),
                    w_pos=float(args.w_pos),
                    w_rank_img=float(args.w_rank_img),
                    rank_n_ctx=int(args.rank_n_ctx),
                    rank_ood_ratio=float(args.rank_ood_ratio),
                )
                if rc != 0:
                    raise SystemExit(f"train failed: n={int(n)} z={int(z)} seed={int(seed)} rc={int(rc)} (see {out_txt})")

    # Verify.
    verify_txt = run_dir / f"verify_{ts}_{bundle_hash[:12]}.txt"
    rc = _run_verify_matrix(snapshot_dir=snapshot_dir, master_jsonl=master_jsonl, out_txt=verify_txt, n_list=n_list, profile=str(args.profile))
    if rc != 0:
        raise SystemExit(f"verify failed rc={int(rc)} (see {verify_txt})")

    print(f"[OK] v10 Phase A1 campaign complete. run_dir={run_dir}")


if __name__ == "__main__":
    main()

