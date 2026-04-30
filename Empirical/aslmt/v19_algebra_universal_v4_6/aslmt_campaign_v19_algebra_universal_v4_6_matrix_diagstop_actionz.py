import argparse
import hashlib
import json
import shutil
from datetime import datetime
from pathlib import Path
import subprocess
import sys


HERE = Path(__file__).resolve().parent
ASLMT_DIR = HERE.parent
RUNS_DIR = ASLMT_DIR / "runs"
SNAP_DIR = RUNS_DIR / "snapshots"


def _sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    h.update(p.read_bytes())
    return h.hexdigest()


def _bundle_hash(paths: list[Path]) -> str:
    h = hashlib.sha256()
    for p in paths:
        h.update(p.name.encode("utf-8"))
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


def _now_ts() -> str:
    # Human-readable timestamps for log provenance (one per line).
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def _run_with_timestamped_log(*, cmd: list[str], out: Path) -> None:
    out.parent.mkdir(parents=True, exist_ok=True)
    with open(out, "w", encoding="utf-8") as f:
        f.write(f"{_now_ts()} CMD: {' '.join(cmd)}\n")
        f.flush()

        p = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
        )
        assert p.stdout is not None
        for line in p.stdout:
            f.write(f"{_now_ts()} {line.rstrip()}\n")
            f.flush()
        rc = p.wait()
        if int(rc) != 0:
            raise SystemExit(2)


def _partial_verify_or_die(
    *,
    snap_root: Path,
    run_dir: Path,
    master_jsonl: Path,
    ts: str,
    bundle_short: str,
    n_states: int,
    seed: int,
    profile: str,
    max_steps: int,
    py: Path,
) -> None:
    verify = snap_root / "verify_aslmt_v19_algebra_universal_v4_6_matrix.py"
    verify_cmd = [
        str(py),
        "-u",
        str(verify),
        "--master-jsonl",
        str(master_jsonl),
        "--profile",
        str(profile),
        "--min-seeds",
        "1",
        "--n-states-list",
        str(int(n_states)),
        "--max-steps",
        str(int(max_steps)),
    ]
    out = run_dir / f"partial_verify_{ts}_{bundle_short}_n{int(n_states)}_seed{int(seed)}.txt"
    _run_with_timestamped_log(cmd=verify_cmd, out=out)


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--profile", type=str, default="solid", choices=["smoke", "solid"])
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--python", type=str, default=str(sys.executable))
    p.add_argument("--seed-from", type=int, default=0)
    p.add_argument("--seed-to", type=int, default=4)
    p.add_argument("--n-states-list", type=str, required=True)
    p.add_argument("--steps", type=int, default=6000)
    p.add_argument("--batch-size", type=int, default=64)
    p.add_argument("--lr", type=float, default=3e-4)
    p.add_argument("--n-views", type=int, default=8)
    p.add_argument("--y-classes", type=int, default=2)
    p.add_argument("--obs-vocab", type=int, default=16)
    p.add_argument("--max-steps", type=int, default=3)
    p.add_argument("--tf-decay-frac", type=float, default=0.65)
    p.add_argument("--w-cand", type=float, default=0.2)
    args = p.parse_args()
    # IMPORTANT: do NOT `.resolve()` the interpreter path.
    #
    # In a venv, `.../bin/python3` is typically a symlink to `/usr/bin/python3`.
    # Resolving it would drop the venv context and can silently switch to a
    # CPU-only torch install. We want to execute the user-chosen interpreter
    # path as-is (after `~` expansion), preserving the venv.
    py_arg = str(args.python)
    if not ("/" in py_arg or "\\" in py_arg):
        found = shutil.which(py_arg)
        if found is None:
            raise SystemExit(f"--python not found on PATH: {py_arg!r}")
        py = Path(found)
    else:
        py = Path(py_arg).expanduser()
    if not py.exists():
        raise SystemExit(f"--python does not exist: {str(py)!r}")

    profile = str(args.profile)
    steps = int(args.steps)
    batch_size = int(args.batch_size)
    if profile == "smoke":
        if steps == 6000:
            steps = 300
        if batch_size == 64:
            batch_size = 32

    sources = [
        # Core runnable bundle (trainer imports these by module name).
        (HERE / "aslmt_oracle_v19_algebra_universal_v4_6_common.py"),
        (HERE / "aslmt_env_v19_algebra_universal_v4_6.py"),
        (HERE / "aslmt_model_v19_algebra_universal_v4_6_actionz.py"),
        (HERE / "aslmt_train_v19_algebra_universal_v4_6_matrix_diagstop_actionz.py"),
        (HERE / "verify_aslmt_v19_algebra_universal_v4_6_matrix.py"),
        # Protocol provenance (document + orchestrator + independent audit).
        (HERE / "aslmt_campaign_v19_algebra_universal_v4_6_matrix_diagstop_actionz.py"),
        (HERE / "audit_v19_algebra_universal_v4_6_algebra.py"),
        (HERE / "README_aslmt_v19_algebra_universal_v4_6.md"),
    ]

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    bundle_hash = _bundle_hash(sources)
    tag = f"aslmt_v19_algebra_universal_actionz_v4_6_{profile}_{ts}_{bundle_hash[:12]}"

    snap_root = SNAP_DIR / f"{tag}"
    snap_root.mkdir(parents=True, exist_ok=False)
    for pth in sources:
        shutil.copy2(pth, snap_root / pth.name)

    manifest = {
        "kind": "aslmt_v19_algebra_universal_actionz_v4_6_snapshot",
        "timestamp": ts,
        "profile": str(profile),
        "bundle_hash_sha256": bundle_hash,
        "snapshot_dir": str(snap_root),
        "sources": [{"name": p.name, "sha256": _sha256_file(p)} for p in sources],
    }
    (snap_root / "snapshot_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")

    run_dir = RUNS_DIR / f"{tag}"
    run_dir.mkdir(parents=True, exist_ok=False)
    master_jsonl = run_dir / f"v19_algebra_universal_actionz_v4_6_{profile}_master_{ts}_{bundle_hash[:12]}.jsonl"

    n_list = _parse_int_list(args.n_states_list)
    seeds = list(range(int(args.seed_from), int(args.seed_to) + 1))

    for n_states in n_list:
        for seed in seeds:
            train = snap_root / "aslmt_train_v19_algebra_universal_v4_6_matrix_diagstop_actionz.py"
            log = run_dir / f"train_{ts}_{bundle_hash[:12]}_n{int(n_states)}_seed{int(seed)}.txt"
            cmd = [
                str(py),
                "-u",
                str(train),
                "--profile",
                str(profile),
                "--device",
                str(args.device),
                "--seed",
                str(int(seed)),
                "--steps",
                str(int(steps)),
                "--batch-size",
                str(int(batch_size)),
                "--lr",
                str(float(args.lr)),
                "--n-states",
                str(int(n_states)),
                "--n-views",
                str(int(args.n_views)),
                "--y-classes",
                str(int(args.y_classes)),
                "--obs-vocab",
                str(int(args.obs_vocab)),
                "--max-steps",
                str(int(args.max_steps)),
                "--tf-decay-frac",
                str(float(args.tf_decay_frac)),
                "--w-cand",
                str(float(args.w_cand)),
                "--master-jsonl",
                str(master_jsonl),
            ]
            _run_with_timestamped_log(cmd=cmd, out=log)

            _partial_verify_or_die(
                snap_root=snap_root,
                run_dir=run_dir,
                master_jsonl=master_jsonl,
                ts=ts,
                bundle_short=bundle_hash[:12],
                n_states=int(n_states),
                seed=int(seed),
                profile=str(profile),
                max_steps=int(args.max_steps),
                py=py,
            )

    # Final verification (aggregated across the full seed range).
    # For "solid" provenance, we require that all seeds in the campaign are present.
    verify = snap_root / "verify_aslmt_v19_algebra_universal_v4_6_matrix.py"
    final_verify_cmd = [
        str(py),
        "-u",
        str(verify),
        "--master-jsonl",
        str(master_jsonl),
        "--profile",
        str(profile),
        "--min-seeds",
        str(len(seeds)),
        "--n-states-list",
        str(args.n_states_list),
        "--max-steps",
        str(int(args.max_steps)),
    ]
    final_out = run_dir / f"final_verify_{ts}_{bundle_hash[:12]}.txt"
    _run_with_timestamped_log(cmd=final_verify_cmd, out=final_out)


if __name__ == "__main__":
    main()
