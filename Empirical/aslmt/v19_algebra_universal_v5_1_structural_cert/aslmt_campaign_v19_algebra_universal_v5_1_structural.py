import argparse
import hashlib
import shutil
import subprocess
import sys
from datetime import datetime
from pathlib import Path


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


def _now_ts() -> str:
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


def main() -> None:
    p = argparse.ArgumentParser(description="Snapshot+run structural certificate+verifier for v5.1 (threshold-free).")
    p.add_argument("--python", type=str, default=str(sys.executable))
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--n-states", type=int, required=True)
    p.add_argument("--n-views", type=int, default=8)
    p.add_argument("--y-classes", type=int, default=2)
    p.add_argument("--obs-vocab", type=int, default=16)
    p.add_argument("--max-steps", type=int, default=3)
    p.add_argument("--episodes", type=int, default=1024)
    p.add_argument("--seed-base", type=int, default=0)
    p.add_argument("--policy", choices=["oracle", "model"], default="oracle")
    p.add_argument("--model-state-dict", type=str, default="")
    args = p.parse_args()

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

    paths = [
        HERE / "certify_struct_aslmt_v19_algebra_universal_v5_1.py",
        HERE / "verify_struct_aslmt_v19_algebra_universal_v5_1.py",
        HERE / "aslmt_env_v19_algebra_universal_v5_1.py",
        HERE / "aslmt_oracle_v19_algebra_universal_v5_1_common.py",
        HERE / "aslmt_model_v19_algebra_universal_v5_1_actionz.py",
        HERE / "README_structural_cert_v5_1.md",
    ]
    bundle = _bundle_hash(paths)
    bundle_short = bundle[:12]
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")

    run_dir = RUNS_DIR / f"aslmt_v19_algebra_universal_structcert_v5_1_{ts}_{bundle_short}"
    run_dir.mkdir(parents=True, exist_ok=False)
    snap_root = SNAP_DIR / f"aslmt_v19_algebra_universal_structcert_v5_1_{ts}_{bundle_short}"
    snap_root.mkdir(parents=True, exist_ok=False)
    for pth in paths:
        shutil.copy2(pth, snap_root / pth.name)

    certify = snap_root / "certify_struct_aslmt_v19_algebra_universal_v5_1.py"
    verify = snap_root / "verify_struct_aslmt_v19_algebra_universal_v5_1.py"

    for split in ["iid", "ood"]:
        cert_jsonl = run_dir / f"cert_{split}_{ts}_{bundle_short}.jsonl"
        cert_log = run_dir / f"cert_{split}_{ts}_{bundle_short}.txt"
        cert_cmd = [
            str(py),
            "-u",
            str(certify),
            "--out-jsonl",
            str(cert_jsonl),
            "--split",
            split,
            "--episodes",
            str(int(args.episodes)),
            "--seed-base",
            str(int(args.seed_base)),
            "--n-states",
            str(int(args.n_states)),
            "--n-views",
            str(int(args.n_views)),
            "--y-classes",
            str(int(args.y_classes)),
            "--obs-vocab",
            str(int(args.obs_vocab)),
            "--max-steps",
            str(int(args.max_steps)),
            "--policy",
            str(args.policy),
            "--device",
            str(args.device),
        ]
        if str(args.policy) == "model":
            if not str(args.model_state_dict):
                raise SystemExit("--model-state-dict required for --policy model")
            cert_cmd += ["--model-state-dict", str(Path(args.model_state_dict).expanduser())]
        _run_with_timestamped_log(cmd=cert_cmd, out=cert_log)

        rep_json = run_dir / f"verify_{split}_{ts}_{bundle_short}.json"
        rep_txt = run_dir / f"verify_{split}_{ts}_{bundle_short}.txt"
        verify_log = run_dir / f"verify_{split}_{ts}_{bundle_short}.log.txt"
        verify_cmd = [
            str(py),
            "-u",
            str(verify),
            "--cert-jsonl",
            str(cert_jsonl),
            "--expect-lines",
            str(int(args.episodes)),
            "--forbid-view0",
            "--forbid-repeats",
            "--out-report-json",
            str(rep_json),
            "--out-report-txt",
            str(rep_txt),
        ]
        _run_with_timestamped_log(cmd=verify_cmd, out=verify_log)

    print(f"DONE run_dir={str(run_dir)} snap_root={str(snap_root)}")


if __name__ == "__main__":
    main()

