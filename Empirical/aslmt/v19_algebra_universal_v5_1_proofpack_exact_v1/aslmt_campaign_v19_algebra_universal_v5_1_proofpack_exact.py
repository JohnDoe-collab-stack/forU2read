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
    p = argparse.ArgumentParser(
        description="v19 universal v5.1 proof pack (Option A: exact STOP + exact readout; learned query actions)."
    )
    p.add_argument("--profile", type=str, default="solid", choices=["smoke", "solid"])
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--python", type=str, default=str(sys.executable))
    p.add_argument("--seed-from", type=int, default=0)
    p.add_argument("--seed-to", type=int, default=0)
    p.add_argument("--n-states-list", type=str, required=True)
    p.add_argument("--steps", type=int, default=6000)
    p.add_argument("--batch-size", type=int, default=64)
    p.add_argument("--lr", type=float, default=3e-4)
    p.add_argument("--n-views", type=int, default=8)
    p.add_argument("--y-classes", type=int, default=2)
    p.add_argument("--obs-vocab", type=int, default=16)
    p.add_argument("--max-steps", type=int, default=3)
    p.add_argument("--tf-decay-frac", type=float, default=0.65)
    p.add_argument("--w-y-closed", type=float, default=2.0)
    p.add_argument("--w-cand", type=float, default=0.0)
    p.add_argument("--episodes", type=int, default=1024)
    p.add_argument("--seed-base", type=int, default=0)
    args = p.parse_args()

    # Do NOT resolve the interpreter path (preserve venv symlink context).
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

    # Snapshot inputs.
    paths = [
        HERE / "README_proofpack_exact_v5_1.md",
        HERE / "aslmt_env_v19_algebra_universal_v5_1.py",
        HERE / "aslmt_oracle_v19_algebra_universal_v5_1_common.py",
        HERE / "aslmt_model_v19_algebra_universal_v5_1_actionz.py",
        HERE / "aslmt_train_v19_algebra_universal_v5_1_matrix_diagstop_actionz.py",
        HERE / "certify_struct_aslmt_v19_algebra_universal_v5_1_exact.py",
        HERE / "verify_struct_aslmt_v19_algebra_universal_v5_1.py",
        HERE / Path(__file__).name,
    ]
    bundle = _bundle_hash(paths)
    bundle_short = bundle[:12]
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")

    run_dir = RUNS_DIR / f"aslmt_v19_algebra_universal_proofpack_exact_v5_1_{ts}_{bundle_short}"
    run_dir.mkdir(parents=True, exist_ok=False)
    snap_root = SNAP_DIR / f"aslmt_v19_algebra_universal_proofpack_exact_v5_1_{ts}_{bundle_short}"
    snap_root.mkdir(parents=True, exist_ok=False)
    for pth in paths:
        shutil.copy2(pth, snap_root / pth.name)

    train = snap_root / "aslmt_train_v19_algebra_universal_v5_1_matrix_diagstop_actionz.py"
    certify = snap_root / "certify_struct_aslmt_v19_algebra_universal_v5_1_exact.py"
    verify = snap_root / "verify_struct_aslmt_v19_algebra_universal_v5_1.py"

    n_states_list = _parse_int_list(str(args.n_states_list))

    for n_states in n_states_list:
        for seed in range(int(args.seed_from), int(args.seed_to) + 1):
            tag = f"{ts}_{bundle_short}_n{int(n_states)}_seed{int(seed)}"
            master_jsonl = run_dir / f"train_master_{tag}.jsonl"
            train_log = run_dir / f"train_{tag}.txt"
            ckpt = run_dir / f"modelA_state_dict_{tag}.pt"

            train_cmd = [
                str(py),
                "-u",
                str(train),
                "--profile",
                str(args.profile),
                "--device",
                str(args.device),
                "--seed",
                str(int(seed)),
                "--steps",
                str(int(args.steps)),
                "--batch-size",
                str(int(args.batch_size)),
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
                "--w-y-closed",
                str(float(args.w_y_closed)),
                "--w-cand",
                str(float(args.w_cand)),
                "--master-jsonl",
                str(master_jsonl),
                "--save-modelA-state-dict",
                str(ckpt),
            ]
            _run_with_timestamped_log(cmd=train_cmd, out=train_log)

            # Structural certificates + verification (IID + OOD).
            for split in ["iid", "ood"]:
                cert_jsonl = run_dir / f"cert_{split}_{tag}.jsonl"
                cert_log = run_dir / f"cert_{split}_{tag}.txt"
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
                    str(int(n_states)),
                    "--n-views",
                    str(int(args.n_views)),
                    "--y-classes",
                    str(int(args.y_classes)),
                    "--obs-vocab",
                    str(int(args.obs_vocab)),
                    "--max-steps",
                    str(int(args.max_steps)),
                    "--policy",
                    "model_exact",
                    "--device",
                    str(args.device),
                    "--model-state-dict",
                    str(ckpt),
                    "--forbid-view0",
                    "--forbid-repeats",
                ]
                _run_with_timestamped_log(cmd=cert_cmd, out=cert_log)

                rep_json = run_dir / f"verify_{split}_{tag}.json"
                rep_txt = run_dir / f"verify_{split}_{tag}.txt"
                viol_jsonl = run_dir / f"violations_{split}_{tag}.jsonl"
                verify_log = run_dir / f"verify_{split}_{tag}.log.txt"
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
                    "--out-violations-jsonl",
                    str(viol_jsonl),
                ]
                _run_with_timestamped_log(cmd=verify_cmd, out=verify_log)

    print(f"[OK] proofpack exact run_dir={str(run_dir)} snapshot_dir={str(snap_root)} bundle_hash={bundle_short}")


if __name__ == "__main__":
    main()

