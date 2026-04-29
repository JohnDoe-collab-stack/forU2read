import argparse
import hashlib
import json
import shutil
from datetime import datetime
from pathlib import Path
from subprocess import run


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
) -> None:
    verify = snap_root / "verify_aslmt_v19_algebra_universal_v2_matrix.py"
    verify_cmd = [
        "/home/frederick/.venvs/cofrs-gpu/bin/python3",
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
    out.write_text(" ".join(verify_cmd) + "\n\n", encoding="utf-8")
    with open(out, "a", encoding="utf-8") as f:
        r = run(verify_cmd, check=False, stdout=f, stderr=f)
    if int(r.returncode) != 0:
        raise SystemExit(2)


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--profile", type=str, default="solid", choices=["smoke", "solid"])
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--seed-from", type=int, default=0)
    p.add_argument("--seed-to", type=int, default=4)
    p.add_argument("--n-states-list", type=str, required=True)
    p.add_argument("--steps", type=int, default=4000)
    p.add_argument("--batch-size", type=int, default=64)
    p.add_argument("--lr", type=float, default=3e-4)
    p.add_argument("--n-views", type=int, default=8)
    p.add_argument("--y-classes", type=int, default=2)
    p.add_argument("--obs-vocab", type=int, default=16)
    p.add_argument("--max-steps", type=int, default=3)
    p.add_argument("--tf-decay-frac", type=float, default=0.8)
    args = p.parse_args()

    profile = str(args.profile)
    steps = int(args.steps)
    batch_size = int(args.batch_size)
    if profile == "smoke":
        if steps == 4000:
            steps = 300
        if batch_size == 64:
            batch_size = 32

    sources = [
        (HERE / "aslmt_oracle_v19_algebra_universal_v2_common.py"),
        (HERE / "aslmt_env_v19_algebra_universal_v2.py"),
        (HERE / "aslmt_model_v19_algebra_universal_v2_actionz.py"),
        (HERE / "aslmt_train_v19_algebra_universal_v2_matrix_diagstop_actionz.py"),
        (HERE / "verify_aslmt_v19_algebra_universal_v2_matrix.py"),
    ]

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    bundle_hash = _bundle_hash(sources)
    tag = f"aslmt_v19_algebra_universal_actionz_v2_{profile}_{ts}_{bundle_hash[:12]}"

    snap_root = SNAP_DIR / f"{tag}"
    snap_root.mkdir(parents=True, exist_ok=False)
    for pth in sources:
        shutil.copy2(pth, snap_root / pth.name)

    manifest = {
        "kind": "aslmt_v19_algebra_universal_actionz_v2_snapshot",
        "timestamp": ts,
        "profile": str(profile),
        "bundle_hash_sha256": bundle_hash,
        "snapshot_dir": str(snap_root),
        "sources": [{"name": p.name, "sha256": _sha256_file(p)} for p in sources],
    }
    (snap_root / "snapshot_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")

    run_dir = RUNS_DIR / f"{tag}"
    run_dir.mkdir(parents=True, exist_ok=False)
    master_jsonl = run_dir / f"v19_algebra_universal_actionz_v2_{profile}_master_{ts}_{bundle_hash[:12]}.jsonl"

    n_list = _parse_int_list(args.n_states_list)
    seeds = list(range(int(args.seed_from), int(args.seed_to) + 1))

    for n_states in n_list:
        for seed in seeds:
            train = snap_root / "aslmt_train_v19_algebra_universal_v2_matrix_diagstop_actionz.py"
            log = run_dir / f"train_{ts}_{bundle_hash[:12]}_n{int(n_states)}_seed{int(seed)}.txt"
            cmd = [
                "/home/frederick/.venvs/cofrs-gpu/bin/python3",
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
                "--master-jsonl",
                str(master_jsonl),
            ]
            log.write_text(" ".join(cmd) + "\n\n", encoding="utf-8")
            with open(log, "a", encoding="utf-8") as f:
                r = run(cmd, check=False, stdout=f, stderr=f)
            if int(r.returncode) != 0:
                raise SystemExit(2)

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
            )


if __name__ == "__main__":
    main()

