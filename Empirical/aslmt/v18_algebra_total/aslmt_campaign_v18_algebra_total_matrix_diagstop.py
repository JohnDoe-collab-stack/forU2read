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


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--profile", type=str, default="solid", choices=["smoke", "solid"])
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--seed-from", type=int, default=0)
    p.add_argument("--seed-to", type=int, default=4)
    p.add_argument("--n-classes-list", type=str, required=True)
    p.add_argument("--steps", type=int, default=4000)
    p.add_argument("--batch-size", type=int, default=256)
    p.add_argument("--m-actions", type=int, default=4)
    p.add_argument("--k-dim", type=int, default=2)
    args = p.parse_args()

    profile = str(args.profile)
    steps = int(args.steps)
    batch_size = int(args.batch_size)
    if profile == "smoke":
        if steps == 4000:
            steps = 1500

    sources = [
        (HERE / "aslmt_env_v18_algebra_total.py"),
        (HERE / "aslmt_model_v18_algebra_total.py"),
        (HERE / "aslmt_train_v18_algebra_total_diag.py"),
        (HERE / "verify_aslmt_v18_algebra_total_matrix.py"),
    ]

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    bundle_hash = _bundle_hash(sources)
    tag = f"aslmt_v18_algebra_total_{profile}_{ts}_{bundle_hash[:12]}"

    snap_root = SNAP_DIR / f"{tag}"
    snap_root.mkdir(parents=True, exist_ok=False)
    for pth in sources:
        shutil.copy2(pth, snap_root / pth.name)

    manifest = {
        "kind": "aslmt_v18_algebra_total_snapshot",
        "timestamp": ts,
        "profile": str(profile),
        "bundle_hash_sha256": bundle_hash,
        "snapshot_dir": str(snap_root),
        "sources": [{"name": p.name, "sha256": _sha256_file(p)} for p in sources],
    }
    (snap_root / "snapshot_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")

    run_dir = RUNS_DIR / f"{tag}"
    run_dir.mkdir(parents=True, exist_ok=False)
    master_jsonl = run_dir / f"v18_algebra_total_{profile}_master_{ts}_{bundle_hash[:12]}.jsonl"

    n_list = _parse_int_list(args.n_classes_list)
    seeds = list(range(int(args.seed_from), int(args.seed_to) + 1))

    for n in n_list:
        z_list = [int(n)]
        for z in z_list:
            for seed in seeds:
                train = snap_root / "aslmt_train_v18_algebra_total_diag.py"
                log = run_dir / f"train_{ts}_{bundle_hash[:12]}_n{int(n)}_z{int(z)}_seed{int(seed)}.txt"
                cmd = [
                    "/home/frederick/.venvs/cofrs-gpu/bin/python3",
                    "-u",
                    str(train),
                    "--profile",
                    str(profile),
                    "--seed",
                    str(int(seed)),
                    "--steps",
                    str(int(steps)),
                    "--batch-size",
                    str(int(batch_size)),
                    "--lr",
                    "0.003",
                    "--n-classes",
                    str(int(n)),
                    "--z-classes",
                    str(int(z)),
                    "--m-actions",
                    str(int(args.m_actions)),
                    "--k-dim",
                    str(int(args.k_dim)),
                    "--device",
                    str(args.device),
                    "--out-jsonl",
                    str(master_jsonl),
                ]
                log.write_text(" ".join(cmd) + "\n\n", encoding="utf-8")
                with open(log, "a", encoding="utf-8") as f:
                    run(cmd, check=True, stdout=f, stderr=f)

    verify = snap_root / "verify_aslmt_v18_algebra_total_matrix.py"
    verify_out = run_dir / f"verify_{ts}_{bundle_hash[:12]}.txt"
    verify_cmd = [
        "/home/frederick/.venvs/cofrs-gpu/bin/python3",
        "-u",
        str(verify),
        "--master-jsonl",
        str(master_jsonl),
        "--profile",
        str(profile),
        "--min-seeds",
        "5" if str(profile) == "solid" else "1",
        "--n-classes-list",
        ",".join(str(int(x)) for x in n_list),
    ]
    verify_out.write_text(" ".join(verify_cmd) + "\n\n", encoding="utf-8")
    with open(verify_out, "a", encoding="utf-8") as f:
        run(verify_cmd, check=False, stdout=f, stderr=f)


if __name__ == "__main__":
    main()
