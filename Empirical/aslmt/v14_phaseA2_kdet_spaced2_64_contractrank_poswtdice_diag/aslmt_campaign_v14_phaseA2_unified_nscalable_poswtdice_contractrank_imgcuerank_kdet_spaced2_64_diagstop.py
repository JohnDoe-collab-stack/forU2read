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


def _zs_for_n_A1(n: int) -> list[int]:
    zs = [int(n), int(n - 1), int(n // 2)]
    zs = [z for z in zs if z >= 2]
    return sorted(set(zs))


def _zs_ref_first(n: int) -> list[int]:
    zs = _zs_for_n_A1(int(n))
    if int(n) in zs:
        zs = [int(n)] + [z for z in zs if z != int(n)]
    return zs


def _partial_verify_ref_or_die(
    *,
    snap_root: Path,
    run_dir: Path,
    master_jsonl: Path,
    ts: str,
    bundle_short: str,
    n: int,
    seed: int,
    profile: str,
) -> None:
    verify = snap_root / "verify_aslmt_v14_phaseA2_matrix.py"
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
        "--n-classes-list",
        str(int(n)),
        "--z-policy",
        "explicit",
        "--z-classes-list",
        str(int(n)),
    ]
    out = run_dir / f"partial_verify_{ts}_{bundle_short}_n{int(n)}_seed{int(seed)}.txt"
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
    p.add_argument("--n-classes-list", type=str, required=True)
    p.add_argument("--steps", type=int, default=9000)
    p.add_argument("--batch-size", type=int, default=64)
    p.add_argument("--w-z", type=float, default=5.0)
    p.add_argument("--w-k", type=float, default=0.0)
    p.add_argument("--w-pos", type=float, default=0.25)
    p.add_argument("--w-rank-img", type=float, default=0.25)
    p.add_argument("--w-rank-cue", type=float, default=0.25)
    p.add_argument("--rank-n-ctx", type=int, default=8)
    p.add_argument("--rank-margin", type=float, default=1.0)
    p.add_argument("--rank-ood-ratio", type=float, default=0.5)
    p.add_argument("--w-bce", type=float, default=1.0)
    p.add_argument("--w-dice", type=float, default=0.0)
    p.add_argument("--bce-pos-weight", type=str, default="none")
    args = p.parse_args()
    if str(args.profile) == "solid":
        if int(args.rank_n_ctx) <= 0 or int(args.rank_n_ctx) > 64:
            raise SystemExit("profile=solid requires 1 <= --rank-n-ctx <= 64")
        if 64 % int(args.rank_n_ctx) != 0:
            raise SystemExit("profile=solid requires 64 to be a multiple of --rank-n-ctx")

    v9 = ASLMT_DIR / "v9_unified"
    sources = [
        v9 / "aslmt_model_v9_unified_double_barrier_minlift_kdet.py",
        v9 / "aslmt_env_v9_unified_double_barrier_minlift_nscalable_spaced2_64.py",
        v9 / "render_v9_unified_paired_ctx_nscalable_spaced2_64.py",
        (HERE / "aslmt_train_v14_unified_double_barrier_minlift_seeded_pair_trainood_poswtdice_contractrank_imgcuerank_nscalable_kdet_spaced2_64_diag.py"),
        (HERE / "verify_aslmt_v14_phaseA2_matrix.py"),
    ]

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    bundle_hash = _bundle_hash(sources)

    snap_root = SNAP_DIR / f"aslmt_v14_phaseA2_unified_nscalable_poswtdice_contractrank_imgcuerank_kdet_spaced2_64_{ts}_{bundle_hash[:12]}"
    snap_root.mkdir(parents=True, exist_ok=False)
    for pth in sources:
        shutil.copy2(pth, snap_root / pth.name)

    manifest = {
        "kind": "aslmt_v14_phaseA2_unified_nscalable_poswtdice_contractrank_imgcuerank_kdet_spaced2_64_snapshot",
        "timestamp": ts,
        "bundle_hash_sha256": bundle_hash,
        "snapshot_dir": str(snap_root),
        "sources": [{"name": p.name, "sha256": _sha256_file(p)} for p in sources],
    }
    (snap_root / "snapshot_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")

    run_dir = RUNS_DIR / f"aslmt_v14_phaseA2_unified_nscalable_poswtdice_contractrank_imgcuerank_kdet_spaced2_64_{ts}_{bundle_hash[:12]}"
    run_dir.mkdir(parents=True, exist_ok=False)
    master_jsonl = run_dir / f"v14_master_{ts}_{bundle_hash[:12]}.jsonl"

    n_list = _parse_int_list(args.n_classes_list)
    seeds = list(range(int(args.seed_from), int(args.seed_to) + 1))

    for n in n_list:
        zs = _zs_ref_first(int(n))
        for z in zs:
            for seed in seeds:
                train = snap_root / "aslmt_train_v14_unified_double_barrier_minlift_seeded_pair_trainood_poswtdice_contractrank_imgcuerank_nscalable_kdet_spaced2_64_diag.py"
                log = run_dir / f"train_{ts}_{bundle_hash[:12]}_n{int(n)}_z{int(z)}_seed{int(seed)}.txt"

                ckpt_path = ""
                faildump_path = ""
                if int(z) == int(n):
                    ckpt_path = str(run_dir / f"ckpt_{ts}_{bundle_hash[:12]}_n{int(n)}_z{int(z)}_seed{int(seed)}.pt")
                    faildump_path = str(run_dir / f"faildump_{ts}_{bundle_hash[:12]}_n{int(n)}_z{int(z)}_seed{int(seed)}.jsonl")

                cmd = [
                    "/home/frederick/.venvs/cofrs-gpu/bin/python3",
                    "-u",
                    str(train),
                    "--seed",
                    str(int(seed)),
                    "--steps",
                    str(int(args.steps)),
                    "--batch-size",
                    str(int(args.batch_size)),
                    "--lr",
                    "0.001",
                    "--w-z",
                    str(float(args.w_z)),
                    "--w-k",
                    str(float(args.w_k)),
                    "--w-pos",
                    str(float(args.w_pos)),
                    "--w-rank-img",
                    str(float(args.w_rank_img)),
                    "--w-rank-cue",
                    str(float(args.w_rank_cue)),
                    "--rank-n-ctx",
                    str(int(args.rank_n_ctx)),
                    "--rank-ood-ratio",
                    str(float(args.rank_ood_ratio)),
                    "--rank-margin",
                    str(float(args.rank_margin)),
                    "--train-ood-ratio",
                    "0.5",
                    "--pair-n-ctx",
                    "64",
                    "--img-size",
                    "64",
                    "--n-classes",
                    str(int(n)),
                    "--z-classes",
                    str(int(z)),
                    "--w-bce",
                    str(float(args.w_bce)),
                    "--w-dice",
                    str(float(args.w_dice)),
                    "--bce-pos-weight",
                    str(args.bce_pos_weight),
                    "--device",
                    str(args.device),
                    "--out-jsonl",
                    str(master_jsonl),
                ]
                if ckpt_path:
                    cmd += ["--out-ckpt", str(ckpt_path)]
                if faildump_path:
                    cmd += ["--out-faildump-jsonl", str(faildump_path)]

                log.write_text(" ".join(cmd) + "\n\n", encoding="utf-8")
                with open(log, "a", encoding="utf-8") as f:
                    run(cmd, check=True, stdout=f, stderr=f)

                if int(z) == int(n) and str(args.profile) == "solid":
                    _partial_verify_ref_or_die(
                        snap_root=snap_root,
                        run_dir=run_dir,
                        master_jsonl=master_jsonl,
                        ts=str(ts),
                        bundle_short=str(bundle_hash[:12]),
                        n=int(n),
                        seed=int(seed),
                        profile=str(args.profile),
                    )

    verify = snap_root / "verify_aslmt_v14_phaseA2_matrix.py"
    verify_out = run_dir / f"verify_{ts}_{bundle_hash[:12]}.txt"
    verify_cmd = [
        "/home/frederick/.venvs/cofrs-gpu/bin/python3",
        "-u",
        str(verify),
        "--master-jsonl",
        str(master_jsonl),
        "--profile",
        str(args.profile),
        "--min-seeds",
        "5" if str(args.profile) == "solid" else "1",
        "--n-classes-list",
        ",".join(str(int(x)) for x in n_list),
        "--z-policy",
        "A1",
    ]
    verify_out.write_text(" ".join(verify_cmd) + "\n\n", encoding="utf-8")
    with open(verify_out, "a", encoding="utf-8") as f:
        run(verify_cmd, check=False, stdout=f, stderr=f)


if __name__ == "__main__":
    main()
