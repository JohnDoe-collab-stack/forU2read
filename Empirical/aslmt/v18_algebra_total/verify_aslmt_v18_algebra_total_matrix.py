import argparse
import json
from pathlib import Path


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


def _group_records(rows: list[dict]) -> dict[tuple[int, int, int], list[dict]]:
    groups: dict[tuple[int, int, int], list[dict]] = {}
    for r in rows:
        key = (int(r["n_classes"]), int(r["z_classes"]), int(r["seed"]))
        groups.setdefault(key, []).append(r)
    return groups


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--profile", type=str, default="solid", choices=["smoke", "solid"])
    p.add_argument("--master-jsonl", type=str, required=True)
    p.add_argument("--min-seeds", type=int, default=5)
    p.add_argument("--n-classes-list", type=str, required=True)
    args = p.parse_args()

    prof = str(args.profile)
    min_seeds = int(args.min_seeds)
    n_list = _parse_int_list(args.n_classes_list)

    rows: list[dict] = []
    for line in Path(args.master_jsonl).read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        rows.append(json.loads(line))

    groups = _group_records(rows)

    ok = True
    for n in n_list:
        seeds_present = sorted({seed for (nn, _z, seed) in groups.keys() if int(nn) == int(n)})
        if len(seeds_present) < (1 if prof == "smoke" else min_seeds):
            print(f"FAIL: n={int(n)} seeds_present={seeds_present}")
            ok = False
            continue

        for seed in seeds_present:
            # Expect a reference record where z=n.
            key = (int(n), int(n), int(seed))
            if key not in groups:
                print(f"FAIL: missing ref record (n={int(n)}, z=n, seed={int(seed)})")
                ok = False
                continue
            rec = groups[key][-1]
            iid = rec["metrics"]["iid"]
            ood = rec["metrics"]["ood"]

            # Strict barrière: visible-only baseline cannot exceed chance on iid+ood.
            if float(iid["B_acc"]) > 0.60 or float(ood["B_acc"]) > 0.60:
                print(f"FAIL: baseline too good (n={int(n)} seed={int(seed)}) iid_B={iid['B_acc']} ood_B={ood['B_acc']}")
                ok = False

            # Success: active solver high acc, query high acc in both splits.
            if float(iid["A_acc"]) < 0.90 or float(ood["A_acc"]) < 0.85:
                print(f"FAIL: A_acc low (n={int(n)} seed={int(seed)}) iid_A={iid['A_acc']} ood_A={ood['A_acc']}")
                ok = False
            if float(iid["z_acc"]) < 0.95 or float(ood["z_acc"]) < 0.95:
                print(f"FAIL: z_acc low (n={int(n)} seed={int(seed)}) iid_z={iid['z_acc']} ood_z={ood['z_acc']}")
                ok = False
            if float(iid["q_acc"]) < 0.90 or float(ood["q_acc"]) < 0.85:
                print(f"FAIL: q_acc low (n={int(n)} seed={int(seed)}) iid_q={iid['q_acc']} ood_q={ood['q_acc']}")
                ok = False

    raise SystemExit(0 if ok else 2)


if __name__ == "__main__":
    main()
