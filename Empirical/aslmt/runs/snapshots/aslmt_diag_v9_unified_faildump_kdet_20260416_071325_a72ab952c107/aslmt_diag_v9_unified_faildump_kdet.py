import argparse
import hashlib
import json
import os
import subprocess
import sys
from dataclasses import asdict
from datetime import datetime
from pathlib import Path

import torch
import torch.nn.functional as F
from torch.utils.data import DataLoader

from aslmt_env_v9_unified_double_barrier_minlift_nscalable import V9UnifiedDoubleBarrierMinLiftDatasetNScalable
from aslmt_model_v9_unified_double_barrier_minlift_kdet import V9CueOnlyBaseline, V9ImageOnlyBaseline, V9MinLiftModelA
from render_v9_unified_paired_ctx_nscalable import Ctx, render


ASLMT_DIR = Path(__file__).resolve().parents[1]
RUNS_DIR = ASLMT_DIR / "runs"
SNAP_DIR = RUNS_DIR / "snapshots"


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _jsonable(x):
    if isinstance(x, (str, int, float, bool)) or x is None:
        return x
    if isinstance(x, dict):
        return {str(k): _jsonable(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [_jsonable(v) for v in x]
    return str(x)


def _xy_grid(*, H: int, W: int, device: torch.device, dtype: torch.dtype) -> torch.Tensor:
    ys = torch.linspace(-1.0, 1.0, steps=int(H), device=device, dtype=dtype)
    xs = torch.linspace(-1.0, 1.0, steps=int(W), device=device, dtype=dtype)
    yv = ys[:, None].expand(int(H), int(W))
    xv = xs[None, :].expand(int(H), int(W))
    return torch.stack([xv, yv], dim=0).unsqueeze(0)


def _add_xy(x: torch.Tensor) -> torch.Tensor:
    B, C, H, W = x.shape
    if int(C) != 1:
        raise ValueError(f"_add_xy expects C==1, got shape={tuple(x.shape)}")
    xy = _xy_grid(H=H, W=W, device=x.device, dtype=x.dtype).expand(int(B), 2, int(H), int(W))
    return torch.cat([x, xy], dim=1)


def _overlap_score(pred_logits: torch.Tensor, true_mask: torch.Tensor) -> torch.Tensor:
    return (torch.sigmoid(pred_logits) * true_mask).sum(dim=(1, 2, 3))


def _center_of_mass(mask01: torch.Tensor) -> torch.Tensor:
    B, C, H, W = mask01.shape
    if int(C) != 1:
        raise ValueError(f"_center_of_mass expects (B,1,H,W), got {tuple(mask01.shape)}")
    xy = _xy_grid(H=H, W=W, device=mask01.device, dtype=mask01.dtype)  # (1,2,H,W)
    w = mask01
    mass = w.sum(dim=(1, 2, 3), keepdim=True).clamp_min(1e-6)  # (B,1,1,1)
    cx = (w * xy[:, 0:1]).sum(dim=(1, 2, 3), keepdim=True) / mass
    cy = (w * xy[:, 1:2]).sum(dim=(1, 2, 3), keepdim=True) / mass
    return torch.cat([cx, cy], dim=1).squeeze(-1).squeeze(-1)  # (B,2)


def _min_occ_half_for_n(*, n_classes: int, ood: bool) -> int:
    n = int(n_classes)
    if ood:
        return int((n + 9) // 2)  # ceil((n+8)/2)
    return int((n + 7) // 2)  # ceil((n+6)/2)


def _sample_ctxs(*, n: int, seed: int, ood: bool, img_size: int, n_classes: int) -> list[Ctx]:
    g = torch.Generator()
    g.manual_seed(int(seed))

    cx = torch.randint(low=12, high=21, size=(n,), generator=g).tolist()
    cy = torch.randint(low=12, high=21, size=(n,), generator=g).tolist()
    if ood:
        t = torch.randint(low=2, high=5, size=(n,), generator=g).tolist()
    else:
        t = torch.randint(low=2, high=4, size=(n,), generator=g).tolist()

    min_occ = _min_occ_half_for_n(n_classes=int(n_classes), ood=bool(ood))
    if min_occ > 10:
        raise ValueError(f"n_classes={int(n_classes)} too large for occ_half<=10 under img_size={int(img_size)} (min_occ={min_occ})")
    hi = min(11, min_occ + (3 if ood else 2))
    occ_half = torch.randint(low=min_occ, high=hi, size=(n,), generator=g).tolist()

    out: list[Ctx] = []
    for i in range(n):
        out.append(Ctx(cx=int(cx[i]), cy=int(cy[i]), t=int(t[i]), occ_half=int(occ_half[i]), img_size=int(img_size), ood=bool(ood), seed=int(seed + i)))
    return out


def _make_dataloaders(*, batch_size: int, steps: int, train_ood_ratio: float, n_classes: int, seed: int) -> tuple[DataLoader, DataLoader, DataLoader]:
    batch_size = int(batch_size)
    steps = int(steps)
    train_ood_ratio = float(train_ood_ratio)
    train_ood_ratio = max(0.0, min(1.0, train_ood_ratio))

    n_train = batch_size * steps
    n_ood = int(round(n_train * train_ood_ratio))
    n_iid = int(n_train - n_ood)

    iid_ds = V9UnifiedDoubleBarrierMinLiftDatasetNScalable(size=1024, n_classes=n_classes, ood=False, seed=seed + 10_000)
    ood_ds = V9UnifiedDoubleBarrierMinLiftDatasetNScalable(size=1024, n_classes=n_classes, ood=True, seed=seed + 20_000)
    train_iid = V9UnifiedDoubleBarrierMinLiftDatasetNScalable(size=n_iid, n_classes=n_classes, ood=False, seed=seed + 30_000)
    train_ood = V9UnifiedDoubleBarrierMinLiftDatasetNScalable(size=n_ood, n_classes=n_classes, ood=True, seed=seed + 40_000)
    train_ds = torch.utils.data.ConcatDataset([train_iid, train_ood])

    train_dl = DataLoader(train_ds, batch_size=batch_size, shuffle=True)
    iid_dl = DataLoader(iid_ds, batch_size=256, shuffle=False)
    ood_dl = DataLoader(ood_ds, batch_size=256, shuffle=False)
    return train_dl, iid_dl, ood_dl


def _dump_image_barrier_fails(
    *,
    modelA: V9MinLiftModelA,
    device: torch.device,
    n_classes: int,
    z_classes: int,
    seed: int,
    n_ctx: int,
    ood: bool,
    out_jsonl: Path,
    out_tensor_dir: Path,
    max_fails: int,
    save_tensors_max: int,
) -> dict:
    n_classes = int(n_classes)
    z_classes = int(z_classes)
    assert z_classes >= 1

    ctxs = _sample_ctxs(n=int(n_ctx), seed=int(seed), ood=bool(ood), img_size=32, n_classes=int(n_classes))
    h_pairs: list[tuple[int, int]] = []
    for i in range(n_classes):
        for j in range(i + 1, n_classes):
            h_pairs.append((i, j))

    n_fail = 0
    n_fail_z_wrong = 0
    n_fail_z_right = 0

    margins = []
    saved = 0

    with open(out_jsonl, "a", encoding="utf-8") as f:
        for i, ctx in enumerate(ctxs):
            h0, h1 = h_pairs[i % len(h_pairs)]
            k_fixed = int((ctx.seed + 0) % 2)

            x_im0 = render(ctx, h=h0, k=k_fixed, n_classes=n_classes)
            x_im1 = render(ctx, h=h1, k=k_fixed, n_classes=n_classes)

            cue_im0 = _add_xy(x_im0["cue_image"].unsqueeze(0).to(device))
            cue_im1 = _add_xy(x_im1["cue_image"].unsqueeze(0).to(device))
            image_fixed = _add_xy(x_im0["image"].unsqueeze(0).to(device))
            t_im0 = x_im0["hidden_target"].unsqueeze(0).to(device)
            t_im1 = x_im1["hidden_target"].unsqueeze(0).to(device)

            with torch.no_grad():
                p0 = modelA(cue_im0, image_fixed)
                p1 = modelA(cue_im1, image_fixed)

                s00 = _overlap_score(p0, t_im0)
                s01 = _overlap_score(p0, t_im1)
                s11 = _overlap_score(p1, t_im1)
                s10 = _overlap_score(p1, t_im0)
                m0 = float((s00 - s01).item())
                m1 = float((s11 - s10).item())

                ok0 = bool(m0 > 0.0)
                ok1 = bool(m1 > 0.0)

                # z-hats + cue conf
                z0_logits = modelA.z_logits(cue_im0)
                z1_logits = modelA.z_logits(cue_im1)
                z0_hat = int(torch.argmax(z0_logits, dim=-1).item())
                z1_hat = int(torch.argmax(z1_logits, dim=-1).item())
                z0_prob = float(F.softmax(z0_logits, dim=-1).max(dim=-1).values.item())
                z1_prob = float(F.softmax(z1_logits, dim=-1).max(dim=-1).values.item())

                marker0 = modelA.cue_to_xy(cue_im0).squeeze(0)
                marker1 = modelA.cue_to_xy(cue_im1).squeeze(0)

                k_hat = int(V9MinLiftModelA.k_hat_from_image(image_fixed).item())

                pred0_xy = _center_of_mass(torch.sigmoid(p0).clamp(0.0, 1.0)).squeeze(0)
                pred1_xy = _center_of_mass(torch.sigmoid(p1).clamp(0.0, 1.0)).squeeze(0)
                true0_xy = _center_of_mass(t_im0).squeeze(0)
                true1_xy = _center_of_mass(t_im1).squeeze(0)

            if ok0 and ok1:
                continue

            n_fail += 1
            margins.append((m0, m1))

            z0_tgt = int(h0 % z_classes)
            z1_tgt = int(h1 % z_classes)
            z_wrong = (z0_hat != z0_tgt) or (z1_hat != z1_tgt)
            if z_wrong:
                n_fail_z_wrong += 1
            else:
                n_fail_z_right += 1

            rec = {
                "kind": "aslmt_v9_unified_faildump_image_barrier",
                "ood": bool(ood),
                "seed": int(seed),
                "i": int(i),
                "ctx": asdict(ctx),
                "pair": {"h0": int(h0), "h1": int(h1), "k_fixed": int(k_fixed), "k_hat": int(k_hat)},
                "z": {
                    "z_classes": int(z_classes),
                    "z0_hat": int(z0_hat),
                    "z1_hat": int(z1_hat),
                    "z0_tgt": int(z0_tgt),
                    "z1_tgt": int(z1_tgt),
                    "z0_prob": float(z0_prob),
                    "z1_prob": float(z1_prob),
                    "marker0": {"x": float(marker0[0].item()), "y": float(marker0[1].item()), "conf": float(marker0[2].item())},
                    "marker1": {"x": float(marker1[0].item()), "y": float(marker1[1].item()), "conf": float(marker1[2].item())},
                },
                "scores": {
                    "m0": float(m0),
                    "m1": float(m1),
                    "ok0": bool(ok0),
                    "ok1": bool(ok1),
                },
                "centroids": {
                    "pred0_xy": [float(pred0_xy[0].item()), float(pred0_xy[1].item())],
                    "pred1_xy": [float(pred1_xy[0].item()), float(pred1_xy[1].item())],
                    "true0_xy": [float(true0_xy[0].item()), float(true0_xy[1].item())],
                    "true1_xy": [float(true1_xy[0].item()), float(true1_xy[1].item())],
                },
            }

            tensor_path = ""
            if saved < int(save_tensors_max):
                tensor_path = str(out_tensor_dir / f"fail_tensors_{'ood' if ood else 'iid'}_{i:04d}.pt")
                torch.save(
                    {
                        "ctx": asdict(ctx),
                        "h0": int(h0),
                        "h1": int(h1),
                        "k_fixed": int(k_fixed),
                        "x_im0": x_im0,
                        "x_im1": x_im1,
                        "cue_im0": cue_im0.detach().cpu(),
                        "cue_im1": cue_im1.detach().cpu(),
                        "image_fixed": image_fixed.detach().cpu(),
                        "t_im0": t_im0.detach().cpu(),
                        "t_im1": t_im1.detach().cpu(),
                        "p0_logits": p0.detach().cpu(),
                        "p1_logits": p1.detach().cpu(),
                    },
                    tensor_path,
                )
                saved += 1
            rec["tensors_pt"] = tensor_path

            f.write(json.dumps(_jsonable(rec)) + "\n")
            if n_fail >= int(max_fails):
                break

    # summarize margins
    m0s = [m[0] for m in margins]
    m1s = [m[1] for m in margins]
    return {
        "n_ctx": int(n_ctx),
        "n_fails": int(n_fail),
        "n_fails_z_wrong": int(n_fail_z_wrong),
        "n_fails_z_right": int(n_fail_z_right),
        "m0_min": float(min(m0s)) if m0s else None,
        "m1_min": float(min(m1s)) if m1s else None,
        "saved_tensors": int(saved),
        "out_jsonl": str(out_jsonl),
        "out_tensor_dir": str(out_tensor_dir),
    }


def _freeze_and_exec_if_needed() -> None:
    if str(os.environ.get("ASLMT_FROZEN", "")) == "1":
        return

    p = argparse.ArgumentParser(add_help=False)
    p.add_argument("--out-dir", type=str, default="")
    ns, _ = p.parse_known_args()

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    script_path = Path(__file__).resolve()
    script_sha = _sha256_file(script_path)
    suf = f"{ts}_{script_sha[:12]}"

    SNAP_DIR.mkdir(parents=True, exist_ok=True)
    snap_root = SNAP_DIR / f"aslmt_diag_v9_unified_faildump_kdet_{suf}"
    snap_root.mkdir(parents=True, exist_ok=False)

    # Snapshot all local dependencies needed to reproduce the exact diagnostic.
    dep_names = [
        script_path.name,
        "aslmt_env_v9_unified_double_barrier_minlift_nscalable.py",
        "aslmt_model_v9_unified_double_barrier_minlift_kdet.py",
        "render_v9_unified_paired_ctx_nscalable.py",
    ]
    src_dir = script_path.parent
    src_files: list[Path] = []
    for name in dep_names:
        pth = (src_dir / name).resolve()
        if not pth.exists():
            raise SystemExit(f"missing dependency for snapshot: {pth}")
        src_files.append(pth)

    for pth in src_files:
        (snap_root / pth.name).write_text(pth.read_text(encoding="utf-8"), encoding="utf-8")

    snap_script = snap_root / script_path.name
    (snap_root / "snapshot_manifest.json").write_text(
        json.dumps(
            {
                "kind": "aslmt_diag_v9_unified_faildump_kdet_snapshot",
                "ts": ts,
                "snapshot_dir": str(snap_root),
                "files": [{"name": p.name, "sha256": _sha256_file(p)} for p in src_files],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )

    if str(ns.out_dir).strip():
        out_dir = Path(str(ns.out_dir)).expanduser().resolve()
    else:
        out_dir = RUNS_DIR / f"aslmt_diag_v9_unified_faildump_kdet_{suf}"
    out_dir.mkdir(parents=True, exist_ok=False)

    cmd = [sys.executable, "-u", str(snap_script)]
    argv = sys.argv[1:]
    if "--out-dir" not in argv:
        argv = argv + ["--out-dir", str(out_dir)]
    cmd += argv

    env = dict(os.environ)
    env["ASLMT_FROZEN"] = "1"
    env["ASLMT_SNAPSHOT_DIR"] = str(snap_root)
    raise SystemExit(subprocess.call(cmd, env=env))


def main() -> None:
    _freeze_and_exec_if_needed()

    p = argparse.ArgumentParser()
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--steps", type=int, default=9000)
    p.add_argument("--batch-size", type=int, default=128)
    p.add_argument("--lr", type=float, default=1e-3)
    p.add_argument("--w-z", type=float, default=5.0)
    p.add_argument("--w-k", type=float, default=0.0)
    p.add_argument("--w-pos", type=float, default=0.25)
    p.add_argument("--w-rank-img", type=float, default=0.25)
    p.add_argument("--rank-n-ctx", type=int, default=8)
    p.add_argument("--rank-ood-ratio", type=float, default=0.5)
    p.add_argument("--train-ood-ratio", type=float, default=0.5)
    p.add_argument("--pair-n-ctx", type=int, default=64)
    p.add_argument("--log-every", type=int, default=250)
    p.add_argument("--n-classes", type=int, required=True)
    p.add_argument("--z-classes", type=int, required=True)
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--dump-split", type=str, default="ood", choices=["iid", "ood", "both"])
    p.add_argument("--max-fails", type=int, default=200)
    p.add_argument("--save-tensors-max", type=int, default=20)
    p.add_argument("--out-dir", type=str, required=True)
    args = p.parse_args()

    out_dir = Path(str(args.out_dir)).expanduser().resolve()
    if not out_dir.exists():
        raise SystemExit(f"--out-dir does not exist: {out_dir}")

    script_path = Path(__file__).resolve()
    script_sha = _sha256_file(script_path)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    suf = f"{ts}_{script_sha[:12]}"

    console_txt = out_dir / f"diag_console_{suf}.txt"
    manifest_json = out_dir / f"diag_manifest_{suf}.json"
    fail_jsonl = out_dir / f"diag_faildump_{suf}.jsonl"
    tensor_dir = out_dir / f"diag_fail_tensors_{suf}"
    tensor_dir.mkdir(parents=True, exist_ok=False)
    ckpt_pt = out_dir / f"diag_modelA_state_{suf}.pt"

    cmd_str = " ".join([os.path.basename(__file__)] + [str(a) for a in sys.argv[1:]])
    snapshot_dir = str(os.environ.get("ASLMT_SNAPSHOT_DIR", ""))

    with open(console_txt, "w", encoding="utf-8") as f:
        f.write(f"CMD: {cmd_str}\n")
        f.write(f"SCRIPT_SHA256: {script_sha}\n")
        if snapshot_dir:
            f.write(f"SNAPSHOT_DIR: {snapshot_dir}\n")

    device = torch.device(str(args.device))
    n_classes = int(args.n_classes)
    z_classes = int(args.z_classes)

    modelA = V9MinLiftModelA(z_classes=z_classes).to(device)
    modelB_img = V9ImageOnlyBaseline().to(device)
    modelB_cue = V9CueOnlyBaseline().to(device)
    opt = torch.optim.Adam(list(modelA.parameters()) + list(modelB_img.parameters()) + list(modelB_cue.parameters()), lr=float(args.lr))

    steps = int(args.steps)
    train_dl, iid_dl, ood_dl = _make_dataloaders(batch_size=int(args.batch_size), steps=steps, train_ood_ratio=float(args.train_ood_ratio), n_classes=n_classes, seed=int(args.seed))
    it = iter(train_dl)

    pos_weight = torch.tensor([10.0], device=device)
    rank_ood_ratio = max(0.0, min(1.0, float(args.rank_ood_ratio)))
    rank_n_ctx = int(args.rank_n_ctx)
    rank_seed_base = int(args.seed) + 123_456

    # training
    for s in range(steps):
        try:
            batch = next(it)
        except StopIteration:
            it = iter(train_dl)
            batch = next(it)

        cue = _add_xy(batch["cue_image"].to(device))
        image = _add_xy(batch["image"].to(device))
        tgt = batch["hidden_target"].to(device)
        h = batch["h"].to(device)

        pA = modelA(cue, image)
        pB_img = modelB_img(image)
        pB_cue = modelB_cue(cue)

        lossA_seg = F.binary_cross_entropy_with_logits(pA, tgt, pos_weight=pos_weight)
        z_logits = modelA.z_logits(cue)
        lossA_z = F.cross_entropy(z_logits, h.remainder(int(modelA.z_classes)))

        pred_mass = torch.sigmoid(pA).clamp(0.0, 1.0)
        pred_xy = _center_of_mass(pred_mass)
        true_xy = _center_of_mass(tgt)
        lossA_pos = F.mse_loss(pred_xy, true_xy)

        rank_ood = (torch.rand(()) < rank_ood_ratio).item()
        lossA_rank = torch.tensor(0.0, device=device)
        if float(args.w_rank_img) != 0.0 and rank_n_ctx > 0:
            ctxs = _sample_ctxs(n=int(rank_n_ctx), seed=rank_seed_base + s, ood=bool(rank_ood), img_size=32, n_classes=n_classes)
            g = torch.Generator()
            g.manual_seed(int(rank_seed_base + s) + (10_000 if rank_ood else 0))
            loss_terms: list[torch.Tensor] = []
            for ctx in ctxs:
                h0 = int(torch.randint(low=0, high=int(n_classes), size=(1,), generator=g).item())
                h1 = int(torch.randint(low=0, high=int(n_classes - 1), size=(1,), generator=g).item())
                if h1 >= h0:
                    h1 += 1
                k_fixed = int(torch.randint(low=0, high=2, size=(1,), generator=g).item())
                x0 = render(ctx, h=h0, k=k_fixed, n_classes=int(n_classes))
                x1 = render(ctx, h=h1, k=k_fixed, n_classes=int(n_classes))
                cue0 = _add_xy(x0["cue_image"].unsqueeze(0).to(device))
                cue1 = _add_xy(x1["cue_image"].unsqueeze(0).to(device))
                image_fixed = _add_xy(x0["image"].unsqueeze(0).to(device))
                t0 = x0["hidden_target"].unsqueeze(0).to(device)
                t1 = x1["hidden_target"].unsqueeze(0).to(device)
                p0 = modelA(cue0, image_fixed)
                p1 = modelA(cue1, image_fixed)
                s00 = _overlap_score(p0, t0)
                s01 = _overlap_score(p0, t1)
                s11 = _overlap_score(p1, t1)
                s10 = _overlap_score(p1, t0)
                loss_terms.append(F.softplus(-(s00 - s01)))
                loss_terms.append(F.softplus(-(s11 - s10)))
            if loss_terms:
                lossA_rank = torch.stack(loss_terms, dim=0).mean()

        lossA = lossA_seg + float(args.w_z) * lossA_z + float(args.w_pos) * lossA_pos + float(args.w_rank_img) * lossA_rank
        lossB_img = F.binary_cross_entropy_with_logits(pB_img, tgt, pos_weight=pos_weight)
        lossB_cue = F.binary_cross_entropy_with_logits(pB_cue, tgt, pos_weight=pos_weight)
        loss = lossA + lossB_img + lossB_cue

        opt.zero_grad(set_to_none=True)
        loss.backward()
        opt.step()

        if (s + 1) % int(args.log_every) == 0:
            print(
                f"step={s+1}/{steps} loss={float(loss.item()):.6f} "
                f"(A_seg={float(lossA_seg.item()):.6f}, A_z={float(lossA_z.item()):.6f}, "
                f"A_pos={float(lossA_pos.item()):.6f}, A_rank_img={float(lossA_rank.item()):.6f}, "
                f"Bimg={float(lossB_img.item()):.6f}, Bcue={float(lossB_cue.item()):.6f})"
            )

    torch.save({"state_dict": modelA.state_dict(), "n_classes": n_classes, "z_classes": z_classes, "seed": int(args.seed)}, ckpt_pt)

    def eval_z_acc(dl: DataLoader) -> float:
        for b in dl:
            cue = _add_xy(b["cue_image"].to(device))
            h = b["h"].to(device)
            with torch.no_grad():
                z_logits = modelA.z_logits(cue)
                pred = torch.argmax(z_logits, dim=-1)
                tgt = h.remainder(int(modelA.z_classes))
                return float((pred == tgt).float().mean().item())
        raise RuntimeError("empty dataloader")

    iid_z_acc = eval_z_acc(iid_dl)
    ood_z_acc = eval_z_acc(ood_dl)

    dump = {}
    if str(args.dump_split) in ("iid", "both"):
        dump["iid"] = _dump_image_barrier_fails(
            modelA=modelA,
            device=device,
            n_classes=n_classes,
            z_classes=z_classes,
            seed=int(args.seed),
            n_ctx=int(args.pair_n_ctx),
            ood=False,
            out_jsonl=fail_jsonl,
            out_tensor_dir=tensor_dir,
            max_fails=int(args.max_fails),
            save_tensors_max=int(args.save_tensors_max),
        )
    if str(args.dump_split) in ("ood", "both"):
        dump["ood"] = _dump_image_barrier_fails(
            modelA=modelA,
            device=device,
            n_classes=n_classes,
            z_classes=z_classes,
            seed=int(args.seed),
            n_ctx=int(args.pair_n_ctx),
            ood=True,
            out_jsonl=fail_jsonl,
            out_tensor_dir=tensor_dir,
            max_fails=int(args.max_fails),
            save_tensors_max=int(args.save_tensors_max),
        )

    manifest = {
        "kind": "aslmt_diag_v9_unified_faildump_kdet",
        "timestamp": ts,
        "script": {"path": str(script_path), "sha256": script_sha},
        "snapshot_dir": snapshot_dir,
        "cmd": cmd_str,
        "args": vars(args),
        "outputs": {
            "console_txt": str(console_txt),
            "manifest_json": str(manifest_json),
            "faildump_jsonl": str(fail_jsonl),
            "tensors_dir": str(tensor_dir),
            "modelA_state_pt": str(ckpt_pt),
        },
        "z_acc": {"iid": float(iid_z_acc), "ood": float(ood_z_acc)},
        "dump_summary": dump,
    }
    with open(manifest_json, "w", encoding="utf-8") as f:
        f.write(json.dumps(_jsonable(manifest), indent=2) + "\n")

    print(json.dumps(_jsonable(manifest), indent=2))


if __name__ == "__main__":
    main()
