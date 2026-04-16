import argparse
import json
import random
from dataclasses import dataclass

import torch
import torch.nn.functional as F
from torch.utils.data import DataLoader

from aslmt_env_v9_unified_double_barrier_minlift_nscalable import V9UnifiedDoubleBarrierMinLiftDatasetNScalable
from aslmt_model_v9_unified_double_barrier_minlift_kdet import V9CueOnlyBaseline, V9ImageOnlyBaseline, V9MinLiftModelA
from render_v9_unified_paired_ctx_nscalable import Ctx, render


def _seed_everything(seed: int) -> None:
    seed = int(seed)
    random.seed(seed)
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)


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


def _calculate_iou(pred_logits: torch.Tensor, true_mask: torch.Tensor) -> float:
    pred_bin = (torch.sigmoid(pred_logits) > 0.5).float()
    intersection = (pred_bin * true_mask).sum(dim=(1, 2, 3))
    union = (pred_bin + true_mask).clamp(0, 1).sum(dim=(1, 2, 3))
    return float((intersection / (union + 1e-6)).mean().item())


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


@dataclass(frozen=True)
class PairEvalCfg:
    n_ctx: int = 64
    seed: int = 0
    img_size: int = 32


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


def _img_pair_rank_loss(
    *,
    modelA: V9MinLiftModelA,
    device: torch.device,
    n_classes: int,
    n_ctx: int,
    seed: int,
    ood: bool,
) -> torch.Tensor:
    """
    Explicit pair-grade ranking loss for the image-barrier:
    same visible image, two different hidden targets. We enforce that, for each
    cue (i.e. each h), the predicted overlap with its own target beats the other.
    """
    ctxs = _sample_ctxs(n=int(n_ctx), seed=int(seed), ood=bool(ood), img_size=32, n_classes=int(n_classes))
    g = torch.Generator()
    g.manual_seed(int(seed) + (10_000 if ood else 0))

    loss_terms: list[torch.Tensor] = []
    for i, ctx in enumerate(ctxs):
        h0 = int(torch.randint(low=0, high=int(n_classes), size=(1,), generator=g).item())
        h1 = int(torch.randint(low=0, high=int(n_classes - 1), size=(1,), generator=g).item())
        if h1 >= h0:
            h1 += 1

        k_fixed = int(torch.randint(low=0, high=2, size=(1,), generator=g).item())

        x0 = render(ctx, h=h0, k=k_fixed, n_classes=int(n_classes))
        x1 = render(ctx, h=h1, k=k_fixed, n_classes=int(n_classes))

        cue0 = _add_xy(x0["cue_image"].unsqueeze(0).to(device))
        cue1 = _add_xy(x1["cue_image"].unsqueeze(0).to(device))
        image = _add_xy(x0["image"].unsqueeze(0).to(device))
        t0 = x0["hidden_target"].unsqueeze(0).to(device)
        t1 = x1["hidden_target"].unsqueeze(0).to(device)

        p0 = modelA(cue0, image)
        p1 = modelA(cue1, image)

        s00 = _overlap_score(p0, t0)
        s01 = _overlap_score(p0, t1)
        s11 = _overlap_score(p1, t1)
        s10 = _overlap_score(p1, t0)

        # want s00 > s01 and s11 > s10
        loss_terms.append(F.softplus(-(s00 - s01)))
        loss_terms.append(F.softplus(-(s11 - s10)))

    if not loss_terms:
        return torch.tensor(0.0, device=device)
    return torch.stack(loss_terms, dim=0).mean()


def _pair_eval_one(
    *,
    modelA: V9MinLiftModelA,
    modelB_img: V9ImageOnlyBaseline,
    modelB_cue: V9CueOnlyBaseline,
    device: torch.device,
    cfg: PairEvalCfg,
    ood: bool,
    n_classes: int,
) -> dict:
    n_classes = int(n_classes)
    ctxs = _sample_ctxs(n=int(cfg.n_ctx), seed=int(cfg.seed), ood=bool(ood), img_size=int(cfg.img_size), n_classes=int(n_classes))

    obs_image_barrier_ok = True
    obs_cue_barrier_ok = True

    A_both_image = 0
    A_both_cue = 0
    B_img_both = 0
    B_cue_both = 0

    A_abl_both_image = 0
    A_swap_follow_image = 0
    A_swap_orig_both_image = 0

    h_pairs = []
    for i in range(n_classes):
        for j in range(i + 1, n_classes):
            h_pairs.append((i, j))

    for i, ctx in enumerate(ctxs):
        h0, h1 = h_pairs[i % len(h_pairs)]

        k_fixed = int((ctx.seed + 0) % 2)
        h_fixed = int((ctx.seed + 1) % n_classes)
        k0, k1 = 0, 1

        x_im0 = render(ctx, h=h0, k=k_fixed, n_classes=n_classes)
        x_im1 = render(ctx, h=h1, k=k_fixed, n_classes=n_classes)
        obs_image_barrier_ok = bool(obs_image_barrier_ok and torch.equal(x_im0["image"], x_im1["image"]) and (not torch.equal(x_im0["hidden_target"], x_im1["hidden_target"])))

        x_cu0 = render(ctx, h=h_fixed, k=k0, n_classes=n_classes)
        x_cu1 = render(ctx, h=h_fixed, k=k1, n_classes=n_classes)
        obs_cue_barrier_ok = bool(obs_cue_barrier_ok and torch.equal(x_cu0["cue_image"], x_cu1["cue_image"]) and (not torch.equal(x_cu0["hidden_target"], x_cu1["hidden_target"])))

        cue_im0 = _add_xy(x_im0["cue_image"].unsqueeze(0).to(device))
        cue_im1 = _add_xy(x_im1["cue_image"].unsqueeze(0).to(device))
        image_fixed = _add_xy(x_im0["image"].unsqueeze(0).to(device))
        t_im0 = x_im0["hidden_target"].unsqueeze(0).to(device)
        t_im1 = x_im1["hidden_target"].unsqueeze(0).to(device)

        cue_fixed = _add_xy(x_cu0["cue_image"].unsqueeze(0).to(device))
        image_cu0 = _add_xy(x_cu0["image"].unsqueeze(0).to(device))
        image_cu1 = _add_xy(x_cu1["image"].unsqueeze(0).to(device))
        t_cu0 = x_cu0["hidden_target"].unsqueeze(0).to(device)
        t_cu1 = x_cu1["hidden_target"].unsqueeze(0).to(device)

        with torch.no_grad():
            pA_im0 = modelA(cue_im0, image_fixed)
            pA_im1 = modelA(cue_im1, image_fixed)
            pA_cu0 = modelA(cue_fixed, image_cu0)
            pA_cu1 = modelA(cue_fixed, image_cu1)

            pB_img = modelB_img(image_fixed)
            pB_cue = modelB_cue(cue_fixed)

            pA_im0_abl = modelA.ablated_forward(cue_im0, image_fixed)
            pA_im1_abl = modelA.ablated_forward(cue_im1, image_fixed)

            cue_pair = torch.cat([cue_im0, cue_im1], dim=0)
            img_pair = torch.cat([image_fixed, image_fixed], dim=0)
            perm = torch.tensor([1, 0], device=device, dtype=torch.long)
            pA_pair_swap = modelA.swap_forward(cue_pair, img_pair, perm=perm)
            pA_im0_swap = pA_pair_swap[0:1]
            pA_im1_swap = pA_pair_swap[1:2]

        A_im0_correct = bool(_overlap_score(pA_im0, t_im0) > _overlap_score(pA_im0, t_im1))
        A_im1_correct = bool(_overlap_score(pA_im1, t_im1) > _overlap_score(pA_im1, t_im0))
        if A_im0_correct and A_im1_correct:
            A_both_image += 1

        A_cu0_correct = bool(_overlap_score(pA_cu0, t_cu0) > _overlap_score(pA_cu0, t_cu1))
        A_cu1_correct = bool(_overlap_score(pA_cu1, t_cu1) > _overlap_score(pA_cu1, t_cu0))
        if A_cu0_correct and A_cu1_correct:
            A_both_cue += 1

        B_im0_correct = bool(_overlap_score(pB_img, t_im0) > _overlap_score(pB_img, t_im1))
        B_im1_correct = bool(_overlap_score(pB_img, t_im1) > _overlap_score(pB_img, t_im0))
        if B_im0_correct and B_im1_correct:
            B_img_both += 1

        B_cu0_correct = bool(_overlap_score(pB_cue, t_cu0) > _overlap_score(pB_cue, t_cu1))
        B_cu1_correct = bool(_overlap_score(pB_cue, t_cu1) > _overlap_score(pB_cue, t_cu0))
        if B_cu0_correct and B_cu1_correct:
            B_cue_both += 1

        A_im0_abl_correct = bool(_overlap_score(pA_im0_abl, t_im0) > _overlap_score(pA_im0_abl, t_im1))
        A_im1_abl_correct = bool(_overlap_score(pA_im1_abl, t_im1) > _overlap_score(pA_im1_abl, t_im0))
        if A_im0_abl_correct and A_im1_abl_correct:
            A_abl_both_image += 1

        A_im0_swap_follows = bool(_overlap_score(pA_im0_swap, t_im1) > _overlap_score(pA_im0_swap, t_im0))
        A_im1_swap_follows = bool(_overlap_score(pA_im1_swap, t_im0) > _overlap_score(pA_im1_swap, t_im1))
        if A_im0_swap_follows and A_im1_swap_follows:
            A_swap_follow_image += 1

        A_im0_swap_orig = bool(_overlap_score(pA_im0_swap, t_im0) > _overlap_score(pA_im0_swap, t_im1))
        A_im1_swap_orig = bool(_overlap_score(pA_im1_swap, t_im1) > _overlap_score(pA_im1_swap, t_im0))
        if A_im0_swap_orig and A_im1_swap_orig:
            A_swap_orig_both_image += 1

    n = int(cfg.n_ctx)
    return {
        "n_ctx": n,
        "ood": bool(ood),
        "obs_image_barrier_ok": bool(obs_image_barrier_ok),
        "obs_cue_barrier_ok": bool(obs_cue_barrier_ok),
        "A_both_image_pair_rate": float(A_both_image) / float(n),
        "A_both_cue_pair_rate": float(A_both_cue) / float(n),
        "B_image_only_both_rate": float(B_img_both) / float(n),
        "B_cue_only_both_rate": float(B_cue_both) / float(n),
        "A_ablated_both_image_pair_rate": float(A_abl_both_image) / float(n),
        "A_swap_follow_image_pair_rate": float(A_swap_follow_image) / float(n),
        "A_swap_orig_both_image_pair_rate": float(A_swap_orig_both_image) / float(n),
        "seed": int(cfg.seed),
    }


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


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--steps", type=int, default=3000)
    p.add_argument("--batch-size", type=int, default=128)
    p.add_argument("--lr", type=float, default=1e-3)
    p.add_argument("--w-z", type=float, default=5.0)
    p.add_argument("--w-k", type=float, default=1.0)
    p.add_argument("--w-pos", type=float, default=0.25)
    p.add_argument("--w-rank-img", type=float, default=0.25)
    p.add_argument("--rank-n-ctx", type=int, default=8)
    p.add_argument("--rank-ood-ratio", type=float, default=0.5)
    p.add_argument("--train-ood-ratio", type=float, default=0.5)
    p.add_argument("--pair-n-ctx", type=int, default=64)
    p.add_argument("--log-every", type=int, default=250)
    p.add_argument("--n-classes", type=int, default=4)
    p.add_argument("--z-classes", type=int, default=4)
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--out-jsonl", type=str, required=True)
    args = p.parse_args()

    _seed_everything(int(args.seed))
    device = torch.device(str(args.device))

    n_classes = int(args.n_classes)
    modelA = V9MinLiftModelA(z_classes=int(args.z_classes)).to(device)
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
        k = batch["k"].to(device)

        pA = modelA(cue, image)
        pB_img = modelB_img(image)
        pB_cue = modelB_cue(cue)

        lossA_seg = F.binary_cross_entropy_with_logits(pA, tgt, pos_weight=pos_weight)
        z_logits = modelA.z_logits(cue)
        lossA_z = F.cross_entropy(z_logits, h.remainder(int(modelA.z_classes)))
        # k is visible; k_hat is extracted deterministically and injected in the decoder.
        # We still audit it here.
        k_hat = V9MinLiftModelA.k_hat_from_image(image)
        lossA_k = torch.tensor(0.0, device=device)

        pred_mass = torch.sigmoid(pA).clamp(0.0, 1.0)
        pred_xy = _center_of_mass(pred_mass)
        true_xy = _center_of_mass(tgt)
        lossA_pos = F.mse_loss(pred_xy, true_xy)

        if random.random() < rank_ood_ratio:
            rank_ood = True
        else:
            rank_ood = False
        lossA_rank = _img_pair_rank_loss(
            modelA=modelA,
            device=device,
            n_classes=n_classes,
            n_ctx=rank_n_ctx,
            seed=rank_seed_base + s,
            ood=rank_ood,
        )

        lossA = (
            lossA_seg
            + float(args.w_z) * lossA_z
            + float(args.w_k) * lossA_k
            + float(args.w_pos) * lossA_pos
            + float(args.w_rank_img) * lossA_rank
        )

        lossB_img = F.binary_cross_entropy_with_logits(pB_img, tgt, pos_weight=pos_weight)
        lossB_cue = F.binary_cross_entropy_with_logits(pB_cue, tgt, pos_weight=pos_weight)
        loss = lossA + lossB_img + lossB_cue

        opt.zero_grad(set_to_none=True)
        loss.backward()
        opt.step()

        if (s + 1) % int(args.log_every) == 0:
            print(
                f"step={s+1}/{steps} loss={float(loss.item()):.6f} "
                f"(A_seg={float(lossA_seg.item()):.6f}, A_z={float(lossA_z.item()):.6f}, A_k={float(lossA_k.item()):.6f}, "
                f"A_pos={float(lossA_pos.item()):.6f}, A_rank_img={float(lossA_rank.item()):.6f}, "
                f"Bimg={float(lossB_img.item()):.6f}, Bcue={float(lossB_cue.item()):.6f})"
            )

    def eval_iou(dl: DataLoader):
        for b in dl:
            cue = _add_xy(b["cue_image"].to(device))
            image = _add_xy(b["image"].to(device))
            tgt = b["hidden_target"].to(device)
            with torch.no_grad():
                pA = modelA(cue, image)
                pB_img = modelB_img(image)
                pB_cue = modelB_cue(cue)
                return _calculate_iou(pA, tgt), _calculate_iou(pB_img, tgt), _calculate_iou(pB_cue, tgt)
        raise RuntimeError("empty dataloader")

    def eval_z_acc(dl: DataLoader):
        for b in dl:
            cue = _add_xy(b["cue_image"].to(device))
            h = b["h"].to(device)
            with torch.no_grad():
                z_logits = modelA.z_logits(cue)
                pred = torch.argmax(z_logits, dim=-1)
                tgt = h.remainder(int(modelA.z_classes))
                return float((pred == tgt).float().mean().item())
        raise RuntimeError("empty dataloader")

    def eval_k_acc(dl: DataLoader):
        for b in dl:
            image = _add_xy(b["image"].to(device))
            k = b["k"].to(device)
            with torch.no_grad():
                pred = V9MinLiftModelA.k_hat_from_image(image)
                return float((pred == k).float().mean().item())
        raise RuntimeError("empty dataloader")

    iid_A_iou, iid_Bimg_iou, iid_Bcue_iou = eval_iou(iid_dl)
    ood_A_iou, ood_Bimg_iou, ood_Bcue_iou = eval_iou(ood_dl)
    iid_z_acc = eval_z_acc(iid_dl)
    ood_z_acc = eval_z_acc(ood_dl)
    iid_k_acc = eval_k_acc(iid_dl)
    ood_k_acc = eval_k_acc(ood_dl)

    cfg = PairEvalCfg(n_ctx=int(args.pair_n_ctx), seed=int(args.seed), img_size=32)
    pair_eval = {
        "iid": _pair_eval_one(modelA=modelA, modelB_img=modelB_img, modelB_cue=modelB_cue, device=device, cfg=cfg, ood=False, n_classes=n_classes),
        "ood": _pair_eval_one(modelA=modelA, modelB_img=modelB_img, modelB_cue=modelB_cue, device=device, cfg=cfg, ood=True, n_classes=n_classes),
    }
    payload = {
        "kind": "aslmt_v9_unified_double_barrier_minlift_posloss_pairrank",
        "seed": int(args.seed),
        "n_classes": int(args.n_classes),
        "z_classes": int(args.z_classes),
        "train_ood_ratio": float(args.train_ood_ratio),
        "rank_ood_ratio": float(args.rank_ood_ratio),
        "rank_n_ctx": int(args.rank_n_ctx),
        "w_z": float(args.w_z),
        "w_k": float(args.w_k),
        "w_pos": float(args.w_pos),
        "w_rank_img": float(args.w_rank_img),
        "metrics": {
            "iid": {"A_iou": float(iid_A_iou), "B_img_iou": float(iid_Bimg_iou), "B_cue_iou": float(iid_Bcue_iou), "z_acc": float(iid_z_acc), "k_acc": float(iid_k_acc)},
            "ood": {"A_iou": float(ood_A_iou), "B_img_iou": float(ood_Bimg_iou), "B_cue_iou": float(ood_Bcue_iou), "z_acc": float(ood_z_acc), "k_acc": float(ood_k_acc)},
        },
        "pair_eval": pair_eval,
    }
    print(json.dumps(payload) + "\n")
    with open(str(args.out_jsonl), "a", encoding="utf-8") as f:
        f.write(json.dumps(payload) + "\n")


if __name__ == "__main__":
    main()
