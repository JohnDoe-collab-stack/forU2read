import argparse
import json
import random
from dataclasses import dataclass

import torch
import torch.nn.functional as F
from torch.utils.data import DataLoader

from aslmt_env_v9_unified_double_barrier_minlift_nscalable_spaced2_64 import (
    V9UnifiedDoubleBarrierMinLiftDatasetNScalableSpaced2_64,
)
from aslmt_model_v9_unified_double_barrier_minlift_kdet import V9CueOnlyBaseline, V9ImageOnlyBaseline, V9MinLiftModelA
from render_v9_unified_paired_ctx_nscalable_spaced2_64 import Ctx, POS_STRIDE, render


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
    img_size: int = 64


def _min_occ_half_for_n(*, n_classes: int, ood: bool) -> int:
    n = int(n_classes)
    needed = int(POS_STRIDE) * int(n - 1) + 1
    if ood:
        return int((needed + 9) // 2)
    return int((needed + 7) // 2)


def _sample_ctxs(*, n: int, seed: int, ood: bool, img_size: int, n_classes: int) -> list[Ctx]:
    g = torch.Generator()
    g.manual_seed(int(seed))

    min_occ = _min_occ_half_for_n(n_classes=int(n_classes), ood=bool(ood))
    margin = 4
    max_occ = (int(img_size) // 2) - margin
    if min_occ > max_occ:
        raise ValueError(
            f"img_size={int(img_size)} too small for n_classes={int(n_classes)} "
            f"under stride={int(POS_STRIDE)} (min_occ={int(min_occ)} > max_occ={int(max_occ)})"
        )

    hi_occ = min(max_occ + 1, min_occ + (3 if ood else 2))
    occ_half = torch.randint(low=int(min_occ), high=int(hi_occ), size=(n,), generator=g).tolist()

    cx = []
    cy = []
    for oh in occ_half:
        lo = int(oh) + margin
        hi = int(img_size) - int(oh) - margin
        if hi < lo:
            raise ValueError(f"no valid center range for occ_half={int(oh)} under img_size={int(img_size)}")
        cx.append(int(torch.randint(low=lo, high=hi + 1, size=(1,), generator=g).item()))
        cy.append(int(torch.randint(low=lo, high=hi + 1, size=(1,), generator=g).item()))

    if ood:
        t = torch.randint(low=2, high=5, size=(n,), generator=g).tolist()
    else:
        t = torch.randint(low=2, high=4, size=(n,), generator=g).tolist()

    out: list[Ctx] = []
    for i in range(n):
        out.append(
            Ctx(
                cx=int(cx[i]),
                cy=int(cy[i]),
                t=int(t[i]),
                occ_half=int(occ_half[i]),
                img_size=int(img_size),
                ood=bool(ood),
                seed=int(seed + i),
            )
        )
    return out


def _img_pair_rank_loss(
    *,
    modelA: V9MinLiftModelA,
    device: torch.device,
    n_classes: int,
    n_ctx: int,
    seed: int,
    ood: bool,
    img_size: int,
) -> torch.Tensor:
    ctxs = _sample_ctxs(n=int(n_ctx), seed=int(seed), ood=bool(ood), img_size=int(img_size), n_classes=int(n_classes))
    g = torch.Generator()
    g.manual_seed(int(seed) + (10_000 if ood else 0))

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
        image = _add_xy(x0["image"].unsqueeze(0).to(device))
        t0 = x0["hidden_target"].unsqueeze(0).to(device)
        t1 = x1["hidden_target"].unsqueeze(0).to(device)

        p0 = modelA(cue0, image)
        p1 = modelA(cue1, image)

        s00 = _overlap_score(p0, t0)
        s01 = _overlap_score(p0, t1)
        s11 = _overlap_score(p1, t1)
        s10 = _overlap_score(p1, t0)

        loss_terms.append(F.softplus(-(s00 - s01)))
        loss_terms.append(F.softplus(-(s11 - s10)))

    if not loss_terms:
        return torch.tensor(0.0, device=device)
    return torch.stack(loss_terms, dim=0).mean()


def _cue_pair_rank_loss(
    *,
    modelA: V9MinLiftModelA,
    device: torch.device,
    n_classes: int,
    n_ctx: int,
    seed: int,
    ood: bool,
    img_size: int,
) -> torch.Tensor:
    ctxs = _sample_ctxs(n=int(n_ctx), seed=int(seed), ood=bool(ood), img_size=int(img_size), n_classes=int(n_classes))
    g = torch.Generator()
    g.manual_seed(int(seed) + (20_000 if ood else 0))

    loss_terms: list[torch.Tensor] = []
    for ctx in ctxs:
        h_fixed = int(torch.randint(low=0, high=int(n_classes), size=(1,), generator=g).item())

        x0 = render(ctx, h=h_fixed, k=0, n_classes=int(n_classes))
        x1 = render(ctx, h=h_fixed, k=1, n_classes=int(n_classes))

        cue = _add_xy(x0["cue_image"].unsqueeze(0).to(device))
        img0 = _add_xy(x0["image"].unsqueeze(0).to(device))
        img1 = _add_xy(x1["image"].unsqueeze(0).to(device))
        t0 = x0["hidden_target"].unsqueeze(0).to(device)
        t1 = x1["hidden_target"].unsqueeze(0).to(device)

        p0 = modelA(cue, img0)
        p1 = modelA(cue, img1)

        s00 = _overlap_score(p0, t0)
        s01 = _overlap_score(p0, t1)
        s11 = _overlap_score(p1, t1)
        s10 = _overlap_score(p1, t0)

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
        obs_image_barrier_ok = bool(
            obs_image_barrier_ok and torch.equal(x_im0["image"], x_im1["image"]) and (not torch.equal(x_im0["hidden_target"], x_im1["hidden_target"]))
        )

        x_cu0 = render(ctx, h=h_fixed, k=k0, n_classes=n_classes)
        x_cu1 = render(ctx, h=h_fixed, k=k1, n_classes=n_classes)
        obs_cue_barrier_ok = bool(
            obs_cue_barrier_ok and torch.equal(x_cu0["cue_image"], x_cu1["cue_image"]) and (not torch.equal(x_cu0["hidden_target"], x_cu1["hidden_target"]))
        )

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

        A_im0_swap_follow = bool(_overlap_score(pA_im0_swap, t_im1) > _overlap_score(pA_im0_swap, t_im0))
        A_im1_swap_follow = bool(_overlap_score(pA_im1_swap, t_im0) > _overlap_score(pA_im1_swap, t_im1))
        if A_im0_swap_follow and A_im1_swap_follow:
            A_swap_follow_image += 1

        A_im0_swap_orig = bool(_overlap_score(pA_im0_swap, t_im0) > _overlap_score(pA_im0_swap, t_im1))
        A_im1_swap_orig = bool(_overlap_score(pA_im1_swap, t_im1) > _overlap_score(pA_im1_swap, t_im0))
        if A_im0_swap_orig and A_im1_swap_orig:
            A_swap_orig_both_image += 1

    n_ctx = int(len(ctxs))
    return {
        "n_ctx": n_ctx,
        "ood": bool(ood),
        "obs_image_barrier_ok": bool(obs_image_barrier_ok),
        "obs_cue_barrier_ok": bool(obs_cue_barrier_ok),
        "A_both_image_pair_rate": float(A_both_image) / float(n_ctx),
        "A_both_cue_pair_rate": float(A_both_cue) / float(n_ctx),
        "B_image_only_both_rate": float(B_img_both) / float(n_ctx),
        "B_cue_only_both_rate": float(B_cue_both) / float(n_ctx),
        "A_ablated_both_image_pair_rate": float(A_abl_both_image) / float(n_ctx),
        "A_swap_follow_image_pair_rate": float(A_swap_follow_image) / float(n_ctx),
        "A_swap_orig_both_image_pair_rate": float(A_swap_orig_both_image) / float(n_ctx),
        "seed": int(cfg.seed),
    }


@dataclass(frozen=True)
class TrainCfg:
    seed: int = 0
    steps: int = 9000
    batch_size: int = 128
    lr: float = 1e-3
    w_z: float = 5.0
    w_k: float = 0.0
    w_pos: float = 0.25
    w_rank_img: float = 0.25
    w_rank_cue: float = 0.25
    rank_n_ctx: int = 8
    rank_ood_ratio: float = 0.5
    train_ood_ratio: float = 0.5
    pair_n_ctx: int = 64
    img_size: int = 64


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--steps", type=int, default=9000)
    p.add_argument("--batch-size", type=int, default=128)
    p.add_argument("--lr", type=float, default=1e-3)
    p.add_argument("--w-z", type=float, default=5.0)
    p.add_argument("--w-k", type=float, default=0.0)
    p.add_argument("--w-pos", type=float, default=0.25)
    p.add_argument("--w-rank-img", type=float, default=0.25)
    p.add_argument("--w-rank-cue", type=float, default=0.25)
    p.add_argument("--rank-n-ctx", type=int, default=8)
    p.add_argument("--rank-ood-ratio", type=float, default=0.5)
    p.add_argument("--train-ood-ratio", type=float, default=0.5)
    p.add_argument("--pair-n-ctx", type=int, default=64)
    p.add_argument("--img-size", type=int, default=64)
    p.add_argument("--n-classes", type=int, required=True)
    p.add_argument("--z-classes", type=int, required=True)
    p.add_argument("--out-jsonl", type=str, default="")
    args = p.parse_args()

    cfg = TrainCfg(
        seed=int(args.seed),
        steps=int(args.steps),
        batch_size=int(args.batch_size),
        lr=float(args.lr),
        w_z=float(args.w_z),
        w_k=float(args.w_k),
        w_pos=float(args.w_pos),
        w_rank_img=float(args.w_rank_img),
        w_rank_cue=float(args.w_rank_cue),
        rank_n_ctx=int(args.rank_n_ctx),
        rank_ood_ratio=float(args.rank_ood_ratio),
        train_ood_ratio=float(args.train_ood_ratio),
        pair_n_ctx=int(args.pair_n_ctx),
        img_size=int(args.img_size),
    )

    device = torch.device(str(args.device))
    _seed_everything(int(cfg.seed))

    n_classes = int(args.n_classes)
    z_classes = int(args.z_classes)

    modelA = V9MinLiftModelA(z_classes=int(z_classes)).to(device)
    modelB_img = V9ImageOnlyBaseline().to(device)
    modelB_cue = V9CueOnlyBaseline().to(device)

    optA = torch.optim.Adam(modelA.parameters(), lr=float(cfg.lr))
    optB_img = torch.optim.Adam(modelB_img.parameters(), lr=float(cfg.lr))
    optB_cue = torch.optim.Adam(modelB_cue.parameters(), lr=float(cfg.lr))

    ds_iid = V9UnifiedDoubleBarrierMinLiftDatasetNScalableSpaced2_64(
        size=50_000, n_classes=int(n_classes), ood=False, img_size=int(cfg.img_size), seed=int(cfg.seed)
    )
    ds_ood = V9UnifiedDoubleBarrierMinLiftDatasetNScalableSpaced2_64(
        size=50_000, n_classes=int(n_classes), ood=True, img_size=int(cfg.img_size), seed=int(cfg.seed) + 1_000_000
    )

    dl_iid = DataLoader(ds_iid, batch_size=int(cfg.batch_size), shuffle=True, num_workers=0)
    dl_ood = DataLoader(ds_ood, batch_size=int(cfg.batch_size), shuffle=True, num_workers=0)
    it_iid = iter(dl_iid)
    it_ood = iter(dl_ood)

    for step in range(1, int(cfg.steps) + 1):
        use_ood = random.random() < float(cfg.train_ood_ratio)
        try:
            batch = next(it_ood if use_ood else it_iid)
        except StopIteration:
            it_iid = iter(dl_iid)
            it_ood = iter(dl_ood)
            batch = next(it_ood if use_ood else it_iid)

        cue = batch["cue_image"].to(device)
        image = batch["image"].to(device)
        tgt = batch["hidden_target"].to(device)
        h = batch["h"].to(device)

        cue_xy = _add_xy(cue)
        img_xy = _add_xy(image)

        pA = modelA(cue_xy, img_xy)
        pB_img = modelB_img(img_xy)
        pB_cue = modelB_cue(cue_xy)

        lossA_seg = F.binary_cross_entropy_with_logits(pA, tgt)
        lossB_img = F.binary_cross_entropy_with_logits(pB_img, tgt)
        lossB_cue = F.binary_cross_entropy_with_logits(pB_cue, tgt)

        z_logits = modelA.z_logits(cue_xy)
        lossA_z = F.cross_entropy(z_logits, (h % int(z_classes)).to(torch.long))

        lossA_pos = torch.tensor(0.0, device=device)
        if float(cfg.w_pos) != 0.0:
            pA01 = torch.sigmoid(pA)
            lossA_pos = F.mse_loss(_center_of_mass(pA01), _center_of_mass(tgt))

        lossA_rank_img = torch.tensor(0.0, device=device)
        if float(cfg.w_rank_img) != 0.0:
            ood_rank = random.random() < float(cfg.rank_ood_ratio)
            lossA_rank_img = _img_pair_rank_loss(
                modelA=modelA,
                device=device,
                n_classes=int(n_classes),
                n_ctx=int(cfg.rank_n_ctx),
                seed=int(cfg.seed + step),
                ood=bool(ood_rank),
                img_size=int(cfg.img_size),
            )

        lossA_rank_cue = torch.tensor(0.0, device=device)
        if float(cfg.w_rank_cue) != 0.0:
            ood_rank = random.random() < float(cfg.rank_ood_ratio)
            lossA_rank_cue = _cue_pair_rank_loss(
                modelA=modelA,
                device=device,
                n_classes=int(n_classes),
                n_ctx=int(cfg.rank_n_ctx),
                seed=int(cfg.seed + 1_000_000 + step),
                ood=bool(ood_rank),
                img_size=int(cfg.img_size),
            )

        lossA = (
            lossA_seg
            + float(cfg.w_z) * lossA_z
            + float(cfg.w_pos) * lossA_pos
            + float(cfg.w_rank_img) * lossA_rank_img
            + float(cfg.w_rank_cue) * lossA_rank_cue
        )
        lossB = lossB_img + lossB_cue

        optA.zero_grad(set_to_none=True)
        lossA.backward()
        optA.step()

        optB_img.zero_grad(set_to_none=True)
        lossB_img.backward()
        optB_img.step()

        optB_cue.zero_grad(set_to_none=True)
        lossB_cue.backward()
        optB_cue.step()

        if step % 250 == 0 or step == int(cfg.steps):
            with torch.no_grad():
                z_acc = float((torch.argmax(z_logits, dim=-1) == (h % int(z_classes))).float().mean().item())
                k_hat = modelA.k_hat_from_image(img_xy)
                k_acc = float((k_hat == batch["k"].to(device)).float().mean().item())
            print(
                f"step={step}/{int(cfg.steps)} loss={float(lossA.item()):.6f} "
                f"(A_seg={float(lossA_seg.item()):.6f}, A_z={float(lossA_z.item()):.6f}, "
                f"A_pos={float(lossA_pos.item()):.6f}, A_rank_img={float(lossA_rank_img.item()):.6f}, "
                f"A_rank_cue={float(lossA_rank_cue.item()):.6f}, "
                f"Bimg={float(lossB_img.item()):.6f}, Bcue={float(lossB_cue.item()):.6f})  "
                f"z_acc={z_acc:.4f} k_acc={k_acc:.4f}"
            )

    def _eval_split(*, ood: bool) -> dict:
        ds = V9UnifiedDoubleBarrierMinLiftDatasetNScalableSpaced2_64(
            size=1024, n_classes=int(n_classes), ood=bool(ood), img_size=int(cfg.img_size), seed=int(cfg.seed) + (2_000_000 if ood else 0)
        )
        dl = DataLoader(ds, batch_size=256, shuffle=False, num_workers=0)
        ious = []
        bi = []
        bc = []
        z_accs = []
        k_accs = []
        for b in dl:
            cue = _add_xy(b["cue_image"].to(device))
            img = _add_xy(b["image"].to(device))
            tgt = b["hidden_target"].to(device)
            h = b["h"].to(device)
            with torch.no_grad():
                pA = modelA(cue, img)
                pB_img = modelB_img(img)
                pB_cue = modelB_cue(cue)
                ious.append(_calculate_iou(pA, tgt))
                bi.append(_calculate_iou(pB_img, tgt))
                bc.append(_calculate_iou(pB_cue, tgt))
                zl = modelA.z_logits(cue)
                z_accs.append(float((torch.argmax(zl, dim=-1) == (h % int(z_classes))).float().mean().item()))
                k_hat = modelA.k_hat_from_image(img)
                k_accs.append(float((k_hat == b["k"].to(device)).float().mean().item()))
        return {
            "A_iou": float(sum(ious) / len(ious)),
            "B_img_iou": float(sum(bi) / len(bi)),
            "B_cue_iou": float(sum(bc) / len(bc)),
            "z_acc": float(sum(z_accs) / len(z_accs)),
            "k_acc": float(sum(k_accs) / len(k_accs)),
        }

    metrics = {"iid": _eval_split(ood=False), "ood": _eval_split(ood=True)}

    pair_cfg = PairEvalCfg(n_ctx=int(cfg.pair_n_ctx), seed=int(cfg.seed), img_size=int(cfg.img_size))
    pair_eval = {
        "iid": _pair_eval_one(modelA=modelA, modelB_img=modelB_img, modelB_cue=modelB_cue, device=device, cfg=pair_cfg, ood=False, n_classes=int(n_classes)),
        "ood": _pair_eval_one(modelA=modelA, modelB_img=modelB_img, modelB_cue=modelB_cue, device=device, cfg=pair_cfg, ood=True, n_classes=int(n_classes)),
    }

    out = {
        "kind": "aslmt_v9_unified_double_barrier_minlift_posloss_pairrank_imgcuerank_spaced2_64",
        "seed": int(cfg.seed),
        "n_classes": int(n_classes),
        "z_classes": int(z_classes),
        "train_ood_ratio": float(cfg.train_ood_ratio),
        "rank_ood_ratio": float(cfg.rank_ood_ratio),
        "rank_n_ctx": int(cfg.rank_n_ctx),
        "w_z": float(cfg.w_z),
        "w_k": float(cfg.w_k),
        "w_pos": float(cfg.w_pos),
        "w_rank_img": float(cfg.w_rank_img),
        "w_rank_cue": float(cfg.w_rank_cue),
        "metrics": metrics,
        "pair_eval": pair_eval,
    }

    print(json.dumps(out))
    if args.out_jsonl:
        with open(str(args.out_jsonl), "a", encoding="utf-8") as f:
            f.write(json.dumps(out) + "\n")


if __name__ == "__main__":
    main()

