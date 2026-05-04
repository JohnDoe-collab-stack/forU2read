import argparse
import json
import random
from dataclasses import asdict, dataclass
from pathlib import Path

import torch
import torch.nn.functional as F
from torch.utils.data import DataLoader

from aslmt_env_v20_algebra_v3b_nscalable_spaced2_64 import V20AlgebraV3bDatasetNScalableSpaced2_64
from aslmt_model_v20_algebra_v3b_query_zread import (
    V20AlgebraV3bCueOnlyBaseline,
    V20AlgebraV3bImageOnlyBaseline,
    V20AlgebraV3bQueryModelA_ZRead,
)
from render_aslmt_v20_algebra_v3b_paired_ctx_nscalable_spaced2_64 import Ctx, POS_STRIDE, render


def _policy_action_from_h(h: torch.Tensor) -> torch.Tensor:
    """
    Non-trivial policy for selecting the correct interface, as a deterministic function of `h`.

    We use a fixed xorshift-style bit-mixing so the correct action is not the simple parity `h % 2`.
    Output is in {0,1}.
    """
    x = h.to(torch.long) & 0xFFFFFFFF
    x = x ^ ((x << 13) & 0xFFFFFFFF)
    x = x ^ (x >> 17)
    x = x ^ ((x << 5) & 0xFFFFFFFF)
    return (x & 1).to(torch.long)


def _env_res_bit(*, h: torch.Tensor, k: torch.Tensor, action: torch.Tensor) -> torch.Tensor:
    """
    v3b-style action-conditioned response bit (qforced variant).

    Two actions, two "interfaces" (sensors). The correct interface is determined by `policy(h)`.

    - If we query the correct interface, the response equals `k`.
    - If we query the wrong interface, the response carries no information about `k`.
    """
    a = action.to(torch.long)
    kk = k.to(torch.long)
    h2 = _policy_action_from_h(h)
    correct = (a == h2).to(torch.long)
    return kk * correct


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


def _dice_loss(pred_logits: torch.Tensor, true_mask: torch.Tensor) -> torch.Tensor:
    p = torch.sigmoid(pred_logits)
    inter = (p * true_mask).sum(dim=(1, 2, 3))
    denom = p.sum(dim=(1, 2, 3)) + true_mask.sum(dim=(1, 2, 3))
    return 1.0 - (2.0 * inter / (denom + 1e-6)).mean()


def _center_of_mass(mask_logits: torch.Tensor) -> torch.Tensor:
    # return (B,2) in normalized coords [-1,1]
    B, C, H, W = mask_logits.shape
    if int(C) != 1:
        raise ValueError(f"_center_of_mass expects C==1, got shape={tuple(mask_logits.shape)}")
    p = torch.sigmoid(mask_logits).clamp_min(1e-6)
    xy = _xy_grid(H=int(H), W=int(W), device=mask_logits.device, dtype=mask_logits.dtype).expand(int(B), 2, int(H), int(W))
    tot = p.sum(dim=(2, 3), keepdim=True)
    cm = (p * xy).sum(dim=(2, 3), keepdim=True) / tot
    return cm.squeeze(-1).squeeze(-1)


@dataclass(frozen=True)
class PairEvalCfg:
    n_ctx: int
    seed: int
    img_size: int


def _pair_eval_one(
    *,
    modelA: V20AlgebraV3bQueryModelA_ZRead,
    modelB_img: V20AlgebraV3bImageOnlyBaseline,
    modelB_cue: V20AlgebraV3bCueOnlyBaseline,
    device: torch.device,
    cfg: PairEvalCfg,
    ood: bool,
    n_classes: int,
) -> dict:
    """
    Paired-context evaluation:

    Build pairs with shared scaffold but different (h,k), then check:
      - image-only barrier
      - cue-only barrier
      - correct predictions under both "gates" (image gate and cue gate)
      - ablation and swap controls (image gate)
    """
    # Mirror the best-passing v3b paired-context checks:
    # - image barrier: vary h with fixed k => images must match
    # - cue barrier: vary k with fixed h => cues must match
    # - swap follow: computed on the image-barrier pair where k is fixed, so swapping z alone is meaningful
    g = torch.Generator(device="cpu")
    g.manual_seed(int(cfg.seed) + (999 if bool(ood) else 0))

    n_classes = int(n_classes)
    n_ctx = int(cfg.n_ctx)
    img_size = int(cfg.img_size)

    # Context sampling close to v3b reference.
    min_occ_half = 20
    needed = int(POS_STRIDE) * int(n_classes - 1) + 1
    if bool(ood):
        min_occ_half = int((needed + 9) // 2)
    else:
        min_occ_half = int((needed + 7) // 2)

    ctxs: list[Ctx] = []
    for i in range(int(n_ctx)):
        occ_half = int(torch.randint(low=min_occ_half, high=min_occ_half + (3 if bool(ood) else 2), size=(1,), generator=g).item())
        margin = 4
        lo = int(occ_half) + margin
        hi = int(img_size) - int(occ_half) - margin
        if hi < lo:
            raise ValueError("ctx sampling failed: img_size too small for occ_half")
        cx = int(torch.randint(low=int(lo), high=int(hi) + 1, size=(1,), generator=g).item())
        cy = int(torch.randint(low=int(lo), high=int(hi) + 1, size=(1,), generator=g).item())
        t = int(torch.randint(low=2, high=(4 if bool(ood) else 3) + 1, size=(1,), generator=g).item())
        ctxs.append(Ctx(cx=cx, cy=cy, t=t, occ_half=occ_half, img_size=int(img_size), ood=bool(ood), seed=int(cfg.seed) + int(i)))

    obs_image_barrier_ok = True
    obs_cue_barrier_ok = True

    A_both_image = 0
    A_both_cue = 0
    B_img_both = 0
    B_cue_both = 0

    A_abl_both_image = 0
    A_swap_follow_image = 0
    A_swap_orig_both_image = 0

    h_pairs: list[tuple[int, int]] = []
    for i in range(n_classes):
        for j in range(i + 1, n_classes):
            h_pairs.append((i, j))

    for i, ctx in enumerate(ctxs):
        h0, h1 = h_pairs[i % len(h_pairs)]

        # Image barrier: vary h with fixed k.
        k_fixed = int((ctx.seed + 0) % 2)
        x_im0 = render(ctx, h=h0, k=k_fixed, n_classes=n_classes)
        x_im1 = render(ctx, h=h1, k=k_fixed, n_classes=n_classes)
        obs_image_barrier_ok = obs_image_barrier_ok and bool(torch.allclose(x_im0["image"], x_im1["image"]))

        cue_im0 = _add_xy(x_im0["cue_image"].unsqueeze(0).to(device))
        cue_im1 = _add_xy(x_im1["cue_image"].unsqueeze(0).to(device))
        image_fixed = _add_xy(x_im0["image"].unsqueeze(0).to(device))
        t_im0 = x_im0["hidden_target"].unsqueeze(0).to(device)
        t_im1 = x_im1["hidden_target"].unsqueeze(0).to(device)

        # Cue barrier: vary k with fixed h.
        h_fixed = int((ctx.seed + 1) % int(n_classes))
        x_cu0 = render(ctx, h=h_fixed, k=0, n_classes=n_classes)
        x_cu1 = render(ctx, h=h_fixed, k=1, n_classes=n_classes)
        obs_cue_barrier_ok = obs_cue_barrier_ok and bool(torch.allclose(x_cu0["cue_image"], x_cu1["cue_image"]))

        cue_fixed = _add_xy(x_cu0["cue_image"].unsqueeze(0).to(device))
        img0 = _add_xy(x_cu0["image"].unsqueeze(0).to(device))
        img1 = _add_xy(x_cu1["image"].unsqueeze(0).to(device))
        t_cu0 = x_cu0["hidden_target"].unsqueeze(0).to(device)
        t_cu1 = x_cu1["hidden_target"].unsqueeze(0).to(device)

        # A forward uses action-conditioned response bit.
        with torch.no_grad():
            # Image barrier evaluation
            act_im0 = modelA.chosen_action(cue_im0)
            act_im1 = modelA.chosen_action(cue_im1)
            h_im0 = x_im0["h"].unsqueeze(0).to(device)
            h_im1 = x_im1["h"].unsqueeze(0).to(device)
            k_im0 = x_im0["k"].unsqueeze(0).to(device)
            k_im1 = x_im1["k"].unsqueeze(0).to(device)
            res_im0 = _env_res_bit(h=h_im0, k=k_im0, action=act_im0)
            res_im1 = _env_res_bit(h=h_im1, k=k_im1, action=act_im1)
            pA_im0 = modelA.forward_with_res_bit(cue_im0, image_fixed, res_bit=res_im0)
            pA_im1 = modelA.forward_with_res_bit(cue_im1, image_fixed, res_bit=res_im1)
            A_im0_correct = bool(_overlap_score(pA_im0, t_im0) > _overlap_score(pA_im0, t_im1))
            A_im1_correct = bool(_overlap_score(pA_im1, t_im1) > _overlap_score(pA_im1, t_im0))
            if A_im0_correct and A_im1_correct:
                A_both_image += 1

            # Cue barrier evaluation
            act0 = modelA.chosen_action(cue_fixed)
            h0t = x_cu0["h"].unsqueeze(0).to(device)
            k0t = x_cu0["k"].unsqueeze(0).to(device)
            k1t = x_cu1["k"].unsqueeze(0).to(device)
            res0 = _env_res_bit(h=h0t, k=k0t, action=act0)
            res1 = _env_res_bit(h=h0t, k=k1t, action=act0)
            pA0 = modelA.forward_with_res_bit(cue_fixed, img0, res_bit=res0)
            pA1 = modelA.forward_with_res_bit(cue_fixed, img1, res_bit=res1)
            A_cu0_correct = bool(_overlap_score(pA0, t_cu0) > _overlap_score(pA0, t_cu1))
            A_cu1_correct = bool(_overlap_score(pA1, t_cu1) > _overlap_score(pA1, t_cu0))
            if A_cu0_correct and A_cu1_correct:
                A_both_cue += 1

            # Baselines (visible-only) for both gates
            pB_im0 = modelB_img(image_fixed)
            pB_im1 = modelB_img(image_fixed)
            if bool(_overlap_score(pB_im0, t_im0) > _overlap_score(pB_im0, t_im1)) and bool(
                _overlap_score(pB_im1, t_im1) > _overlap_score(pB_im1, t_im0)
            ):
                B_img_both += 1

            pB0 = modelB_cue(cue_fixed)
            pB1 = modelB_cue(cue_fixed)
            if bool(_overlap_score(pB0, t_cu0) > _overlap_score(pB0, t_cu1)) and bool(
                _overlap_score(pB1, t_cu1) > _overlap_score(pB1, t_cu0)
            ):
                B_cue_both += 1

            # Ablation and swap (image gate only)
            pA_im0_abl = modelA.ablated_forward_with_res_bit(cue_im0, image_fixed, res_bit=res_im0)
            pA_im1_abl = modelA.ablated_forward_with_res_bit(cue_im1, image_fixed, res_bit=res_im1)
            if bool(_overlap_score(pA_im0_abl, t_im0) > _overlap_score(pA_im0_abl, t_im1)) and bool(
                _overlap_score(pA_im1_abl, t_im1) > _overlap_score(pA_im1_abl, t_im0)
            ):
                A_abl_both_image += 1

            cue_pair = torch.cat([cue_im0, cue_im1], dim=0)
            img_pair = torch.cat([image_fixed, image_fixed], dim=0)
            res_pair = torch.cat([res_im0, res_im1], dim=0)
            perm = torch.tensor([1, 0], device=device, dtype=torch.long)
            pA_pair_swap = modelA.swap_forward_with_res_bit(cue_pair, img_pair, res_bit=res_pair, perm=perm)
            pA_im0_swap = pA_pair_swap[0:1]
            pA_im1_swap = pA_pair_swap[1:2]

            A_im0_swap_follow = bool(_overlap_score(pA_im0_swap, t_im1) > _overlap_score(pA_im0_swap, t_im0))
            A_im1_swap_follow = bool(_overlap_score(pA_im1_swap, t_im0) > _overlap_score(pA_im1_swap, t_im1))
            if A_im0_swap_follow and A_im1_swap_follow:
                A_swap_follow_image += 1

            A_im0_swap_orig = bool(_overlap_score(pA_im0_swap, t_im0) > _overlap_score(pA_im0_swap, t_im1))
            A_im1_swap_orig = bool(_overlap_score(pA_im1_swap, t_im1) > _overlap_score(pA_im1_swap, t_im0))
            if A_im0_swap_orig and A_im1_swap_orig:
                A_swap_orig_both_image += 1

    return {
        "n_ctx": int(len(ctxs)),
        "ood": bool(ood),
        "obs_image_barrier_ok": bool(obs_image_barrier_ok),
        "obs_cue_barrier_ok": bool(obs_cue_barrier_ok),
        "A_both_image_pair_rate": float(A_both_image) / float(len(ctxs)),
        "A_both_cue_pair_rate": float(A_both_cue) / float(len(ctxs)),
        "B_image_only_both_rate": float(B_img_both) / float(len(ctxs)),
        "B_cue_only_both_rate": float(B_cue_both) / float(len(ctxs)),
        "A_ablated_both_image_pair_rate": float(A_abl_both_image) / float(len(ctxs)),
        "A_swap_follow_image_pair_rate": float(A_swap_follow_image) / float(len(ctxs)),
        "A_swap_orig_both_image_pair_rate": float(A_swap_orig_both_image) / float(len(ctxs)),
        "seed": int(cfg.seed),
    }


@dataclass(frozen=True)
class TrainCfg:
    profile: str
    seed: int
    steps: int
    batch_size: int
    lr: float
    train_ood_ratio: float
    pair_n_ctx: int
    img_size: int
    n_classes: int
    z_classes: int
    w_z: float
    w_k: float
    w_q: float
    w_pos: float
    w_rank_img: float
    w_rank_cue: float
    rank_n_ctx: int
    rank_ood_ratio: float
    rank_margin: float
    w_bce: float
    w_dice: float
    bce_pos_weight: str
    faildump_max: int = 50


def main() -> None:
    p = argparse.ArgumentParser(description="ASLMT v20 algebra v3b (zread) training script.")
    p.add_argument("--profile", type=str, default="solid", choices=["smoke", "solid"])
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--steps", type=int, default=9000)
    p.add_argument("--batch-size", type=int, default=64)
    p.add_argument("--lr", type=float, default=1e-3)
    p.add_argument("--train-ood-ratio", type=float, default=0.5)
    p.add_argument("--pair-n-ctx", type=int, default=64)
    p.add_argument("--img-size", type=int, default=64)
    p.add_argument("--n-classes", type=int, required=True)
    p.add_argument("--z-classes", type=int, required=True)
    p.add_argument("--w-z", type=float, default=5.0)
    p.add_argument("--w-k", type=float, default=0.0)
    p.add_argument("--w-q", type=float, default=1.0)
    p.add_argument("--w-pos", type=float, default=0.25)
    p.add_argument("--w-rank-img", type=float, default=1.0)
    p.add_argument("--w-rank-cue", type=float, default=0.25)
    p.add_argument("--rank-n-ctx", type=int, default=8)
    p.add_argument("--rank-ood-ratio", type=float, default=0.5)
    p.add_argument("--rank-margin", type=float, default=2.0)
    p.add_argument("--w-bce", type=float, default=1.0)
    p.add_argument("--w-dice", type=float, default=1.0)
    p.add_argument("--bce-pos-weight", type=str, default="auto")
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--out-jsonl", type=str, default="")
    p.add_argument("--out-ckpt", type=str, default="")
    p.add_argument("--out-faildump-jsonl", type=str, default="")
    args = p.parse_args()

    cfg = TrainCfg(
        profile=str(args.profile),
        seed=int(args.seed),
        steps=int(args.steps),
        batch_size=int(args.batch_size),
        lr=float(args.lr),
        train_ood_ratio=float(args.train_ood_ratio),
        pair_n_ctx=int(args.pair_n_ctx),
        img_size=int(args.img_size),
        n_classes=int(args.n_classes),
        z_classes=int(args.z_classes),
        w_z=float(args.w_z),
        w_k=float(args.w_k),
        w_q=float(args.w_q),
        w_pos=float(args.w_pos),
        w_rank_img=float(args.w_rank_img),
        w_rank_cue=float(args.w_rank_cue),
        rank_n_ctx=int(args.rank_n_ctx),
        rank_ood_ratio=float(args.rank_ood_ratio),
        rank_margin=float(args.rank_margin),
        w_bce=float(args.w_bce),
        w_dice=float(args.w_dice),
        bce_pos_weight=str(args.bce_pos_weight),
    )

    _seed_everything(int(cfg.seed))
    device = torch.device(str(args.device))

    n_classes = int(cfg.n_classes)
    z_classes = int(cfg.z_classes)

    ds_iid = V20AlgebraV3bDatasetNScalableSpaced2_64(
        size=20000 if str(cfg.profile) == "solid" else 2048,
        n_classes=int(n_classes),
        ood=False,
        img_size=int(cfg.img_size),
        seed=int(cfg.seed) + 17,
    )
    ds_ood = V20AlgebraV3bDatasetNScalableSpaced2_64(
        size=20000 if str(cfg.profile) == "solid" else 2048,
        n_classes=int(n_classes),
        ood=True,
        img_size=int(cfg.img_size),
        seed=int(cfg.seed) + 17,
    )

    # Mix IID/OOD in training.
    # We implement by sampling from each loader per step according to train_ood_ratio.
    dl_iid = DataLoader(ds_iid, batch_size=int(cfg.batch_size), shuffle=True, num_workers=0)
    dl_ood = DataLoader(ds_ood, batch_size=int(cfg.batch_size), shuffle=True, num_workers=0)
    it_iid = iter(dl_iid)
    it_ood = iter(dl_ood)

    modelA = V20AlgebraV3bQueryModelA_ZRead(z_classes=int(z_classes)).to(device)
    modelB_img = V20AlgebraV3bImageOnlyBaseline().to(device)
    modelB_cue = V20AlgebraV3bCueOnlyBaseline().to(device)

    opt = torch.optim.AdamW(
        list(modelA.parameters()) + list(modelB_img.parameters()) + list(modelB_cue.parameters()), lr=float(cfg.lr)
    )

    def _bce_pos_weight_tensor() -> torch.Tensor | None:
        if str(cfg.bce_pos_weight) == "none":
            return None
        if str(cfg.bce_pos_weight) == "auto":
            # approximate positive weight for occluded targets in this family
            return torch.tensor(10.0, device=device)
        try:
            return torch.tensor(float(cfg.bce_pos_weight), device=device)
        except Exception:
            raise ValueError(f"invalid bce_pos_weight={cfg.bce_pos_weight!r}")

    bce_pos_w = _bce_pos_weight_tensor()

    def _img_pair_contract_rank_loss(
        *, modelA: V20AlgebraV3bQueryModelA_ZRead, device: torch.device, n_classes: int, ctxs: list[Ctx], margin: float
    ) -> torch.Tensor:
        loss_terms: list[torch.Tensor] = []
        for ctx in ctxs:
            h0 = random.randint(0, int(n_classes) - 1)
            h1 = random.randint(0, int(n_classes) - 1)
            k0 = random.randint(0, 1)
            k1 = random.randint(0, 1)
            ex0 = render(ctx, h=int(h0), k=int(k0), n_classes=int(n_classes))
            ex1 = render(ctx, h=int(h1), k=int(k1), n_classes=int(n_classes))
            cue0 = _add_xy(ex0["cue_image"].unsqueeze(0).to(device))
            cue1 = _add_xy(ex1["cue_image"].unsqueeze(0).to(device))
            img0 = _add_xy(ex0["image"].unsqueeze(0).to(device))
            img1 = _add_xy(ex1["image"].unsqueeze(0).to(device))
            t0 = ex0["hidden_target"].unsqueeze(0).to(device)
            t1 = ex1["hidden_target"].unsqueeze(0).to(device)
            h0t = torch.tensor([int(h0)], device=device, dtype=torch.long)
            h1t = torch.tensor([int(h1)], device=device, dtype=torch.long)
            k0t = torch.tensor([int(k0)], device=device, dtype=torch.long)
            k1t = torch.tensor([int(k1)], device=device, dtype=torch.long)
            with torch.no_grad():
                act0 = modelA.chosen_action(cue0)
                act1 = modelA.chosen_action(cue1)
            res0 = _env_res_bit(h=h0t, k=k0t, action=act0)
            res1 = _env_res_bit(h=h1t, k=k1t, action=act1)
            p0 = modelA.forward_with_res_bit(cue0, img0, res_bit=res0)
            p1 = modelA.forward_with_res_bit(cue1, img1, res_bit=res1)

            # enforce: p0 overlaps t0 more than t1, and p1 overlaps t1 more than t0
            s00 = _overlap_score(p0, t0)
            s01 = _overlap_score(p0, t1)
            s11 = _overlap_score(p1, t1)
            s10 = _overlap_score(p1, t0)
            margin_t = torch.tensor(float(margin), device=device)
            loss_terms.append(F.relu(margin_t - (s00 - s01)))
            loss_terms.append(F.relu(margin_t - (s11 - s10)))

            # swap rank: swapped should prefer the opposite
            cue_pair = torch.cat([cue0, cue1], dim=0)
            img_pair = torch.cat([img0, img1], dim=0)
            res_pair = torch.cat([res0, res1], dim=0)
            perm = torch.tensor([1, 0], device=device, dtype=torch.long)
            # For swap-ranking, we swap both mediators' carriers:
            # - z is swapped inside swap_forward_with_res_bit
            # - res_bit is swapped here (so the full (h,k) target follows)
            res_pair_swap = res_pair[perm]
            p_pair_swap = modelA.swap_forward_with_res_bit(cue_pair, img_pair, res_bit=res_pair_swap, perm=perm)
            p0_swap = p_pair_swap[0:1]
            p1_swap = p_pair_swap[1:2]
            sw00 = _overlap_score(p0_swap, t0)
            sw01 = _overlap_score(p0_swap, t1)
            sw11 = _overlap_score(p1_swap, t1)
            sw10 = _overlap_score(p1_swap, t0)
            loss_terms.append(F.relu(margin_t - (sw01 - sw00)))
            loss_terms.append(F.relu(margin_t - (sw10 - sw11)))

        if not loss_terms:
            return torch.tensor(0.0, device=device)
        return torch.stack(loss_terms, dim=0).mean()

    def _cue_pair_contract_rank_loss(
        *, modelA: V20AlgebraV3bQueryModelA_ZRead, device: torch.device, n_classes: int, ctxs: list[Ctx], margin: float
    ) -> torch.Tensor:
        loss_terms: list[torch.Tensor] = []
        for ctx in ctxs:
            h0 = random.randint(0, int(n_classes) - 1)
            k0 = random.randint(0, 1)
            k1 = random.randint(0, 1)
            ex0 = render(ctx, h=int(h0), k=int(k0), n_classes=int(n_classes))
            ex1 = render(ctx, h=int(h0), k=int(k1), n_classes=int(n_classes))
            cue = _add_xy(ex0["cue_image"].unsqueeze(0).to(device))
            img0 = _add_xy(ex0["image"].unsqueeze(0).to(device))
            img1 = _add_xy(ex1["image"].unsqueeze(0).to(device))
            t0 = ex0["hidden_target"].unsqueeze(0).to(device)
            t1 = ex1["hidden_target"].unsqueeze(0).to(device)
            h0t = torch.tensor([int(h0)], device=device, dtype=torch.long)
            k0t = torch.tensor([int(k0)], device=device, dtype=torch.long)
            k1t = torch.tensor([int(k1)], device=device, dtype=torch.long)
            with torch.no_grad():
                act = modelA.chosen_action(cue)
            res0 = _env_res_bit(h=h0t, k=k0t, action=act)
            res1 = _env_res_bit(h=h0t, k=k1t, action=act)
            p0 = modelA.forward_with_res_bit(cue, img0, res_bit=res0)
            p1 = modelA.forward_with_res_bit(cue, img1, res_bit=res1)

            s00 = _overlap_score(p0, t0)
            s01 = _overlap_score(p0, t1)
            s11 = _overlap_score(p1, t1)
            s10 = _overlap_score(p1, t0)
            margin_t = torch.tensor(float(margin), device=device)
            loss_terms.append(F.relu(margin_t - (s00 - s01)))
            loss_terms.append(F.relu(margin_t - (s11 - s10)))

        if not loss_terms:
            return torch.tensor(0.0, device=device)
        return torch.stack(loss_terms, dim=0).mean()

    # build ctx bank for rank loss
    def _sample_ctxs(*, n_ctx: int, ood: bool) -> list[Ctx]:
        out = []
        for i in range(int(n_ctx)):
            ctx = Ctx(cx=32, cy=32, t=2, occ_half=20, img_size=int(cfg.img_size), ood=bool(ood), seed=int(cfg.seed) + i)
            out.append(ctx)
        return out

    ctxs_iid = _sample_ctxs(n_ctx=int(cfg.rank_n_ctx), ood=False)
    ctxs_ood = _sample_ctxs(n_ctx=int(cfg.rank_n_ctx), ood=True)

    for step in range(1, int(cfg.steps) + 1):
        use_ood = random.random() < float(cfg.train_ood_ratio)
        it = it_ood if bool(use_ood) else it_iid
        try:
            batch = next(it)
        except StopIteration:
            if bool(use_ood):
                it_ood = iter(dl_ood)
                batch = next(it_ood)
            else:
                it_iid = iter(dl_iid)
                batch = next(it_iid)

        cue = _add_xy(batch["cue_image"].to(device))
        img = _add_xy(batch["image"].to(device))
        tgt = batch["hidden_target"].to(device)
        h = batch["h"].to(device)
        k = batch["k"].to(device)

        q_logits = modelA.logits_query(cue)
        action = torch.argmax(q_logits, dim=-1).to(torch.long)
        res_bit = _env_res_bit(h=h, k=k, action=action)
        pA = modelA.forward_with_res_bit(cue, img, res_bit=res_bit)
        pB_img = modelB_img(img)
        pB_cue = modelB_cue(cue)

        # segmentation losses
        if bce_pos_w is None:
            lossA_seg_bce = F.binary_cross_entropy_with_logits(pA, tgt)
        else:
            lossA_seg_bce = F.binary_cross_entropy_with_logits(pA, tgt, pos_weight=bce_pos_w)
        lossA_seg_dice = _dice_loss(pA, tgt) if float(cfg.w_dice) != 0.0 else torch.tensor(0.0, device=device)
        lossA_seg = float(cfg.w_bce) * lossA_seg_bce + float(cfg.w_dice) * lossA_seg_dice

        lossB_img = F.binary_cross_entropy_with_logits(pB_img, tgt)
        lossB_cue = F.binary_cross_entropy_with_logits(pB_cue, tgt)

        # z & q losses
        z_logits = modelA.z_logits(cue)
        lossA_z = F.cross_entropy(z_logits, (h % int(z_classes)).to(torch.long))
        lossA_q = F.cross_entropy(q_logits, _policy_action_from_h(h))

        # optional position loss
        lossA_pos = torch.tensor(0.0, device=device)
        if float(cfg.w_pos) != 0.0:
            lossA_pos = F.mse_loss(_center_of_mass(pA), _center_of_mass(tgt))

        # optional rank losses
        lossA_rank_img = torch.tensor(0.0, device=device)
        if float(cfg.w_rank_img) != 0.0:
            lossA_rank_img_iid = _img_pair_contract_rank_loss(
                modelA=modelA, device=device, n_classes=int(n_classes), ctxs=ctxs_iid, margin=float(cfg.rank_margin)
            )
            lossA_rank_img_ood = _img_pair_contract_rank_loss(
                modelA=modelA, device=device, n_classes=int(n_classes), ctxs=ctxs_ood, margin=float(cfg.rank_margin)
            )
            lossA_rank_img = 0.5 * (lossA_rank_img_iid + lossA_rank_img_ood)

        lossA_rank_cue = torch.tensor(0.0, device=device)
        if float(cfg.w_rank_cue) != 0.0:
            lossA_rank_cue_iid = _cue_pair_contract_rank_loss(
                modelA=modelA, device=device, n_classes=int(n_classes), ctxs=ctxs_iid, margin=float(cfg.rank_margin)
            )
            lossA_rank_cue_ood = _cue_pair_contract_rank_loss(
                modelA=modelA, device=device, n_classes=int(n_classes), ctxs=ctxs_ood, margin=float(cfg.rank_margin)
            )
            lossA_rank_cue = 0.5 * (lossA_rank_cue_iid + lossA_rank_cue_ood)

        lossA = (
            lossA_seg
            + float(cfg.w_z) * lossA_z
            + float(cfg.w_q) * lossA_q
            + float(cfg.w_pos) * lossA_pos
            + float(cfg.w_rank_img) * lossA_rank_img
            + float(cfg.w_rank_cue) * lossA_rank_cue
        )
        lossB = lossB_img + lossB_cue
        loss = lossA + lossB

        opt.zero_grad(set_to_none=True)
        loss.backward()
        opt.step()

        if int(step) % 200 == 0:
            print(
                json.dumps(
                    {
                        "step": int(step),
                        "split": "ood" if bool(use_ood) else "iid",
                        "loss": float(loss.item()),
                        "lossA": float(lossA.item()),
                        "lossB": float(lossB.item()),
                        "lossA_seg": float(lossA_seg.item()),
                        "lossA_seg_bce": float(lossA_seg_bce.item()),
                        "lossA_seg_dice": float(lossA_seg_dice.item()) if float(cfg.w_dice) != 0.0 else 0.0,
                        "lossA_z": float(lossA_z.item()),
                        "lossA_q": float(lossA_q.item()),
                        "lossA_pos": float(lossA_pos.item()) if float(cfg.w_pos) != 0.0 else 0.0,
                        "lossA_rank_img": float(lossA_rank_img.item()) if float(cfg.w_rank_img) != 0.0 else 0.0,
                        "lossA_rank_cue": float(lossA_rank_cue.item()) if float(cfg.w_rank_cue) != 0.0 else 0.0,
                    }
                )
            )

    # Evaluation
    modelA.eval()
    modelB_img.eval()
    modelB_cue.eval()

    def _eval_split(*, ood: bool) -> dict:
        ds = V20AlgebraV3bDatasetNScalableSpaced2_64(
            size=2048 if str(cfg.profile) == "solid" else 256,
            n_classes=int(n_classes),
            ood=bool(ood),
            img_size=int(cfg.img_size),
            seed=int(cfg.seed) + (999 if bool(ood) else 0),
        )
        dl = DataLoader(ds, batch_size=int(cfg.batch_size), shuffle=False, num_workers=0)
        ious = []
        bi = []
        bc = []
        z_accs = []
        q_accs = []
        res_accs = []
        action_rates = []
        for b in dl:
            cue = _add_xy(b["cue_image"].to(device))
            img = _add_xy(b["image"].to(device))
            tgt = b["hidden_target"].to(device)
            h = b["h"].to(device)
            k = b["k"].to(device)
            with torch.no_grad():
                act = modelA.chosen_action(cue)
                action_rates.append(float(act.to(dtype=torch.float32).mean().item()))
                res = _env_res_bit(h=h, k=k, action=act)
                pA = modelA.forward_with_res_bit(cue, img, res_bit=res)
                pB_img = modelB_img(img)
                pB_cue = modelB_cue(cue)
                ious.append(_calculate_iou(pA, tgt))
                bi.append(_calculate_iou(pB_img, tgt))
                bc.append(_calculate_iou(pB_cue, tgt))
                zl = modelA.z_logits(cue)
                z_accs.append(float((torch.argmax(zl, dim=-1) == (h % int(z_classes))).float().mean().item()))
                q_accs.append(float((act == _policy_action_from_h(h)).float().mean().item()))
                res_accs.append(float((res == k.to(torch.long)).float().mean().item()))
        return {
            "A_iou": float(sum(ious) / len(ious)),
            "B_img_iou": float(sum(bi) / len(bi)),
            "B_cue_iou": float(sum(bc) / len(bc)),
            "z_acc": float(sum(z_accs) / len(z_accs)),
            "q_acc": float(sum(q_accs) / len(q_accs)),
            "res_acc": float(sum(res_accs) / len(res_accs)),
            "query_action_rate": float(sum(action_rates) / len(action_rates)) if action_rates else 0.0,
        }

    metrics = {"iid": _eval_split(ood=False), "ood": _eval_split(ood=True)}

    pair_cfg = PairEvalCfg(n_ctx=int(cfg.pair_n_ctx), seed=int(cfg.seed), img_size=int(cfg.img_size))
    pair_eval = {
        "iid": _pair_eval_one(
            modelA=modelA, modelB_img=modelB_img, modelB_cue=modelB_cue, device=device, cfg=pair_cfg, ood=False, n_classes=int(n_classes)
        ),
        "ood": _pair_eval_one(
            modelA=modelA, modelB_img=modelB_img, modelB_cue=modelB_cue, device=device, cfg=pair_cfg, ood=True, n_classes=int(n_classes)
        ),
    }

    out = {
        "kind": "aslmt_v20_algebra_v3b_unified_v2_strong_qforced_zread_policy_nontrivial",
        "seed": int(cfg.seed),
        "n_classes": int(n_classes),
        "z_classes": int(z_classes),
        "train_ood_ratio": float(cfg.train_ood_ratio),
        "rank_ood_ratio": float(cfg.rank_ood_ratio),
        "rank_n_ctx": int(cfg.rank_n_ctx),
        "rank_margin": float(cfg.rank_margin),
        "w_z": float(cfg.w_z),
        "w_k": float(cfg.w_k),
        "w_q": float(cfg.w_q),
        "w_pos": float(cfg.w_pos),
        "w_rank_img": float(cfg.w_rank_img),
        "w_rank_cue": float(cfg.w_rank_cue),
        "w_bce": float(cfg.w_bce),
        "w_dice": float(cfg.w_dice),
        "bce_pos_weight": str(cfg.bce_pos_weight),
        "metrics": metrics,
        "pair_eval": pair_eval,
    }

    print(json.dumps(out))
    if args.out_jsonl:
        with open(str(args.out_jsonl), "a", encoding="utf-8") as f:
            f.write(json.dumps(out) + "\n")

    if str(args.out_ckpt).strip():
        ckpt_path = Path(str(args.out_ckpt)).expanduser().resolve()
        ckpt_path.parent.mkdir(parents=True, exist_ok=True)
        torch.save(
            {
                "kind": out["kind"],
                "seed": int(cfg.seed),
                "n_classes": int(n_classes),
                "z_classes": int(z_classes),
                "cfg": {k: getattr(cfg, k) for k in cfg.__dataclass_fields__.keys()},
                "modelA_state_dict": modelA.state_dict(),
            },
            ckpt_path,
        )

    if str(args.out_faildump_jsonl).strip():
        need_dump = False
        for sp in ("iid", "ood"):
            pe = pair_eval[sp]
            if not bool(pe.get("obs_image_barrier_ok", False)) or not bool(pe.get("obs_cue_barrier_ok", False)):
                need_dump = True
            if float(pe.get("A_both_image_pair_rate", 0.0)) != 1.0:
                need_dump = True
            if float(pe.get("A_swap_follow_image_pair_rate", 0.0)) != 1.0:
                need_dump = True
            if float(pe.get("A_both_cue_pair_rate", 0.0)) != 1.0:
                need_dump = True
        if need_dump:
            dump_path = Path(str(args.out_faildump_jsonl)).expanduser().resolve()
            dump_path.parent.mkdir(parents=True, exist_ok=True)
            rec = {
                "kind": "aslmt_v20_algebra_v3b_faildump_image_gate",
                "seed": int(cfg.seed),
                "n_classes": int(n_classes),
                "z_classes": int(z_classes),
                "pair_n_ctx": int(cfg.pair_n_ctx),
                "img_size": int(cfg.img_size),
                "pair_eval": pair_eval,
            }
            with open(str(dump_path), "a", encoding="utf-8") as f:
                f.write(json.dumps(rec) + "\n")


if __name__ == "__main__":
    main()
