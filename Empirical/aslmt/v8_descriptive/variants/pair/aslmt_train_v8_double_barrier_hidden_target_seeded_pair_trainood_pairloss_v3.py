import argparse
import json
import random
from dataclasses import dataclass

import torch
import torch.nn.functional as F

from aslmt_model_v8_double_barrier_jepa import V8DoubleBarrierCausalJEPA, V8CueOnlyBaseline, V8ImageOnlyBaseline
from render_v8_paired_ctx import Ctx, render


def v8_jepa_loss(pred_latent: torch.Tensor, target_latent: torch.Tensor, z: torch.Tensor) -> torch.Tensor:
    pos = (pred_latent * target_latent).sum(dim=-1).mean()
    perm = torch.randperm(pred_latent.size(0), device=pred_latent.device)
    neg = (pred_latent * target_latent[perm]).sum(dim=-1).mean()
    std_z = torch.sqrt(z.var(dim=0) + 1e-4)
    var_loss = torch.relu(0.1 - std_z).mean()
    return -(pos) + neg + 10.0 * var_loss


def calculate_iou(pred_mask: torch.Tensor, true_mask: torch.Tensor) -> float:
    pred_bin = (torch.sigmoid(pred_mask) > 0.5).float()
    intersection = (pred_bin * true_mask).sum(dim=(1, 2, 3))
    union = (pred_bin + true_mask).clamp(0, 1).sum(dim=(1, 2, 3))
    return float((intersection / (union + 1e-6)).mean().item())


def _seed_everything(seed: int) -> None:
    seed = int(seed)
    random.seed(seed)
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)


def _overlap_score(pred_logits: torch.Tensor, true_mask: torch.Tensor) -> torch.Tensor:
    return (torch.sigmoid(pred_logits) * true_mask).sum(dim=(1, 2, 3))


def _pair_rank_loss(pred_logits: torch.Tensor, target_right: torch.Tensor, target_wrong: torch.Tensor) -> torch.Tensor:
    s_right = _overlap_score(pred_logits, target_right)
    s_wrong = _overlap_score(pred_logits, target_wrong)
    return F.softplus(s_wrong - s_right).mean()


def _weighted_bce_with_logits(pred_logits: torch.Tensor, target: torch.Tensor, *, pos_weight_max: float) -> torch.Tensor:
    # Targets are sparse (hidden-only inside occluder). Without reweighting, predicting zeros can look good.
    pos = target.mean().clamp(min=1e-6)
    w = ((1.0 - pos) / pos).clamp(min=1.0, max=float(pos_weight_max))
    w_t = torch.tensor(float(w.item()), device=pred_logits.device)
    return F.binary_cross_entropy_with_logits(pred_logits, target, pos_weight=w_t)


@dataclass(frozen=True)
class PairEvalCfg:
    n_ctx: int = 64
    seed: int = 0
    img_size: int = 32


def _sample_ctxs(*, n: int, seed: int, ood: bool, img_size: int) -> list[Ctx]:
    g = torch.Generator()
    g.manual_seed(int(seed))

    cx = torch.randint(low=12, high=21, size=(n,), generator=g).tolist()
    cy = torch.randint(low=12, high=21, size=(n,), generator=g).tolist()
    if ood:
        t = torch.randint(low=2, high=5, size=(n,), generator=g).tolist()  # 2..4
        occ_half = torch.randint(low=7, high=10, size=(n,), generator=g).tolist()  # 7..9
    else:
        t = torch.randint(low=2, high=4, size=(n,), generator=g).tolist()  # 2..3
        occ_half = torch.randint(low=5, high=7, size=(n,), generator=g).tolist()  # 5..6

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


def _stack(xs: list[torch.Tensor], device: torch.device) -> torch.Tensor:
    return torch.cat([x.unsqueeze(0).to(device) for x in xs], dim=0)


def _make_image_barrier_batch(ctxs: list[Ctx], device: torch.device) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor]:
    cues, images, targets, wrong = [], [], [], []
    for ctx in ctxs:
        k_fixed = int(ctx.seed % 2)
        x0 = render(ctx, h=0, k=k_fixed)
        x1 = render(ctx, h=1, k=k_fixed)
        cues.append(x0["cue_image"])
        images.append(x0["image"])
        targets.append(x0["hidden_target"])
        wrong.append(x1["hidden_target"])
        cues.append(x1["cue_image"])
        images.append(x1["image"])
        targets.append(x1["hidden_target"])
        wrong.append(x0["hidden_target"])
    return _stack(cues, device), _stack(images, device), _stack(targets, device), _stack(wrong, device)


def _make_cue_barrier_batch(ctxs: list[Ctx], device: torch.device) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor]:
    cues, images, targets, wrong = [], [], [], []
    for ctx in ctxs:
        h_fixed = int((ctx.seed + 1) % 2)
        x0 = render(ctx, h=h_fixed, k=0)
        x1 = render(ctx, h=h_fixed, k=1)
        cues.append(x0["cue_image"])
        images.append(x0["image"])
        targets.append(x0["hidden_target"])
        wrong.append(x1["hidden_target"])
        cues.append(x1["cue_image"])
        images.append(x1["image"])
        targets.append(x1["hidden_target"])
        wrong.append(x0["hidden_target"])
    return _stack(cues, device), _stack(images, device), _stack(targets, device), _stack(wrong, device)


def _pair_eval_one(
    *,
    modelA: V8DoubleBarrierCausalJEPA,
    modelB_img: V8ImageOnlyBaseline,
    modelB_cue: V8CueOnlyBaseline,
    device: torch.device,
    cfg: PairEvalCfg,
    ood: bool,
) -> dict:
    ctxs = _sample_ctxs(n=int(cfg.n_ctx), seed=int(cfg.seed), ood=bool(ood), img_size=int(cfg.img_size))

    obs_image_barrier_ok = True
    obs_cue_barrier_ok = True

    A_both_image = 0
    A_both_cue = 0

    B_img_both = 0
    B_cue_both = 0

    for ctx in ctxs:
        k_fixed = int(ctx.seed % 2)
        h_fixed = int((ctx.seed + 1) % 2)

        x_im0 = render(ctx, h=0, k=k_fixed)
        x_im1 = render(ctx, h=1, k=k_fixed)
        obs_image_barrier_ok = bool(
            obs_image_barrier_ok
            and torch.equal(x_im0["image"], x_im1["image"])
            and (not torch.equal(x_im0["hidden_target"], x_im1["hidden_target"]))
        )

        x_cu0 = render(ctx, h=h_fixed, k=0)
        x_cu1 = render(ctx, h=h_fixed, k=1)
        obs_cue_barrier_ok = bool(
            obs_cue_barrier_ok
            and torch.equal(x_cu0["cue_image"], x_cu1["cue_image"])
            and (not torch.equal(x_cu0["hidden_target"], x_cu1["hidden_target"]))
        )

        cue_im0 = x_im0["cue_image"].unsqueeze(0).to(device)
        cue_im1 = x_im1["cue_image"].unsqueeze(0).to(device)
        image_fixed = x_im0["image"].unsqueeze(0).to(device)
        t_im0 = x_im0["hidden_target"].unsqueeze(0).to(device)
        t_im1 = x_im1["hidden_target"].unsqueeze(0).to(device)

        cue_fixed = x_cu0["cue_image"].unsqueeze(0).to(device)
        image_cu0 = x_cu0["image"].unsqueeze(0).to(device)
        image_cu1 = x_cu1["image"].unsqueeze(0).to(device)
        t_cu0 = x_cu0["hidden_target"].unsqueeze(0).to(device)
        t_cu1 = x_cu1["hidden_target"].unsqueeze(0).to(device)

        with torch.no_grad():
            pA_im0 = modelA(cue_im0, image_fixed)
            pA_im1 = modelA(cue_im1, image_fixed)
            pA_cu0 = modelA(cue_fixed, image_cu0)
            pA_cu1 = modelA(cue_fixed, image_cu1)

            pB_img = modelB_img(image_fixed)
            pB_cue = modelB_cue(cue_fixed)

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
        "seed": int(cfg.seed),
    }


def train(args) -> None:
    _seed_everything(int(args.seed))
    device = torch.device(args.device)

    modelA = V8DoubleBarrierCausalJEPA().to(device)
    modelB_img = V8ImageOnlyBaseline().to(device)
    modelB_cue = V8CueOnlyBaseline().to(device)

    optA = torch.optim.Adam(modelA.parameters(), lr=float(args.lr))
    optB_img = torch.optim.Adam(modelB_img.parameters(), lr=float(args.lr))
    optB_cue = torch.optim.Adam(modelB_cue.parameters(), lr=float(args.lr))

    steps = int(args.steps)
    batch_ctx = int(args.batch_size)
    train_ood_ratio = float(args.train_ood_ratio)
    w_jepa = float(args.w_jepa)
    w_pair = float(args.w_pair)
    pos_weight_max = float(args.pos_weight_max)

    print(
        f"Starting Training (V8 Double-Barrier, pair-loss v3, train_ood_ratio={train_ood_ratio:.2f}, "
        f"steps={steps}, seed={args.seed}, device={args.device})..."
    )

    for step in range(steps):
        n_ood = int(round(batch_ctx * train_ood_ratio))
        n_iid = int(batch_ctx - n_ood)

        ctxs = []
        if n_iid > 0:
            ctxs += _sample_ctxs(n=n_iid, seed=int(args.seed + 100000 * step), ood=False, img_size=32)
        if n_ood > 0:
            ctxs += _sample_ctxs(n=n_ood, seed=int(args.seed + 100000 * step + 77777), ood=True, img_size=32)

        mid = len(ctxs) // 2
        ctxs_im = ctxs[:mid]
        ctxs_cu = ctxs[mid:]

        cue_im, image_im, target_im, wrong_im = _make_image_barrier_batch(ctxs_im, device)
        cue_cu, image_cu, target_cu, wrong_cu = _make_cue_barrier_batch(ctxs_cu, device)

        modelA.train()
        pA_im = modelA(cue_im, image_im)
        pA_cu = modelA(cue_cu, image_cu)

        loss_seg_im = _weighted_bce_with_logits(pA_im, target_im, pos_weight_max=pos_weight_max)
        loss_seg_cu = _weighted_bce_with_logits(pA_cu, target_cu, pos_weight_max=pos_weight_max)
        loss_seg = 0.5 * (loss_seg_im + loss_seg_cu)

        loss_pair_im = _pair_rank_loss(pA_im, target_im, wrong_im)
        loss_pair_cu = _pair_rank_loss(pA_cu, target_cu, wrong_cu)
        loss_pair = 0.5 * (loss_pair_im + loss_pair_cu)

        p_full_im, t_full_im, z_im = modelA.jepa_forward(cue_im, image_im, target_im)
        p_full_cu, t_full_cu, z_cu = modelA.jepa_forward(cue_cu, image_cu, target_cu)
        loss_jepa = 0.5 * (v8_jepa_loss(p_full_im, t_full_im, z_im) + v8_jepa_loss(p_full_cu, t_full_cu, z_cu))

        loss_A = loss_seg + w_jepa * loss_jepa + w_pair * loss_pair

        optA.zero_grad()
        loss_A.backward()
        optA.step()
        modelA.ema_update()

        # Baseline training (diagnostic).
        modelB_img.train()
        modelB_cue.train()

        images_all = torch.cat([image_im, image_cu], dim=0)
        cues_all = torch.cat([cue_im, cue_cu], dim=0)
        targets_all = torch.cat([target_im, target_cu], dim=0)

        pB_img = modelB_img(images_all)
        loss_B_img = _weighted_bce_with_logits(pB_img, targets_all, pos_weight_max=pos_weight_max)
        optB_img.zero_grad()
        loss_B_img.backward()
        optB_img.step()

        pB_cue = modelB_cue(cues_all)
        loss_B_cue = _weighted_bce_with_logits(pB_cue, targets_all, pos_weight_max=pos_weight_max)
        optB_cue.zero_grad()
        loss_B_cue.backward()
        optB_cue.step()

        if step % 250 == 0:
            print(
                f"[{step}] A_seg={loss_seg.item():.4f} (im {loss_seg_im.item():.4f} cu {loss_seg_cu.item():.4f}) "
                f"A_pair={loss_pair.item():.4f} JEPA={loss_jepa.item():.4f} | "
                f"B_img={loss_B_img.item():.4f} B_cue={loss_B_cue.item():.4f}"
            )

    # --- Evaluation (IoU + pair-grade) ---
    modelA.eval()
    modelB_img.eval()
    modelB_cue.eval()

    def eval_iou(*, ood: bool) -> tuple[float, float, float]:
        ctxs_eval = _sample_ctxs(n=256, seed=int(args.seed + (999999 if ood else 111111)), ood=ood, img_size=32)
        cues, images, targets = [], [], []
        for ctx in ctxs_eval:
            for h in (0, 1):
                for k in (0, 1):
                    x = render(ctx, h=h, k=k)
                    cues.append(x["cue_image"])
                    images.append(x["image"])
                    targets.append(x["hidden_target"])

        cue = _stack(cues, device)
        image = _stack(images, device)
        target = _stack(targets, device)

        with torch.no_grad():
            oA = modelA(cue, image)
            oB_img = modelB_img(image)
            oB_cue = modelB_cue(cue)

        return calculate_iou(oA, target), calculate_iou(oB_img, target), calculate_iou(oB_cue, target)

    iidA, iidB_img, iidB_cue = eval_iou(ood=False)
    oodA, oodB_img, oodB_cue = eval_iou(ood=True)

    pair_cfg = PairEvalCfg(n_ctx=int(args.pair_n_ctx), seed=int(args.pair_seed), img_size=32)
    pair_iid = _pair_eval_one(modelA=modelA, modelB_img=modelB_img, modelB_cue=modelB_cue, device=device, cfg=pair_cfg, ood=False)
    pair_ood = _pair_eval_one(modelA=modelA, modelB_img=modelB_img, modelB_cue=modelB_cue, device=device, cfg=pair_cfg, ood=True)

    print("\n--- EVALUATION (diagnostic IoU) ---")
    print(f"IID  -> A_IoU: {iidA:.4f} | B_img_IoU: {iidB_img:.4f} | B_cue_IoU: {iidB_cue:.4f}")
    print(f"OOD  -> A_IoU: {oodA:.4f} | B_img_IoU: {oodB_img:.4f} | B_cue_IoU: {oodB_cue:.4f}")

    print("\n--- PAIR EVAL (COFRS-grade, double barrier) ---")
    print(
        "PAIR IID -> "
        f"img_barrier={pair_iid['obs_image_barrier_ok']} cue_barrier={pair_iid['obs_cue_barrier_ok']} "
        f"A_img={pair_iid['A_both_image_pair_rate']:.4f} A_cue={pair_iid['A_both_cue_pair_rate']:.4f} "
        f"B_img_both={pair_iid['B_image_only_both_rate']:.4f} B_cue_both={pair_iid['B_cue_only_both_rate']:.4f}"
    )
    print(
        "PAIR OOD -> "
        f"img_barrier={pair_ood['obs_image_barrier_ok']} cue_barrier={pair_ood['obs_cue_barrier_ok']} "
        f"A_img={pair_ood['A_both_image_pair_rate']:.4f} A_cue={pair_ood['A_both_cue_pair_rate']:.4f} "
        f"B_img_both={pair_ood['B_image_only_both_rate']:.4f} B_cue_both={pair_ood['B_cue_only_both_rate']:.4f}"
    )

    if args.out_jsonl:
        row = {
            "kind": "aslmt_v8_double_barrier_hidden_target_pair_trainood_pairloss_v3",
            "steps": int(args.steps),
            "seed": int(args.seed),
            "cfg": {
                "batch_size": int(args.batch_size),
                "lr": float(args.lr),
                "w_jepa": float(args.w_jepa),
                "w_pair": float(args.w_pair),
                "pos_weight_max": float(args.pos_weight_max),
                "train_ood_ratio": float(args.train_ood_ratio),
            },
            "iid": {"A_IoU": iidA, "B_img_IoU": iidB_img, "B_cue_IoU": iidB_cue},
            "ood": {"A_IoU": oodA, "B_img_IoU": oodB_img, "B_cue_IoU": oodB_cue},
            "pair_eval": {"iid": pair_iid, "ood": pair_ood},
        }
        with open(args.out_jsonl, "a", encoding="utf-8") as f:
            f.write(json.dumps(row) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--steps", type=int, default=3000)
    parser.add_argument("--batch-size", type=int, default=128)
    parser.add_argument("--lr", type=float, default=1e-3)
    parser.add_argument("--w-jepa", type=float, default=0.1)
    parser.add_argument("--w-pair", type=float, default=0.2)
    parser.add_argument("--pos-weight-max", type=float, default=20.0)
    parser.add_argument("--train-ood-ratio", type=float, default=1.0)
    parser.add_argument("--device", type=str, default="cpu")
    parser.add_argument("--out-jsonl", type=str, default="v8_master.jsonl")
    parser.add_argument("--pair-n-ctx", type=int, default=64)
    parser.add_argument("--pair-seed", type=int, default=0)
    args = parser.parse_args()
    train(args)
