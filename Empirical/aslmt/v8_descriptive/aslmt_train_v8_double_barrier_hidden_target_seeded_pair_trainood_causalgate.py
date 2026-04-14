import argparse
import json
import random
from dataclasses import dataclass

import torch
import torch.nn.functional as F
from torch.utils.data import DataLoader

from aslmt_env_v8_double_barrier_hidden_target import DoubleBarrierHiddenTargetSequenceDataset
from aslmt_model_v8_double_barrier_jepa import V8DoubleBarrierCausalJEPA, V8CueOnlyBaseline, V8ImageOnlyBaseline
from render_v8_paired_ctx import Ctx, render


def _seed_everything(seed: int) -> None:
    seed = int(seed)
    random.seed(seed)
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)


def _overlap_score(pred_logits: torch.Tensor, true_mask: torch.Tensor) -> torch.Tensor:
    return (torch.sigmoid(pred_logits) * true_mask).sum(dim=(1, 2, 3))


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


def _pair_eval_one(*, modelA: V8DoubleBarrierCausalJEPA, modelB_img: V8ImageOnlyBaseline, modelB_cue: V8CueOnlyBaseline, device: torch.device, cfg: PairEvalCfg, ood: bool) -> dict:
    ctxs = _sample_ctxs(n=int(cfg.n_ctx), seed=int(cfg.seed), ood=bool(ood), img_size=int(cfg.img_size))

    obs_image_barrier_ok = True
    obs_cue_barrier_ok = True

    A_both_image = 0
    A_both_cue = 0
    B_img_both = 0
    B_cue_both = 0

    # Causal gates on image-barrier pairs.
    A_abl_both_image = 0
    A_swap_follow_image = 0
    A_swap_orig_both_image = 0

    for ctx in ctxs:
        k_fixed = int((ctx.seed + 0) % 2)
        h0 = int((ctx.seed + 0) % 2)
        h1 = 1 - h0
        h_fixed = int((ctx.seed + 1) % 2)

        x_im0 = render(ctx, h=h0, k=k_fixed)
        x_im1 = render(ctx, h=h1, k=k_fixed)
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


def _make_dataloaders(*, batch_size: int, steps: int, train_ood_ratio: float) -> DataLoader:
    batch_size = int(batch_size)
    steps = int(steps)
    train_ood_ratio = max(0.0, min(1.0, float(train_ood_ratio)))

    n_train = batch_size * steps
    n_ood = int(round(n_train * train_ood_ratio))
    n_iid = int(n_train - n_ood)

    train_parts = []
    if n_iid > 0:
        train_parts.append(DoubleBarrierHiddenTargetSequenceDataset(size=n_iid, ood=False))
    if n_ood > 0:
        train_parts.append(DoubleBarrierHiddenTargetSequenceDataset(size=n_ood, ood=True))

    train_ds = train_parts[0] if len(train_parts) == 1 else torch.utils.data.ConcatDataset(train_parts)
    return DataLoader(train_ds, batch_size=batch_size, shuffle=True)


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--snapshot-tag", type=str, default="")
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--steps", type=int, default=3000)
    p.add_argument("--batch-size", type=int, default=128)
    p.add_argument("--lr", type=float, default=1e-3)
    p.add_argument("--w-jepa", type=float, default=0.1)
    p.add_argument("--train-ood-ratio", type=float, default=0.5)
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--out-jsonl", type=str, required=True)
    args = p.parse_args()

    _seed_everything(int(args.seed))
    device = torch.device(args.device)

    print(
        f"Starting Training (V8 pair-grade OOD-required + causal gates, train_ood_ratio={float(args.train_ood_ratio):.2f}, "
        f"steps={int(args.steps)}, seed={int(args.seed)}, device={args.device})..."
    )

    train_dl = _make_dataloaders(batch_size=int(args.batch_size), steps=int(args.steps), train_ood_ratio=float(args.train_ood_ratio))

    modelA = V8DoubleBarrierCausalJEPA().to(device)
    modelB_img = V8ImageOnlyBaseline().to(device)
    modelB_cue = V8CueOnlyBaseline().to(device)
    opt = torch.optim.AdamW(list(modelA.parameters()) + list(modelB_img.parameters()) + list(modelB_cue.parameters()), lr=float(args.lr))

    it = iter(train_dl)
    for step in range(int(args.steps)):
        try:
            batch = next(it)
        except StopIteration:
            it = iter(train_dl)
            batch = next(it)

        cue = batch["cue_image"].to(device)
        image = batch["image"].to(device)
        hidden_target = batch["hidden_target"].to(device)
        x_full = torch.clamp(cue + image, 0.0, 1.0)

        pA = modelA(cue, image)
        pB_img = modelB_img(image)
        pB_cue = modelB_cue(cue)

        lossA_seg = F.binary_cross_entropy_with_logits(pA, hidden_target)
        lossB_img = F.binary_cross_entropy_with_logits(pB_img, hidden_target)
        lossB_cue = F.binary_cross_entropy_with_logits(pB_cue, hidden_target)

        pred_lat, tgt_lat, z = modelA.jepa_forward(cue, image, x_full)
        pos = (pred_lat * tgt_lat).sum(dim=-1).mean()
        perm = torch.randperm(pred_lat.size(0), device=pred_lat.device)
        neg = (pred_lat * tgt_lat[perm]).sum(dim=-1).mean()
        std_z = torch.sqrt(z.var(dim=0) + 1e-4)
        var_loss = torch.relu(0.1 - std_z).mean()
        loss_jepa = -(pos) + neg + 10.0 * var_loss

        lossA = lossA_seg + float(args.w_jepa) * loss_jepa
        loss = lossA + lossB_img + lossB_cue

        opt.zero_grad(set_to_none=True)
        loss.backward()
        opt.step()
        modelA.ema_update()

        if step % max(1, int(args.steps) // 12) == 0:
            print(f"[{step}] A_seg={lossA_seg.item():.4f} (JEPA {loss_jepa.item():.4f}) | B_img={lossB_img.item():.4f} | B_cue={lossB_cue.item():.4f}")

    pe_cfg = PairEvalCfg(n_ctx=64, seed=int(args.seed), img_size=32)
    with torch.no_grad():
        pair_iid = _pair_eval_one(modelA=modelA, modelB_img=modelB_img, modelB_cue=modelB_cue, device=device, cfg=pe_cfg, ood=False)
        pair_ood = _pair_eval_one(modelA=modelA, modelB_img=modelB_img, modelB_cue=modelB_cue, device=device, cfg=pe_cfg, ood=True)

    row = {
        "kind": "aslmt_v8_double_barrier_hidden_target_pair_trainood_causalgate",
        "snapshot_tag": str(args.snapshot_tag),
        "steps": int(args.steps),
        "seed": int(args.seed),
        "train_ood_ratio": float(args.train_ood_ratio),
        "pair_eval": {"iid": pair_iid, "ood": pair_ood},
    }
    with open(args.out_jsonl, "a", encoding="utf-8") as f:
        f.write(json.dumps(row) + "\n")

    print("\n--- PAIR EVAL (causal-gated) ---")
    print("IID ->", pair_iid)
    print("OOD ->", pair_ood)


if __name__ == "__main__":
    main()

