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
                # Deterministic nuisance seed; must be independent of k for cue-barrier.
                seed=int(seed + i),
            )
        )
    return out


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

    for i, ctx in enumerate(ctxs):
        # Choose fixed bits deterministically per ctx so we do not accidentally pick a degenerate sub-family.
        k_fixed = int((ctx.seed + 0) % 2)
        h_fixed = int((ctx.seed + 1) % 2)

        # Image barrier: same image (k fixed), different targets (flip h).
        x_im0 = render(ctx, h=0, k=k_fixed)
        x_im1 = render(ctx, h=1, k=k_fixed)
        obs_image_barrier_ok = bool(
            obs_image_barrier_ok
            and torch.equal(x_im0["image"], x_im1["image"])
            and (not torch.equal(x_im0["hidden_target"], x_im1["hidden_target"]))
        )

        # Cue barrier: same cue (h fixed), different targets (flip k).
        x_cu0 = render(ctx, h=h_fixed, k=0)
        x_cu1 = render(ctx, h=h_fixed, k=1)
        obs_cue_barrier_ok = bool(
            obs_cue_barrier_ok
            and torch.equal(x_cu0["cue_image"], x_cu1["cue_image"])
            and (not torch.equal(x_cu0["hidden_target"], x_cu1["hidden_target"]))
        )

        # --- Evaluate A on both pairs ---
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

        # Image-only baseline can only output one prediction for the image-barrier pair.
        B_im0_correct = bool(_overlap_score(pB_img, t_im0) > _overlap_score(pB_img, t_im1))
        B_im1_correct = bool(_overlap_score(pB_img, t_im1) > _overlap_score(pB_img, t_im0))
        if B_im0_correct and B_im1_correct:
            B_img_both += 1

        # Cue-only baseline can only output one prediction for the cue-barrier pair.
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


def _make_dataloaders(*, batch_size: int, steps: int, train_ood_ratio: float) -> tuple[DataLoader, DataLoader, DataLoader]:
    batch_size = int(batch_size)
    steps = int(steps)
    train_ood_ratio = float(train_ood_ratio)
    train_ood_ratio = max(0.0, min(1.0, train_ood_ratio))

    n_train = batch_size * steps
    n_ood = int(round(n_train * train_ood_ratio))
    n_iid = int(n_train - n_ood)

    iid_ds = DoubleBarrierHiddenTargetSequenceDataset(size=1024, ood=False)
    ood_ds = DoubleBarrierHiddenTargetSequenceDataset(size=1024, ood=True)

    train_parts = []
    if n_iid > 0:
        train_parts.append(DoubleBarrierHiddenTargetSequenceDataset(size=n_iid, ood=False))
    if n_ood > 0:
        train_parts.append(DoubleBarrierHiddenTargetSequenceDataset(size=n_ood, ood=True))

    if len(train_parts) == 1:
        train_ds = train_parts[0]
    else:
        train_ds = torch.utils.data.ConcatDataset(train_parts)

    train_dl = DataLoader(train_ds, batch_size=batch_size, shuffle=True)
    iid_dl = DataLoader(iid_ds, batch_size=1024, shuffle=False)
    ood_dl = DataLoader(ood_ds, batch_size=1024, shuffle=False)
    return train_dl, iid_dl, ood_dl


def train(args) -> None:
    _seed_everything(int(args.seed))
    device = torch.device(args.device)

    train_dl, iid_dl, ood_dl = _make_dataloaders(batch_size=int(args.batch_size), steps=int(args.steps), train_ood_ratio=float(args.train_ood_ratio))

    modelA = V8DoubleBarrierCausalJEPA().to(device)
    modelB_img = V8ImageOnlyBaseline().to(device)
    modelB_cue = V8CueOnlyBaseline().to(device)

    optA = torch.optim.Adam(modelA.parameters(), lr=float(args.lr))
    optB_img = torch.optim.Adam(modelB_img.parameters(), lr=float(args.lr))
    optB_cue = torch.optim.Adam(modelB_cue.parameters(), lr=float(args.lr))

    print(
        f"Starting Training (V8 Double-Barrier Hidden-Target, pair-grade, train_ood_ratio={float(args.train_ood_ratio):.2f}, "
        f"steps={args.steps}, seed={args.seed}, device={args.device})..."
    )

    modelA.train()
    modelB_img.train()
    modelB_cue.train()

    for batch_idx, batch in enumerate(train_dl):
        cue = batch["cue_image"].to(device)
        image = batch["image"].to(device)
        target = batch["hidden_target"].to(device)

        out_A = modelA(cue, image)
        loss_seg_A = F.binary_cross_entropy_with_logits(out_A, target)
        p_full, t_full, z = modelA.jepa_forward(cue, image, target)
        loss_jepa = v8_jepa_loss(p_full, t_full, z)
        loss_A = loss_seg_A + float(args.w_jepa) * loss_jepa
        optA.zero_grad()
        loss_A.backward()
        optA.step()
        modelA.ema_update()

        out_B_img = modelB_img(image)
        loss_B_img = F.binary_cross_entropy_with_logits(out_B_img, target)
        optB_img.zero_grad()
        loss_B_img.backward()
        optB_img.step()

        out_B_cue = modelB_cue(cue)
        loss_B_cue = F.binary_cross_entropy_with_logits(out_B_cue, target)
        optB_cue.zero_grad()
        loss_B_cue.backward()
        optB_cue.step()

        if batch_idx % 250 == 0:
            print(
                f"[{batch_idx}] A_seg: {loss_seg_A.item():.4f} (JEPA {loss_jepa.item():.4f}) | "
                f"B_img: {loss_B_img.item():.4f} | B_cue: {loss_B_cue.item():.4f}"
            )

    print("\n--- EVALUATION (diagnostic IoU) ---")
    modelA.eval()
    modelB_img.eval()
    modelB_cue.eval()

    def eval_loop(dl):
        accA, accB_img, accB_cue = [], [], []
        for batch in dl:
            cue = batch["cue_image"].to(device)
            image = batch["image"].to(device)
            target = batch["hidden_target"].to(device)
            with torch.no_grad():
                oA = modelA(cue, image)
                oB_img = modelB_img(image)
                oB_cue = modelB_cue(cue)
            accA.append(calculate_iou(oA, target))
            accB_img.append(calculate_iou(oB_img, target))
            accB_cue.append(calculate_iou(oB_cue, target))
        return sum(accA) / len(accA), sum(accB_img) / len(accB_img), sum(accB_cue) / len(accB_cue)

    iidA, iidB_img, iidB_cue = eval_loop(iid_dl)
    oodA, oodB_img, oodB_cue = eval_loop(ood_dl)
    print(f"IID  -> A_IoU: {iidA:.4f} | B_img_IoU: {iidB_img:.4f} | B_cue_IoU: {iidB_cue:.4f}")
    print(f"OOD  -> A_IoU: {oodA:.4f} | B_img_IoU: {oodB_img:.4f} | B_cue_IoU: {oodB_cue:.4f}")

    print("\n--- PAIR EVAL (COFRS-grade, double barrier) ---")
    pair_cfg = PairEvalCfg(n_ctx=int(args.pair_n_ctx), seed=int(args.pair_seed), img_size=32)
    pair_iid = _pair_eval_one(modelA=modelA, modelB_img=modelB_img, modelB_cue=modelB_cue, device=device, cfg=pair_cfg, ood=False)
    pair_ood = _pair_eval_one(modelA=modelA, modelB_img=modelB_img, modelB_cue=modelB_cue, device=device, cfg=pair_cfg, ood=True)

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
            "kind": "aslmt_v8_double_barrier_hidden_target_pair_trainood",
            "steps": int(args.steps),
            "seed": int(args.seed),
            "cfg": {
                "batch_size": int(args.batch_size),
                "lr": float(args.lr),
                "w_jepa": float(args.w_jepa),
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
    parser.add_argument("--train-ood-ratio", type=float, default=1.0)
    parser.add_argument("--device", type=str, default="cpu")
    parser.add_argument("--out-jsonl", type=str, default="v8_master.jsonl")
    parser.add_argument("--pair-n-ctx", type=int, default=64)
    parser.add_argument("--pair-seed", type=int, default=0)
    args = parser.parse_args()
    train(args)
