import argparse
import json
import random
from dataclasses import dataclass

import torch
import torch.nn.functional as F

from aslmt_env_v7_perfect_amodal_hidden_target import get_dataloaders
from aslmt_model_v7_perfect_jepa import V7PerfectAmodalCausalJEPA, V7PerfectVisibleOnlyBaseline
from render_v7_paired_ctx import Ctx, render


def v7_jepa_loss(pred_latent: torch.Tensor, target_latent: torch.Tensor, z: torch.Tensor) -> torch.Tensor:
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
    # Threshold-free overlap score used only to compare paired targets.
    return (torch.sigmoid(pred_logits) * true_mask).sum(dim=(1, 2, 3))


@dataclass(frozen=True)
class PairEvalCfg:
    n_ctx: int = 64
    seed: int = 0
    img_size: int = 32


def _sample_ctxs(*, n: int, seed: int, img_size: int) -> list[Ctx]:
    g = torch.Generator()
    g.manual_seed(int(seed))

    # IID ranges only (COFRS-grade witness does not depend on an OOD distribution).
    cx = torch.randint(low=12, high=21, size=(n,), generator=g).tolist()
    cy = torch.randint(low=12, high=21, size=(n,), generator=g).tolist()
    t = torch.randint(low=2, high=4, size=(n,), generator=g).tolist()  # 2..3
    occ_half = torch.randint(low=5, high=7, size=(n,), generator=g).tolist()  # 5..6

    out: list[Ctx] = []
    for i in range(n):
        out.append(Ctx(cx=int(cx[i]), cy=int(cy[i]), t=int(t[i]), occ_half=int(occ_half[i]), img_size=int(img_size), ood=False, seed=int(seed + i)))
    return out


def _pair_eval_iid_only(
    *,
    modelA: V7PerfectAmodalCausalJEPA,
    modelB: V7PerfectVisibleOnlyBaseline,
    device: torch.device,
    cfg: PairEvalCfg,
) -> dict:
    ctxs = _sample_ctxs(n=int(cfg.n_ctx), seed=int(cfg.seed), img_size=int(cfg.img_size))

    obs_barrier_ok = True
    A_both_correct = 0
    B_both_correct = 0

    for ctx in ctxs:
        x0 = render(ctx, hidden_label=0)
        x1 = render(ctx, hidden_label=1)

        obs_barrier_ok = bool(
            obs_barrier_ok and torch.equal(x0["image"], x1["image"]) and (not torch.equal(x0["hidden_target"], x1["hidden_target"]))
        )

        cue0 = x0["cue_image"].unsqueeze(0).to(device)
        cue1 = x1["cue_image"].unsqueeze(0).to(device)
        image = x0["image"].unsqueeze(0).to(device)
        t0 = x0["hidden_target"].unsqueeze(0).to(device)
        t1 = x1["hidden_target"].unsqueeze(0).to(device)

        with torch.no_grad():
            pA0 = modelA(cue0, image)
            pA1 = modelA(cue1, image)
            pB = modelB(image)

        A0_correct = bool(_overlap_score(pA0, t0) > _overlap_score(pA0, t1))
        A1_correct = bool(_overlap_score(pA1, t1) > _overlap_score(pA1, t0))
        if A0_correct and A1_correct:
            A_both_correct += 1

        B0_correct = bool(_overlap_score(pB, t0) > _overlap_score(pB, t1))
        B1_correct = bool(_overlap_score(pB, t1) > _overlap_score(pB, t0))
        if B0_correct and B1_correct:
            B_both_correct += 1

    n = int(cfg.n_ctx)
    return {
        "n_ctx": n,
        "ood": False,
        "obs_barrier_ok": bool(obs_barrier_ok),
        "A_both_correct_rate": float(A_both_correct) / float(n),
        "B_both_correct_rate": float(B_both_correct) / float(n),
        "seed": int(cfg.seed),
    }


def train(args) -> None:
    _seed_everything(int(args.seed))
    device = torch.device(args.device)
    batch_size = int(args.batch_size)
    train_dl, iid_dl, ood_dl = get_dataloaders(batch_size=batch_size, steps=int(args.steps))

    modelA = V7PerfectAmodalCausalJEPA().to(device)
    modelB = V7PerfectVisibleOnlyBaseline().to(device)

    optA = torch.optim.Adam(modelA.parameters(), lr=float(args.lr))
    optB = torch.optim.Adam(modelB.parameters(), lr=float(args.lr))

    print(
        f"Starting Training (V7 Perfect Amodal Hidden-Target, steps={args.steps}, seed={args.seed}, device={args.device})..."
    )
    modelA.train()
    modelB.train()
    for batch_idx, batch in enumerate(train_dl):
        cue = batch["cue_image"].to(device)
        image = batch["image"].to(device)
        target = batch["hidden_target"].to(device)

        out_A = modelA(cue, image)
        loss_seg_A = F.binary_cross_entropy_with_logits(out_A, target)
        p_full, t_full, z = modelA.jepa_forward(cue, image, target)
        loss_jepa = v7_jepa_loss(p_full, t_full, z)
        loss_A = loss_seg_A + float(args.w_jepa) * loss_jepa
        optA.zero_grad()
        loss_A.backward()
        optA.step()
        modelA.ema_update()

        out_B = modelB(image)
        loss_B = F.binary_cross_entropy_with_logits(out_B, target)
        optB.zero_grad()
        loss_B.backward()
        optB.step()

        if batch_idx % 250 == 0:
            print(f"[{batch_idx}] M_A: {loss_seg_A.item():.4f} (JEPA {loss_jepa.item():.4f}) | M_B: {loss_B.item():.4f}")

    print("\n--- EVALUATION (diagnostic) ---")
    modelA.eval()
    modelB.eval()

    def eval_loop(dl):
        accA, accB = [], []
        for batch in dl:
            cue = batch["cue_image"].to(device)
            image = batch["image"].to(device)
            target = batch["hidden_target"].to(device)
            with torch.no_grad():
                oA = modelA(cue, image)
                oB = modelB(image)
            accA.append(calculate_iou(oA, target))
            accB.append(calculate_iou(oB, target))
        return sum(accA) / len(accA), sum(accB) / len(accB)

    iidA, iidB = eval_loop(iid_dl)
    oodA, oodB = eval_loop(ood_dl)
    print(f"IID  -> A_IoU: {iidA:.4f} | B_IoU: {iidB:.4f}")
    print(f"OOD  -> A_IoU: {oodA:.4f} | B_IoU: {oodB:.4f}")

    print("\n--- PAIR EVAL (COFRS-grade, IID only, binary) ---")
    pair_cfg = PairEvalCfg(n_ctx=int(args.pair_n_ctx), seed=int(args.pair_seed), img_size=32)
    pair_iid = _pair_eval_iid_only(modelA=modelA, modelB=modelB, device=device, cfg=pair_cfg)
    print(f"PAIR IID -> obs_barrier_ok={pair_iid['obs_barrier_ok']} A_both={pair_iid['A_both_correct_rate']:.4f} B_both={pair_iid['B_both_correct_rate']:.4f}")

    if args.out_jsonl:
        row = {
            "kind": "aslmt_v7_perfect_amodal_hidden_target_pair_iidonly",
            "steps": int(args.steps),
            "seed": int(args.seed),
            "cfg": {"batch_size": int(args.batch_size), "lr": float(args.lr), "w_jepa": float(args.w_jepa)},
            "iid": {"A_IoU": iidA, "B_IoU": iidB},
            "ood": {"A_IoU": oodA, "B_IoU": oodB},
            "pair_eval": {"iid": pair_iid},
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
    parser.add_argument("--device", type=str, default="cpu")
    parser.add_argument("--out-jsonl", type=str, default="v7_master.jsonl")
    parser.add_argument("--pair-n-ctx", type=int, default=64)
    parser.add_argument("--pair-seed", type=int, default=0)
    args = parser.parse_args()
    train(args)

