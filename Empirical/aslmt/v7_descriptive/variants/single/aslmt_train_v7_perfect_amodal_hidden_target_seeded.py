import argparse
import json
import random
import torch
import torch.nn.functional as F

from aslmt_env_v7_perfect_amodal_hidden_target import get_dataloaders
from aslmt_model_v7_perfect_jepa import V7PerfectAmodalCausalJEPA, V7PerfectVisibleOnlyBaseline


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

    print("\n--- EVALUATION ---")
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

    def run_audits(dl):
        acc_abl = []
        swap_orig = []
        swap_perm = []
        jepa_orig = []
        jepa_perm = []
        for batch in dl:
            cue = batch["cue_image"].to(device)
            image = batch["image"].to(device)
            target = batch["hidden_target"].to(device)
            perm = torch.randperm(image.shape[0], device=device)
            target_perm = target[perm]
            with torch.no_grad():
                oA_abl = modelA.ablated_forward(cue, image)
                acc_abl.append(calculate_iou(oA_abl, target))
                oA_swap = modelA.swap_forward(cue, image, perm)
                swap_orig.append(calculate_iou(oA_swap, target))
                swap_perm.append(calculate_iou(oA_swap, target_perm))
                pred, targ, _ = modelA.jepa_forward(cue, image, target)
                jepa_orig.append(float((pred * targ).sum(dim=-1).mean().item()))
                jepa_perm.append(float((pred * targ[perm]).sum(dim=-1).mean().item()))
        return {
            "A_IoU_ablated": sum(acc_abl) / len(acc_abl),
            "swap_vs_orig": sum(swap_orig) / len(swap_orig),
            "swap_vs_perm": sum(swap_perm) / len(swap_perm),
            "jepa_match_orig": sum(jepa_orig) / len(jepa_orig),
            "jepa_match_perm": sum(jepa_perm) / len(jepa_perm),
        }

    audit = run_audits(ood_dl)
    audit["ablation_drop"] = oodA - audit["A_IoU_ablated"]
    print(f"A_IoU (Ablated z): {audit['A_IoU_ablated']:.4f} (Drop: {audit['ablation_drop']:.4f})")
    print(f"Swap vs Original : {audit['swap_vs_orig']:.4f}")
    print(f"Swap vs Permuted : {audit['swap_vs_perm']:.4f}")
    print(f"JEPA margin      : {audit['jepa_match_orig'] - audit['jepa_match_perm']:.4f}")

    if args.out_jsonl:
        row = {
            "kind": "aslmt_v7_perfect_amodal_hidden_target",
            "steps": int(args.steps),
            "seed": int(args.seed),
            "cfg": {"batch_size": int(args.batch_size), "lr": float(args.lr), "w_jepa": float(args.w_jepa)},
            "iid": {"A_IoU": iidA, "B_IoU": iidB},
            "ood": {"A_IoU": oodA, "B_IoU": oodB, "audit": audit},
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
    args = parser.parse_args()
    train(args)

