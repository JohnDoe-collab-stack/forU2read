import argparse
import json
import random
from dataclasses import asdict, dataclass

import torch
import torch.nn.functional as F
from torch.utils.data import DataLoader, Dataset

from aslmt_env_v7_perfect_amodal_hidden_target import PerfectAmodalHiddenTargetSequenceDataset
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
    """
    Threshold-free score used only to decide between the two paired targets.
    true_mask is {0,1}. score is sum(sigmoid(pred) * true_mask).
    """
    return (torch.sigmoid(pred_logits) * true_mask).sum(dim=(1, 2, 3))


@dataclass(frozen=True)
class PairEvalCfg:
    n_ctx: int = 64
    seed: int = 0
    img_size: int = 32


def _sample_ctxs(*, n: int, seed: int, ood: bool, img_size: int) -> list[Ctx]:
    g = torch.Generator()
    g.manual_seed(int(seed))

    # Match v7 env ranges.
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
                # Per-ctx deterministic nuisance seed for OOD cue flips.
                seed=int(seed + i),
            )
        )
    return out


def _pair_eval_one(
    *,
    modelA: V7PerfectAmodalCausalJEPA,
    modelB: V7PerfectVisibleOnlyBaseline,
    device: torch.device,
    cfg: PairEvalCfg,
    ood: bool,
) -> dict:
    """
    Returns the usual pair_eval summary keys plus an audit list `A_fail_ctxs`:
    each element is a dict describing a context where A failed the both-correct condition,
    including the four overlap scores and margins.
    """
    ctxs = _sample_ctxs(n=int(cfg.n_ctx), seed=int(cfg.seed), ood=bool(ood), img_size=int(cfg.img_size))

    obs_barrier_ok = True
    A_both_correct = 0
    B_both_correct = 0

    A_fail_ctxs: list[dict] = []

    for ctx in ctxs:
        x0 = render(ctx, hidden_label=0)
        x1 = render(ctx, hidden_label=1)

        # COFRS fiber witness: same decision-time obs, different hidden target.
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

        # Decide label by comparing overlap to the two paired targets (threshold-free).
        sA00 = float(_overlap_score(pA0, t0).item())
        sA01 = float(_overlap_score(pA0, t1).item())
        sA11 = float(_overlap_score(pA1, t1).item())
        sA10 = float(_overlap_score(pA1, t0).item())
        mA0 = float(sA00 - sA01)
        mA1 = float(sA11 - sA10)

        A0_correct = bool(mA0 > 0.0)
        A1_correct = bool(mA1 > 0.0)
        if A0_correct and A1_correct:
            A_both_correct += 1
        else:
            A_fail_ctxs.append(
                {
                    "ctx": asdict(ctx),
                    "A0_correct": bool(A0_correct),
                    "A1_correct": bool(A1_correct),
                    "scores": {"sA00": sA00, "sA01": sA01, "sA11": sA11, "sA10": sA10},
                    "margins": {"mA0": mA0, "mA1": mA1},
                }
            )

        # Visible-only baseline outputs the same pB for both paired members; it cannot be correct on both if targets differ.
        sB0 = float(_overlap_score(pB, t0).item())
        sB1 = float(_overlap_score(pB, t1).item())
        B0_correct = bool(sB0 > sB1)
        B1_correct = bool(sB1 > sB0)
        if B0_correct and B1_correct:
            B_both_correct += 1

    n = int(cfg.n_ctx)
    return {
        "n_ctx": int(cfg.n_ctx),
        "ood": bool(ood),
        "obs_barrier_ok": bool(obs_barrier_ok),
        "A_both_correct_rate": float(A_both_correct) / float(n),
        "B_both_correct_rate": float(B_both_correct) / float(n),
        "seed": int(cfg.seed),
        # Extra diagnostics (ignored by the strict verifier).
        "A_fail_ctxs": A_fail_ctxs,
    }


class _FrontierIidDataset(Dataset):
    """
    Minimal constructive coverage for the IID frontier identified by ctx-audit:
    (occ_half=5, t=2) with cx,cy in the usual IID range.

    This is used to test "frontier injection": keep training almost entirely OOD,
    but inject a small fraction of these IID frontier contexts.
    """

    def __init__(self, *, size: int, seed: int, img_size: int = 32, occ_half: int = 5, t: int = 2):
        self.size = int(size)
        self.seed = int(seed)
        self.img_size = int(img_size)
        self.occ_half = int(occ_half)
        self.t = int(t)

    def __len__(self) -> int:
        return self.size

    def __getitem__(self, idx: int) -> dict[str, torch.Tensor]:
        g = torch.Generator()
        g.manual_seed(int(self.seed + idx))
        cx = int(torch.randint(low=12, high=21, size=(1,), generator=g).item())
        cy = int(torch.randint(low=12, high=21, size=(1,), generator=g).item())
        hidden_label = int(torch.randint(low=0, high=2, size=(1,), generator=g).item())
        ctx = Ctx(
            cx=int(cx),
            cy=int(cy),
            t=int(self.t),
            occ_half=int(self.occ_half),
            img_size=int(self.img_size),
            ood=False,
            seed=int(self.seed + idx),
        )
        return render(ctx, hidden_label=hidden_label)


def _make_dataloaders(
    *, batch_size: int, steps: int, train_ood_ratio: float, frontier_frac: float
) -> tuple[DataLoader, DataLoader, DataLoader]:
    """
    Training coverage for the declared OOD family, with optional IID "frontier injection".

    - train_ood_ratio=1.0 means: base training on OOD only.
    - frontier_frac>0 means: replace a small fraction of the *training* examples with IID frontier contexts
      (occ_half=5, t=2), regardless of train_ood_ratio.

    This does not change evaluation; it only tests whether a minimal constructive IID support suffices
    to close the strict OOD-required verifier under near-OOD training.
    """
    batch_size = int(batch_size)
    steps = int(steps)
    train_ood_ratio = float(train_ood_ratio)
    train_ood_ratio = max(0.0, min(1.0, train_ood_ratio))
    frontier_frac = float(frontier_frac)
    frontier_frac = max(0.0, min(1.0, frontier_frac))

    n_train = batch_size * steps

    # Baseline split per train_ood_ratio (as in the canonical ctx-audit script).
    n_ood = int(round(n_train * train_ood_ratio))
    n_iid = int(n_train - n_ood)

    # Frontier injection: allocate from the total training budget, and subtract from the OOD portion first.
    n_frontier = int(round(n_train * frontier_frac))
    n_frontier = max(0, min(n_train, n_frontier))
    n_ood = max(0, n_ood - n_frontier)

    iid_ds = PerfectAmodalHiddenTargetSequenceDataset(size=1024, ood=False)
    ood_ds = PerfectAmodalHiddenTargetSequenceDataset(size=1024, ood=True)

    train_parts = []
    if n_iid > 0:
        train_parts.append(PerfectAmodalHiddenTargetSequenceDataset(size=n_iid, ood=False))
    if n_ood > 0:
        train_parts.append(PerfectAmodalHiddenTargetSequenceDataset(size=n_ood, ood=True))
    if n_frontier > 0:
        train_parts.append(_FrontierIidDataset(size=n_frontier, seed=0, img_size=32, occ_half=5, t=2))

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
    batch_size = int(args.batch_size)
    train_dl, iid_dl, ood_dl = _make_dataloaders(
        batch_size=batch_size,
        steps=int(args.steps),
        train_ood_ratio=float(args.train_ood_ratio),
        frontier_frac=float(args.frontier_frac),
    )

    modelA = V7PerfectAmodalCausalJEPA().to(device)
    modelB = V7PerfectVisibleOnlyBaseline().to(device)

    optA = torch.optim.Adam(modelA.parameters(), lr=float(args.lr))
    optB = torch.optim.Adam(modelB.parameters(), lr=float(args.lr))

    print(
        f"Starting Training (V7 Perfect Amodal Hidden-Target, pair-grade, train_ood_ratio={float(args.train_ood_ratio):.2f}, "
        f"frontier_frac={float(args.frontier_frac):.4f}, steps={args.steps}, seed={args.seed}, device={args.device})..."
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

    print("\n--- PAIR EVAL (COFRS-grade, binary) ---")
    pair_cfg = PairEvalCfg(n_ctx=int(args.pair_n_ctx), seed=int(args.pair_seed), img_size=32)
    pair_iid = _pair_eval_one(modelA=modelA, modelB=modelB, device=device, cfg=pair_cfg, ood=False)
    pair_ood = _pair_eval_one(modelA=modelA, modelB=modelB, device=device, cfg=pair_cfg, ood=True)
    print(
        f"PAIR IID -> obs_barrier_ok={pair_iid['obs_barrier_ok']} A_both={pair_iid['A_both_correct_rate']:.4f} "
        f"B_both={pair_iid['B_both_correct_rate']:.4f}"
    )
    print(
        f"PAIR OOD -> obs_barrier_ok={pair_ood['obs_barrier_ok']} A_both={pair_ood['A_both_correct_rate']:.4f} "
        f"B_both={pair_ood['B_both_correct_rate']:.4f}"
    )

    if args.out_jsonl:
        row = {
            "kind": "aslmt_v7_perfect_amodal_hidden_target_pair_trainood_ctxaudit_frontier_inject",
            "steps": int(args.steps),
            "seed": int(args.seed),
            "cfg": {
                "batch_size": int(args.batch_size),
                "lr": float(args.lr),
                "w_jepa": float(args.w_jepa),
                "train_ood_ratio": float(args.train_ood_ratio),
                "frontier_frac": float(args.frontier_frac),
                "frontier_occ_half": 5,
                "frontier_t": 2,
            },
            "iid": {"A_IoU": float(iidA), "B_IoU": float(iidB)},
            "ood": {"A_IoU": float(oodA), "B_IoU": float(oodB)},
            "pair_eval": {"iid": pair_iid, "ood": pair_ood},
        }
        with open(args.out_jsonl, "w", encoding="utf-8") as f:
            f.write(json.dumps(row) + "\n")


def main() -> None:
    p = argparse.ArgumentParser(description="V7 pair-grade train-coverage + ctx-audit + frontier injection.")
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--steps", type=int, default=3000)
    p.add_argument("--batch-size", type=int, default=128)
    p.add_argument("--lr", type=float, default=1e-3)
    p.add_argument("--w-jepa", type=float, default=0.1)
    p.add_argument("--train-ood-ratio", type=float, default=1.0)
    p.add_argument("--frontier-frac", type=float, default=0.0, help="Fraction of training examples forced to IID frontier (occ_half=5, t=2).")
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--out-jsonl", type=str, default="v7_master.jsonl")
    p.add_argument("--pair-n-ctx", type=int, default=64)
    p.add_argument("--pair-seed", type=int, default=0)
    args = p.parse_args()
    train(args)


if __name__ == "__main__":
    main()

