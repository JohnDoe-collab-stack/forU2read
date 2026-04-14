#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import time
from dataclasses import asdict
from pathlib import Path

import torch
import torch.nn.functional as F

from aslmt_env_law_v5b_amodal_localclass_family import cfg_by_name
from aslmt_env_law_v5b_amodal_localclass_family import sample_batch
from aslmt_model_law_v5b_amodal_localclass import LawV5bAmodalCausalJEPA, local_baseline_builders


def _timestamp() -> str:
    return time.strftime("%Y-%m-%d %H:%M:%S")


def _sha256_self() -> str:
    p = Path(__file__).resolve()
    h = hashlib.sha256()
    with open(p, "rb") as f:
        while True:
            b = f.read(1 << 20)
            if not b:
                break
            h.update(b)
    return h.hexdigest()


def _calculate_iou(pred_logits: torch.Tensor, true_mask: torch.Tensor) -> float:
    pred_bin = (torch.sigmoid(pred_logits) > 0.5).float()
    inter = (pred_bin * true_mask).sum(dim=(1, 2, 3))
    union = (pred_bin + true_mask).clamp(0, 1).sum(dim=(1, 2, 3))
    return float((inter / (union + 1e-6)).mean().item())


def _v5b_jepa_loss(p_full: torch.Tensor, t_full: torch.Tensor, z: torch.Tensor) -> torch.Tensor:
    pos = (p_full * t_full).sum(dim=-1).mean()
    perm = torch.randperm(p_full.size(0), device=p_full.device)
    neg = (p_full * t_full[perm]).sum(dim=-1).mean()
    std_z = torch.sqrt(z.var(dim=0) + 1e-4)
    var_loss = torch.relu(0.1 - std_z).mean()
    return -(pos) + neg + 10.0 * var_loss


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--snapshot-tag", type=str, required=True)
    ap.add_argument("--seed", type=int, required=True)
    ap.add_argument("--profile", type=str, choices=["smoke", "solid"], default="smoke")
    ap.add_argument("--device", type=str, default="cpu")
    ap.add_argument("--cfg-name", type=str, required=True)
    ap.add_argument("--out-jsonl", type=str, required=True)
    ap.add_argument("--out-txt", type=str, required=True)
    args = ap.parse_args()

    torch.manual_seed(int(args.seed))
    device = str(args.device)

    cfg = cfg_by_name(str(args.cfg_name))
    cfg_dict = asdict(cfg)

    if args.profile == "smoke":
        steps = 2000
        batch_size = 128
        eval_batches = 4
        log_every = 1000
    else:
        steps = 30000
        batch_size = 256
        eval_batches = 8
        log_every = 2000

    # CPU generator for sampling (fast + avoids CUDA generator mismatch).
    g = torch.Generator(device="cpu")
    g.manual_seed(int(args.seed) + 12345)

    modelA = LawV5bAmodalCausalJEPA().to(device)
    baselines = local_baseline_builders(img_size=int(cfg.img_size))
    for m in baselines.values():
        m.to(device)

    optA = torch.optim.Adam(modelA.parameters(), lr=1e-3)
    optB = {name: torch.optim.Adam(m.parameters(), lr=1e-3) for name, m in baselines.items()}

    out_txt = Path(args.out_txt)
    out_txt.parent.mkdir(parents=True, exist_ok=True)
    with open(out_txt, "w", encoding="utf-8") as f:
        f.write(f"timestamp: {_timestamp()}\n")
        f.write(f"snapshot_tag: {args.snapshot_tag}\n")
        f.write(f"seed: {int(args.seed)}\n")
        f.write(f"profile: {args.profile}\n")
        f.write(f"cfg_name: {args.cfg_name}\n")
        f.write(f"cfg: {json.dumps(cfg_dict, sort_keys=True)}\n")
        f.write(f"self_sha256: {_sha256_self()}\n")
        f.write("cmd: " + " ".join(os.sys.argv) + "\n")
        f.write("baselines: " + json.dumps(sorted(baselines.keys())) + "\n")

    modelA.train()
    for m in baselines.values():
        m.train()

    for step in range(1, int(steps) + 1):
        batch = sample_batch(cfg=cfg, batch_size=int(batch_size), device=device, g=g, ood=False)
        image = batch["image"]
        target = batch["amodal_mask"]

        outA = modelA(image)
        loss_seg_A = F.binary_cross_entropy_with_logits(outA, target)
        p_full, t_full, z = modelA.jepa_forward(x_visible=image, full_mask=target)
        loss_jepa = _v5b_jepa_loss(p_full, t_full, z)
        loss_A = loss_seg_A + 0.1 * loss_jepa
        optA.zero_grad()
        loss_A.backward()
        optA.step()
        modelA.ema_update()

        loss_B_last = 0.0
        for name, m in baselines.items():
            outB = m(image)
            loss_B = F.binary_cross_entropy_with_logits(outB, target)
            optB[name].zero_grad()
            loss_B.backward()
            optB[name].step()
            loss_B_last = float(loss_B.item())

        if step == 1 or step % int(log_every) == 0 or step == int(steps):
            with open(out_txt, "a", encoding="utf-8") as f:
                f.write(f"step {step}/{steps} A.seg={loss_seg_A.item():.4f} A.jepa={loss_jepa.item():.4f} | B_last.seg={loss_B_last:.4f}\n")

    modelA.eval()
    for m in baselines.values():
        m.eval()

    def eval_iou(*, ood: bool) -> tuple[float, dict[str, float]]:
        iousA = []
        iousB: dict[str, list[float]] = {k: [] for k in baselines.keys()}
        for _ in range(int(eval_batches)):
            bb = sample_batch(cfg=cfg, batch_size=1024, device=device, g=g, ood=bool(ood))
            with torch.no_grad():
                oA = modelA(bb["image"])
                iousA.append(_calculate_iou(oA, bb["amodal_mask"]))
                for name, m in baselines.items():
                    oB = m(bb["image"])
                    iousB[name].append(_calculate_iou(oB, bb["amodal_mask"]))
        A = float(sum(iousA) / len(iousA))
        B = {name: float(sum(v) / len(v)) for name, v in iousB.items()}
        return A, B

    iidA, iidBs = eval_iou(ood=False)
    oodA, oodBs = eval_iou(ood=True)
    iidB_max = float(max(iidBs.values()))
    oodB_max = float(max(oodBs.values()))

    # audits on a fresh OOD batch (A only; z is the audited object)
    aud_batch = sample_batch(cfg=cfg, batch_size=1024, device=device, g=g, ood=True)
    with torch.no_grad():
        baseA = modelA(aud_batch["image"])
        base_iou = _calculate_iou(baseA, aud_batch["amodal_mask"])

        z_zero = torch.zeros((aud_batch["image"].shape[0], modelA.amodal_head[0].in_features), device=device)
        ablA = modelA.amodal_head(z_zero).view(-1, 1, cfg.img_size, cfg.img_size)
        abl_iou = _calculate_iou(ablA, aud_batch["amodal_mask"])

        perm = torch.randperm(aud_batch["image"].shape[0], device=device)
        swapA = modelA.swap_forward(aud_batch["image"], perm)
        swap_vs_orig = _calculate_iou(swapA, aud_batch["amodal_mask"])
        swap_vs_perm = _calculate_iou(swapA, aud_batch["amodal_mask"][perm])

    row = {
        "kind": "aslmt_law_v5b_amodal_localclass",
        "snapshot_tag": str(args.snapshot_tag),
        "seed": int(args.seed),
        "profile": str(args.profile),
        "cfg_name": str(args.cfg_name),
        "cfg": cfg_dict,
        "steps": int(steps),
        "baseline_class": {"names": sorted(baselines.keys())},
        "iid": {"A_IoU": float(iidA), "B_IoU": float(iidB_max), "Bs_IoU": iidBs},
        "ood": {
            "A_IoU": float(oodA),
            "B_IoU": float(oodB_max),  # class best-case
            "Bs_IoU": oodBs,
            "audit": {
                "A_IoU_base": float(base_iou),
                "A_IoU_ablated": float(abl_iou),
                "ablation_drop": float(base_iou - abl_iou),
                "swap_vs_orig": float(swap_vs_orig),
                "swap_vs_perm": float(swap_vs_perm),
            },
        },
    }

    out_jsonl = Path(args.out_jsonl)
    out_jsonl.parent.mkdir(parents=True, exist_ok=True)
    with open(out_jsonl, "a", encoding="utf-8") as f:
        f.write(json.dumps(row, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()

