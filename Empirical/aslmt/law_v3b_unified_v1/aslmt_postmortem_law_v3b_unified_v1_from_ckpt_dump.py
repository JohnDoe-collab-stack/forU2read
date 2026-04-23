import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path

import torch


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


@dataclass(frozen=True)
class PairEvalCfg:
    n_ctx: int = 64
    seed: int = 0
    img_size: int = 64


def _min_occ_half_for_n(*, n_classes: int, ood: bool, pos_stride: int) -> int:
    n = int(n_classes)
    needed = int(pos_stride) * int(n - 1) + 1
    if ood:
        return int((needed + 9) // 2)
    return int((needed + 7) // 2)


def _sample_ctxs(*, n: int, seed: int, ood: bool, img_size: int, n_classes: int, pos_stride: int) -> list:
    # This mirrors the sampling used in the v9_unified train/eval scripts:
    # deterministic in `seed`, with `occ_half` constrained for injectivity.
    import torch as _torch

    g = _torch.Generator()
    g.manual_seed(int(seed))

    min_occ = _min_occ_half_for_n(n_classes=int(n_classes), ood=bool(ood), pos_stride=int(pos_stride))
    margin = 4
    max_occ = (int(img_size) // 2) - margin
    if min_occ > max_occ:
        raise ValueError(
            f"img_size={int(img_size)} too small for n_classes={int(n_classes)} "
            f"under stride={int(pos_stride)} (min_occ={int(min_occ)} > max_occ={int(max_occ)})"
        )

    hi_occ = min(max_occ + 1, min_occ + (3 if ood else 2))
    occ_half = _torch.randint(low=int(min_occ), high=int(hi_occ), size=(n,), generator=g).tolist()

    cx = []
    cy = []
    for oh in occ_half:
        lo = int(oh) + margin
        hi = int(img_size) - int(oh) - margin
        if hi < lo:
            raise ValueError(f"no valid center range for occ_half={int(oh)} under img_size={int(img_size)}")
        cx.append(int(_torch.randint(low=lo, high=hi + 1, size=(1,), generator=g).item()))
        cy.append(int(_torch.randint(low=lo, high=hi + 1, size=(1,), generator=g).item()))

    if ood:
        t = _torch.randint(low=2, high=5, size=(n,), generator=g).tolist()
    else:
        t = _torch.randint(low=2, high=4, size=(n,), generator=g).tolist()

    from render_law_v3b_unified_v1_paired_ctx_nscalable_spaced2_64 import Ctx

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


def main() -> None:
    p = argparse.ArgumentParser(description="Postmortem dumper for law_v3b_unified_v1 checkpoints: dump strict gate failures with margins.")
    p.add_argument("--ckpt", type=str, required=True)
    p.add_argument("--snapshot-dir", type=str, required=True, help="Snapshot directory that contains the exact render/model modules used in the run.")
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--pair-n-ctx", type=int, default=64)
    p.add_argument("--img-size", type=int, default=64)
    p.add_argument("--max-fails", type=int, default=200)
    p.add_argument("--out-jsonl", type=str, required=True)
    args = p.parse_args()

    snap = Path(str(args.snapshot_dir)).expanduser().resolve()
    if not snap.is_dir():
        raise SystemExit(f"snapshot-dir not found: {snap}")
    sys.path.insert(0, str(snap))

    import render_law_v3b_unified_v1_paired_ctx_nscalable_spaced2_64 as render_mod
    from aslmt_model_law_v3b_unified_v1_query import LawV3bUnifiedV1QueryModelA

    ckpt_path = Path(str(args.ckpt)).expanduser().resolve()
    ckpt = torch.load(ckpt_path, map_location="cpu")
    if not isinstance(ckpt, dict) or "modelA_state_dict" not in ckpt:
        raise SystemExit("ckpt does not look like a modelA checkpoint")
    if str(ckpt.get("kind", "")) != "aslmt_law_v3b_unified_v1_poswtdice_contractrank_spaced2_64":
        raise SystemExit("ckpt kind mismatch (expected law_v3b_unified_v1)")

    seed = int(ckpt.get("seed", 0))
    n_classes = int(ckpt.get("n_classes"))
    z_classes = int(ckpt.get("z_classes"))

    device = torch.device(str(args.device))
    modelA = LawV3bUnifiedV1QueryModelA(z_classes=int(z_classes)).to(device)
    modelA.load_state_dict(ckpt["modelA_state_dict"])
    modelA.eval()

    pos_stride = int(getattr(render_mod, "POS_STRIDE"))

    pair_cfg = PairEvalCfg(n_ctx=int(args.pair_n_ctx), seed=int(seed), img_size=int(args.img_size))

    h_pairs: list[tuple[int, int]] = []
    for i in range(n_classes):
        for j in range(i + 1, n_classes):
            h_pairs.append((i, j))

    out_path = Path(str(args.out_jsonl)).expanduser().resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)

    total_checked = 0
    total_fails = 0

    def _dump(rec: dict) -> None:
        nonlocal total_fails
        total_fails += 1
        with open(str(out_path), "a", encoding="utf-8") as f:
            f.write(json.dumps(rec) + "\n")

    for ood in (False, True):
        split = "ood" if bool(ood) else "iid"
        ctxs = _sample_ctxs(
            n=int(pair_cfg.n_ctx),
            seed=int(pair_cfg.seed),
            ood=bool(ood),
            img_size=int(pair_cfg.img_size),
            n_classes=int(n_classes),
            pos_stride=int(pos_stride),
        )

        for i, ctx in enumerate(ctxs):
            total_checked += 1
            h0, h1 = h_pairs[i % len(h_pairs)]

            k_fixed = int((ctx.seed + 0) % 2)
            h_fixed = int((ctx.seed + 1) % n_classes)
            k0, k1 = 0, 1

            x_im0 = render_mod.render(ctx, h=h0, k=k_fixed, n_classes=n_classes)
            x_im1 = render_mod.render(ctx, h=h1, k=k_fixed, n_classes=n_classes)
            x_cu0 = render_mod.render(ctx, h=h_fixed, k=k0, n_classes=n_classes)
            x_cu1 = render_mod.render(ctx, h=h_fixed, k=k1, n_classes=n_classes)

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

                pA_im0_abl = modelA.ablated_forward(cue_im0, image_fixed)
                pA_im1_abl = modelA.ablated_forward(cue_im1, image_fixed)

                cue_pair = torch.cat([cue_im0, cue_im1], dim=0)
                img_pair = torch.cat([image_fixed, image_fixed], dim=0)
                perm = torch.tensor([1, 0], device=device, dtype=torch.long)
                pA_pair_swap = modelA.swap_forward(cue_pair, img_pair, perm=perm)
                pA_im0_swap = pA_pair_swap[0:1]
                pA_im1_swap = pA_pair_swap[1:2]

            s00 = float(_overlap_score(pA_im0, t_im0).item())
            s01 = float(_overlap_score(pA_im0, t_im1).item())
            s11 = float(_overlap_score(pA_im1, t_im1).item())
            s10 = float(_overlap_score(pA_im1, t_im0).item())

            c00 = float(_overlap_score(pA_cu0, t_cu0).item())
            c01 = float(_overlap_score(pA_cu0, t_cu1).item())
            c11 = float(_overlap_score(pA_cu1, t_cu1).item())
            c10 = float(_overlap_score(pA_cu1, t_cu0).item())

            a00 = float(_overlap_score(pA_im0_abl, t_im0).item())
            a01 = float(_overlap_score(pA_im0_abl, t_im1).item())
            a11 = float(_overlap_score(pA_im1_abl, t_im1).item())
            a10 = float(_overlap_score(pA_im1_abl, t_im0).item())

            sw00 = float(_overlap_score(pA_im0_swap, t_im0).item())
            sw01 = float(_overlap_score(pA_im0_swap, t_im1).item())
            sw11 = float(_overlap_score(pA_im1_swap, t_im1).item())
            sw10 = float(_overlap_score(pA_im1_swap, t_im0).item())

            A_im0_correct = bool(s00 > s01)
            A_im1_correct = bool(s11 > s10)
            A_cu0_correct = bool(c00 > c01)
            A_cu1_correct = bool(c11 > c10)

            A_im0_abl_correct = bool(a00 > a01)
            A_im1_abl_correct = bool(a11 > a10)

            A_im0_swap_follow = bool(sw01 > sw00)
            A_im1_swap_follow = bool(sw10 > sw11)
            A_im0_swap_orig = bool(sw00 > sw01)
            A_im1_swap_orig = bool(sw11 > sw10)

            failures = []
            if not (A_im0_correct and A_im1_correct):
                failures.append("A_both_image")
            if not (A_cu0_correct and A_cu1_correct):
                failures.append("A_both_cue")
            if (A_im0_abl_correct and A_im1_abl_correct):
                failures.append("A_ablated_both_image_should_be_0")
            if not (A_im0_swap_follow and A_im1_swap_follow):
                failures.append("A_swap_follow_image")
            if (A_im0_swap_orig and A_im1_swap_orig):
                failures.append("A_swap_orig_both_image_should_be_0")

            if failures:
                _dump(
                    {
                        "kind": "aslmt_law_v3b_unified_v1_postmortem_fail",
                        "ckpt": str(ckpt_path),
                        "snapshot_dir": str(snap),
                        "seed": int(seed),
                        "n_classes": int(n_classes),
                        "z_classes": int(z_classes),
                        "split": str(split),
                        "ctx_index": int(i),
                        "ctx": {"cx": int(ctx.cx), "cy": int(ctx.cy), "t": int(ctx.t), "occ_half": int(ctx.occ_half), "img_size": int(ctx.img_size), "ood": bool(ctx.ood), "seed": int(ctx.seed)},
                        "h0": int(h0),
                        "h1": int(h1),
                        "k_fixed": int(k_fixed),
                        "h_fixed": int(h_fixed),
                        "failures": failures,
                        "scores_image": {"s00": s00, "s01": s01, "s11": s11, "s10": s10, "m0": float(s00 - s01), "m1": float(s11 - s10)},
                        "scores_cue": {"c00": c00, "c01": c01, "c11": c11, "c10": c10, "m0": float(c00 - c01), "m1": float(c11 - c10)},
                        "scores_abl": {"a00": a00, "a01": a01, "a11": a11, "a10": a10, "m0": float(a00 - a01), "m1": float(a11 - a10)},
                        "scores_swap": {"sw00": sw00, "sw01": sw01, "sw11": sw11, "sw10": sw10},
                        "bools": {
                            "A_im0_correct": bool(A_im0_correct),
                            "A_im1_correct": bool(A_im1_correct),
                            "A_cu0_correct": bool(A_cu0_correct),
                            "A_cu1_correct": bool(A_cu1_correct),
                            "A_im0_abl_correct": bool(A_im0_abl_correct),
                            "A_im1_abl_correct": bool(A_im1_abl_correct),
                            "A_im0_swap_follow": bool(A_im0_swap_follow),
                            "A_im1_swap_follow": bool(A_im1_swap_follow),
                            "A_im0_swap_orig": bool(A_im0_swap_orig),
                            "A_im1_swap_orig": bool(A_im1_swap_orig),
                        },
                    }
                )

            if int(total_fails) >= int(args.max_fails):
                break

        if int(total_fails) >= int(args.max_fails):
            break

    print(
        json.dumps(
            {
                "kind": "aslmt_law_v3b_unified_v1_postmortem_summary",
                "total_checked": int(total_checked),
                "total_fail_records": int(total_fails),
                "out_jsonl": str(out_path),
            }
        )
    )


if __name__ == "__main__":
    main()
