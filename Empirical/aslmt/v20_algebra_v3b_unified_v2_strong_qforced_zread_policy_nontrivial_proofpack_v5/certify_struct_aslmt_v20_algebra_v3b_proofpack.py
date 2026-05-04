import argparse
import hashlib
import json
from datetime import datetime
from pathlib import Path
from typing import Any

import torch

from aslmt_model_v20_algebra_v3b_query_zread import (
    V20AlgebraV3bCueOnlyBaseline,
    V20AlgebraV3bImageOnlyBaseline,
    V20AlgebraV3bQueryModelA_ZRead,
)
from render_aslmt_v20_algebra_v3b_paired_ctx_nscalable_spaced2_64 import Ctx, POS_STRIDE, render


HERE = Path(__file__).resolve().parent


def _now_ts() -> str:
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def _sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    h.update(p.read_bytes())
    return h.hexdigest()


def _tensor_to_jsonable(x: torch.Tensor) -> Any:
    x = x.detach().cpu()
    if x.ndim == 0:
        return int(x.item())
    if x.dtype.is_floating_point:
        return x.to(torch.float32).tolist()
    return x.to(torch.long).tolist()


def _seed_everything(seed: int) -> None:
    torch.manual_seed(int(seed))
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(int(seed))


def _policy_action_from_h(h: torch.Tensor) -> torch.Tensor:
    x = h.to(torch.long) & 0xFFFFFFFF
    x = x ^ ((x << 13) & 0xFFFFFFFF)
    x = x ^ (x >> 17)
    x = x ^ ((x << 5) & 0xFFFFFFFF)
    return (x & 1).to(torch.long)


def _env_res_bit(*, h: torch.Tensor, k: torch.Tensor, action: torch.Tensor) -> torch.Tensor:
    a = action.to(torch.long)
    kk = k.to(torch.long)
    h2 = _policy_action_from_h(h)
    correct = (a == h2).to(torch.long)
    return kk * correct


def _add_xy(x: torch.Tensor) -> torch.Tensor:
    B, C, H, W = x.shape
    if int(C) != 1:
        raise ValueError(f"_add_xy expects C==1, got shape={tuple(x.shape)}")
    ys = torch.linspace(-1.0, 1.0, steps=int(H), device=x.device, dtype=x.dtype)
    xs = torch.linspace(-1.0, 1.0, steps=int(W), device=x.device, dtype=x.dtype)
    yv = ys[:, None].expand(int(H), int(W))
    xv = xs[None, :].expand(int(H), int(W))
    xy = torch.stack([xv, yv], dim=0).unsqueeze(0).expand(int(B), 2, int(H), int(W))
    return torch.cat([x, xy], dim=1)


def _overlap_score(pred_logits: torch.Tensor, true_mask: torch.Tensor) -> torch.Tensor:
    return (torch.sigmoid(pred_logits) * true_mask).sum(dim=(1, 2, 3))


def _make_ctxs(*, n_ctx: int, seed: int, ood: bool, img_size: int, n_classes: int) -> list[Ctx]:
    """
    Deterministic context family used by the proofpack.

    We intentionally keep it simple and seeded (no hidden randomness),
    so the verifier can reconstruct exactly.
    """
    g = torch.Generator(device="cpu")
    g.manual_seed(int(seed) + (999 if bool(ood) else 0))

    n = int(n_classes)
    needed = int(POS_STRIDE) * int(n - 1) + 1
    min_occ_half = int((needed + (9 if bool(ood) else 7)) // 2)

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
        ctxs.append(Ctx(cx=cx, cy=cy, t=t, occ_half=occ_half, img_size=int(img_size), ood=bool(ood), seed=int(seed) + int(i)))
    return ctxs


def _write_jsonl(path: Path, recs: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        for rec in recs:
            f.write(json.dumps(rec, sort_keys=True) + "\n")


def _load_modelA(*, ckpt_path: Path, device: str) -> tuple[V20AlgebraV3bQueryModelA_ZRead, dict]:
    ckpt = torch.load(str(ckpt_path), map_location=str(device))
    z_classes = int(ckpt.get("z_classes", 0))
    if z_classes <= 0:
        raise ValueError("invalid ckpt: missing z_classes")
    modelA = V20AlgebraV3bQueryModelA_ZRead(z_classes=z_classes).to(str(device))
    sd = ckpt.get("modelA_state_dict", None)
    if not isinstance(sd, dict):
        raise ValueError("invalid ckpt: missing modelA_state_dict")
    modelA.load_state_dict(sd)
    modelA.eval()
    return modelA, ckpt


def _compute_violations_for_ctx(
    *,
    modelA: V20AlgebraV3bQueryModelA_ZRead,
    modelB_img: V20AlgebraV3bImageOnlyBaseline,
    modelB_cue: V20AlgebraV3bCueOnlyBaseline,
    device: torch.device,
    ctx: Ctx,
    n_classes: int,
) -> list[dict]:
    """
    Return a list of violation records for one context (may be empty).

    We mirror the v3b paired-context checks, but we emit *per-context counterexamples*
    instead of aggregate rates.
    """
    vios: list[dict] = []
    n_classes = int(n_classes)

    # Deterministic selection of the paired test points from the context seed.
    # This removes any hidden randomness from the proof object and allows an independent
    # verifier to re-run the exact same checks.
    h0 = int(ctx.seed % int(n_classes))
    h1 = int((h0 + 1) % int(n_classes))
    k_fixed = int(ctx.seed & 1)
    ex_im0 = render(ctx, h=int(h0), k=int(k_fixed), n_classes=int(n_classes))
    ex_im1 = render(ctx, h=int(h1), k=int(k_fixed), n_classes=int(n_classes))

    if not torch.allclose(ex_im0["image"], ex_im1["image"]):
        vios.append({"prop": "barrier_image", "detail": "image depends on h under fixed k"})

    # Cue barrier pair: vary k with fixed h
    h_fixed = int((ctx.seed * 3 + 1) % int(n_classes))
    ex_cu0 = render(ctx, h=int(h_fixed), k=0, n_classes=int(n_classes))
    ex_cu1 = render(ctx, h=int(h_fixed), k=1, n_classes=int(n_classes))
    if not torch.allclose(ex_cu0["cue_image"], ex_cu1["cue_image"]):
        vios.append({"prop": "barrier_cue", "detail": "cue depends on k under fixed h"})

    # Build tensors
    cue_im0 = _add_xy(ex_im0["cue_image"].unsqueeze(0).to(device))
    cue_im1 = _add_xy(ex_im1["cue_image"].unsqueeze(0).to(device))
    image_fixed = _add_xy(ex_im0["image"].unsqueeze(0).to(device))
    t_im0 = ex_im0["hidden_target"].unsqueeze(0).to(device)
    t_im1 = ex_im1["hidden_target"].unsqueeze(0).to(device)
    h_im0 = ex_im0["h"].unsqueeze(0).to(device)
    h_im1 = ex_im1["h"].unsqueeze(0).to(device)
    k_im0 = ex_im0["k"].unsqueeze(0).to(device)
    k_im1 = ex_im1["k"].unsqueeze(0).to(device)

    act_im0 = modelA.chosen_action(cue_im0)
    act_im1 = modelA.chosen_action(cue_im1)
    res_im0 = _env_res_bit(h=h_im0, k=k_im0, action=act_im0)
    res_im1 = _env_res_bit(h=h_im1, k=k_im1, action=act_im1)
    pA_im0 = modelA.forward_with_res_bit(cue_im0, image_fixed, res_bit=res_im0)
    pA_im1 = modelA.forward_with_res_bit(cue_im1, image_fixed, res_bit=res_im1)

    A_im0_correct = bool(_overlap_score(pA_im0, t_im0) > _overlap_score(pA_im0, t_im1))
    A_im1_correct = bool(_overlap_score(pA_im1, t_im1) > _overlap_score(pA_im1, t_im0))
    if not (A_im0_correct and A_im1_correct):
        vios.append({"prop": "image_gate", "detail": "modelA failed image-gate pair discrimination"})

    # Cue gate check: fix cue (=h_fixed) but vary k
    cue_fixed = _add_xy(ex_cu0["cue_image"].unsqueeze(0).to(device))
    img0 = _add_xy(ex_cu0["image"].unsqueeze(0).to(device))
    img1 = _add_xy(ex_cu1["image"].unsqueeze(0).to(device))
    t_cu0 = ex_cu0["hidden_target"].unsqueeze(0).to(device)
    t_cu1 = ex_cu1["hidden_target"].unsqueeze(0).to(device)
    h0t = ex_cu0["h"].unsqueeze(0).to(device)
    k0t = ex_cu0["k"].unsqueeze(0).to(device)
    k1t = ex_cu1["k"].unsqueeze(0).to(device)
    act0 = modelA.chosen_action(cue_fixed)
    res0 = _env_res_bit(h=h0t, k=k0t, action=act0)
    res1 = _env_res_bit(h=h0t, k=k1t, action=act0)
    pA0 = modelA.forward_with_res_bit(cue_fixed, img0, res_bit=res0)
    pA1 = modelA.forward_with_res_bit(cue_fixed, img1, res_bit=res1)
    A_cu0_correct = bool(_overlap_score(pA0, t_cu0) > _overlap_score(pA0, t_cu1))
    A_cu1_correct = bool(_overlap_score(pA1, t_cu1) > _overlap_score(pA1, t_cu0))
    if not (A_cu0_correct and A_cu1_correct):
        vios.append({"prop": "cue_gate", "detail": "modelA failed cue-gate pair discrimination"})

    # Baseline counterexamples: any baseline that succeeds on both is a violation
    pB_im0 = modelB_img(image_fixed)
    pB_im1 = modelB_img(image_fixed)
    B_img_both = bool(_overlap_score(pB_im0, t_im0) > _overlap_score(pB_im0, t_im1)) and bool(
        _overlap_score(pB_im1, t_im1) > _overlap_score(pB_im1, t_im0)
    )
    if B_img_both:
        vios.append({"prop": "baseline_image", "detail": "image-only baseline succeeded (should be impossible)"})

    pB0 = modelB_cue(cue_fixed)
    pB1 = modelB_cue(cue_fixed)
    B_cue_both = bool(_overlap_score(pB0, t_cu0) > _overlap_score(pB0, t_cu1)) and bool(
        _overlap_score(pB1, t_cu1) > _overlap_score(pB1, t_cu0)
    )
    if B_cue_both:
        vios.append({"prop": "baseline_cue", "detail": "cue-only baseline succeeded (should be impossible)"})

    # Ablation and swap (image-gate only)
    pA_im0_abl = modelA.ablated_forward_with_res_bit(cue_im0, image_fixed, res_bit=res_im0)
    pA_im1_abl = modelA.ablated_forward_with_res_bit(cue_im1, image_fixed, res_bit=res_im1)
    A_abl_both = bool(_overlap_score(pA_im0_abl, t_im0) > _overlap_score(pA_im0_abl, t_im1)) and bool(
        _overlap_score(pA_im1_abl, t_im1) > _overlap_score(pA_im1_abl, t_im0)
    )
    if A_abl_both:
        vios.append({"prop": "ablation_z", "detail": "z-ablated model still succeeded (should fail)"})

    cue_pair = torch.cat([cue_im0, cue_im1], dim=0)
    img_pair = torch.cat([image_fixed, image_fixed], dim=0)
    res_pair = torch.cat([res_im0, res_im1], dim=0)
    perm = torch.tensor([1, 0], device=device, dtype=torch.long)
    pA_pair_swap = modelA.swap_forward_with_res_bit(cue_pair, img_pair, res_bit=res_pair, perm=perm)
    pA_im0_swap = pA_pair_swap[0:1]
    pA_im1_swap = pA_pair_swap[1:2]

    A_im0_swap_follow = bool(_overlap_score(pA_im0_swap, t_im1) > _overlap_score(pA_im0_swap, t_im0))
    A_im1_swap_follow = bool(_overlap_score(pA_im1_swap, t_im0) > _overlap_score(pA_im1_swap, t_im1))
    if not (A_im0_swap_follow and A_im1_swap_follow):
        vios.append({"prop": "swap_follow", "detail": "swap(z) did not follow as expected"})

    A_im0_swap_orig = bool(_overlap_score(pA_im0_swap, t_im0) > _overlap_score(pA_im0_swap, t_im1))
    A_im1_swap_orig = bool(_overlap_score(pA_im1_swap, t_im1) > _overlap_score(pA_im1_swap, t_im0))
    if A_im0_swap_orig and A_im1_swap_orig:
        vios.append({"prop": "swap_orig", "detail": "swap(z) still matched original targets (should not)"})

    # Always attach minimal reproduction payload (ctx + chosen h/k),
    # so a verifier can re-run the checks independently (even in the zero-violation case).
    payload = {
        "ctx": {
            "cx": int(ctx.cx),
            "cy": int(ctx.cy),
            "t": int(ctx.t),
            "occ_half": int(ctx.occ_half),
            "img_size": int(ctx.img_size),
            "ood": bool(ctx.ood),
            "seed": int(ctx.seed),
        },
        "image_gate": {"h0": int(h0), "h1": int(h1), "k": int(k_fixed)},
        "cue_gate": {"h": int(h_fixed), "k0": 0, "k1": 1},
    }
    for v in vios:
        v["payload"] = payload
    return vios


def main() -> None:
    p = argparse.ArgumentParser(description="Certify v20 algebra v3b by emitting structural counterexamples (proofpack).")
    p.add_argument("--out-jsonl", type=str, required=True)
    p.add_argument("--split", choices=["iid", "ood"], required=True)
    p.add_argument("--episodes", type=int, default=64)
    p.add_argument("--seed-base", type=int, default=0)
    p.add_argument("--n-classes", type=int, required=True)
    p.add_argument("--img-size", type=int, default=64)
    p.add_argument("--z-classes", type=int, required=True)
    p.add_argument("--pair-n-ctx", type=int, default=64)
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--ckpt", type=str, required=True)
    args = p.parse_args()

    out_jsonl = Path(args.out_jsonl)
    split = str(args.split)
    ood = split == "ood"

    _seed_everything(int(args.seed_base))

    ckpt_path = Path(args.ckpt).expanduser().resolve()
    modelA, ckpt = _load_modelA(ckpt_path=ckpt_path, device=str(args.device))

    # Baselines are part of the structural counterexamples.
    modelB_img = V20AlgebraV3bImageOnlyBaseline().to(str(args.device)).eval()
    modelB_cue = V20AlgebraV3bCueOnlyBaseline().to(str(args.device)).eval()

    run_meta = {
        "run_tag": f"v20_algebra_v3b_proofpack_{split}",
        "timestamp": _now_ts(),
        "sha256": {
            "certify_script": _sha256_file(Path(__file__).resolve()),
            "ckpt": _sha256_file(ckpt_path),
            "train_script": _sha256_file(HERE / "aslmt_train_v20_algebra_v3b_seeded_pair_trainood_poswtdice_contractrank_diag_zread_policy_nontrivial.py"),
            "model_script": _sha256_file(HERE / "aslmt_model_v20_algebra_v3b_query_zread.py"),
            "render_script": _sha256_file(HERE / "render_aslmt_v20_algebra_v3b_paired_ctx_nscalable_spaced2_64.py"),
        },
        "config": {
            "split": split,
            "episodes": int(args.episodes),
            "seed_base": int(args.seed_base),
            "n_classes": int(args.n_classes),
            "img_size": int(args.img_size),
            "z_classes": int(args.z_classes),
            "pair_n_ctx": int(args.pair_n_ctx),
        },
        "ckpt_meta": {
            "kind": str(ckpt.get("kind", "")),
            "seed": int(ckpt.get("seed", -1)) if isinstance(ckpt.get("seed", None), int) else -1,
            "n_classes": int(ckpt.get("n_classes", -1)) if isinstance(ckpt.get("n_classes", None), int) else -1,
            "z_classes": int(ckpt.get("z_classes", -1)) if isinstance(ckpt.get("z_classes", None), int) else -1,
        },
    }

    device = torch.device(str(args.device))
    recs: list[dict] = []

    for ep_id in range(int(args.episodes)):
        ctxs = _make_ctxs(
            n_ctx=int(args.pair_n_ctx),
            seed=int(args.seed_base) + int(ep_id),
            ood=bool(ood),
            img_size=int(args.img_size),
            n_classes=int(args.n_classes),
        )
        all_vios: list[dict] = []
        for ctx_i, ctx in enumerate(ctxs):
            vios = _compute_violations_for_ctx(
                modelA=modelA,
                modelB_img=modelB_img,
                modelB_cue=modelB_cue,
                device=device,
                ctx=ctx,
                n_classes=int(args.n_classes),
            )
            for v in vios:
                v["episode_id"] = int(ep_id)
                v["ctx_i"] = int(ctx_i)
            all_vios.extend(vios)

        recs.append(
            {
                "run_meta": run_meta,
                "episode_id": int(ep_id),
                "episode": {
                    "ood": bool(ood),
                    "seed": int(args.seed_base) + int(ep_id),
                    "ctxs": [
                        {
                            "cx": int(c.cx),
                            "cy": int(c.cy),
                            "t": int(c.t),
                            "occ_half": int(c.occ_half),
                            "img_size": int(c.img_size),
                            "ood": bool(c.ood),
                            "seed": int(c.seed),
                        }
                        for c in ctxs
                    ],
                },
                "result": {
                    "n_ctx": int(len(ctxs)),
                    "violations": all_vios,
                    "n_violations": int(len(all_vios)),
                },
            }
        )

    _write_jsonl(out_jsonl, recs)
    print(f"WROTE {str(out_jsonl)} lines={len(recs)}")


if __name__ == "__main__":
    main()
