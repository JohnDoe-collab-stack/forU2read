import argparse
import hashlib
import json
from datetime import datetime
from pathlib import Path
from typing import Any

import torch

from aslmt_model_v20_algebra_v3b_query_zread import V20AlgebraV3bQueryModelA_ZRead
from render_aslmt_v20_algebra_v3b_paired_ctx_nscalable_spaced2_64 import Ctx, POS_STRIDE, render


HERE = Path(__file__).resolve().parent


def _now_ts() -> str:
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def _sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    h.update(p.read_bytes())
    return h.hexdigest()


def _seed_everything(seed: int) -> None:
    torch.manual_seed(int(seed))
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(int(seed))


def _tensor_to_jsonable(x: torch.Tensor) -> Any:
    x = x.detach().cpu()
    if x.ndim == 0:
        return int(x.item())
    if x.dtype.is_floating_point:
        return x.to(torch.float32).tolist()
    return x.to(torch.long).tolist()


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


def _z_argmax_for_h(*, modelA: V20AlgebraV3bQueryModelA_ZRead, device: torch.device, ctx: Ctx, h: int, k: int, n_classes: int) -> int:
    ex = render(ctx, h=int(h), k=int(k), n_classes=int(n_classes))
    cue = _add_xy(ex["cue_image"].unsqueeze(0).to(device))
    with torch.no_grad():
        zl = modelA.z_logits(cue)
    return int(torch.argmax(zl, dim=-1).item())


def _find_collision_h_pair(*, modelA: V20AlgebraV3bQueryModelA_ZRead, device: torch.device, ctx: Ctx, k: int, n_classes: int) -> tuple[int, int, int] | None:
    seen: dict[int, int] = {}
    for h in range(int(n_classes)):
        z = _z_argmax_for_h(modelA=modelA, device=device, ctx=ctx, h=int(h), k=int(k), n_classes=int(n_classes))
        if z in seen:
            return int(seen[z]), int(h), int(z)
        seen[z] = int(h)
    return None


def _forced_fail_from_collision(
    *,
    modelA: V20AlgebraV3bQueryModelA_ZRead,
    device: torch.device,
    ctx: Ctx,
    h0: int,
    h1: int,
    z: int,
    k_fixed: int,
    n_classes: int,
) -> dict:
    ex0 = render(ctx, h=int(h0), k=int(k_fixed), n_classes=int(n_classes))
    ex1 = render(ctx, h=int(h1), k=int(k_fixed), n_classes=int(n_classes))

    cue0 = _add_xy(ex0["cue_image"].unsqueeze(0).to(device))
    cue1 = _add_xy(ex1["cue_image"].unsqueeze(0).to(device))
    img = _add_xy(ex0["image"].unsqueeze(0).to(device))
    t0 = ex0["hidden_target"].unsqueeze(0).to(device)
    t1 = ex1["hidden_target"].unsqueeze(0).to(device)

    k = torch.tensor([int(k_fixed)], device=device, dtype=torch.long)
    with torch.no_grad():
        p0 = modelA.forward_with_res_bit(cue0, img, res_bit=k)
        p1 = modelA.forward_with_res_bit(cue1, img, res_bit=k)

    same_pred = bool(torch.allclose(p0, p1))
    s00 = float(_overlap_score(p0, t0).item())
    s01 = float(_overlap_score(p0, t1).item())
    s10 = float(_overlap_score(p1, t0).item())
    s11 = float(_overlap_score(p1, t1).item())

    # If predictions are identical (they should be when z-collided), they cannot rank both targets correctly.
    # We export the scores as the check payload, and mark the case as a forced failure when at least one side
    # ranks incorrectly under the overlap ordering.
    side0_correct = bool(s00 > s01)
    side1_correct = bool(s11 > s10)
    forced_fail = bool(same_pred and not (side0_correct and side1_correct))

    return {
        "prop": "minproof_z_collision_forced_fail",
        "detail": "z(h0)=z(h1) implies identical decoder input (image,k,z) so paired discrimination must fail",
        "payload": {
            "ctx": {
                "cx": int(ctx.cx),
                "cy": int(ctx.cy),
                "t": int(ctx.t),
                "occ_half": int(ctx.occ_half),
                "img_size": int(ctx.img_size),
                "ood": bool(ctx.ood),
                "seed": int(ctx.seed),
            },
            "collision": {"h0": int(h0), "h1": int(h1), "z": int(z), "k_fixed": int(k_fixed)},
            "check": {
                "same_pred": bool(same_pred),
                "forced_fail": bool(forced_fail),
                "scores": {"s00": s00, "s01": s01, "s10": s10, "s11": s11},
            },
        },
    }


def main() -> None:
    p = argparse.ArgumentParser(
        description="Minproof certifier for v20 algebra v3b proofpack: emit forced-failure witnesses when z mediates too few classes."
    )
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

    run_meta = {
        "run_tag": f"v20_algebra_v3b_minproof_{split}",
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
            k_fixed = int(ctx.seed & 1)
            coll = _find_collision_h_pair(modelA=modelA, device=device, ctx=ctx, k=int(k_fixed), n_classes=int(args.n_classes))
            if coll is None:
                continue
            h0, h1, z = coll
            v = _forced_fail_from_collision(
                modelA=modelA,
                device=device,
                ctx=ctx,
                h0=int(h0),
                h1=int(h1),
                z=int(z),
                k_fixed=int(k_fixed),
                n_classes=int(args.n_classes),
            )
            v["episode_id"] = int(ep_id)
            v["ctx_i"] = int(ctx_i)
            all_vios.append(v)

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
                    "pigeonhole": {
                        "requires_collision": bool(int(args.z_classes) < int(args.n_classes)),
                        "required_min_z_classes": int(args.n_classes),
                        "z_classes": int(args.z_classes),
                    },
                    "violations": all_vios,
                    "n_violations": int(len(all_vios)),
                },
            }
        )

    _write_jsonl(out_jsonl, recs)
    print(f"WROTE {str(out_jsonl)} lines={len(recs)}")


if __name__ == "__main__":
    main()
