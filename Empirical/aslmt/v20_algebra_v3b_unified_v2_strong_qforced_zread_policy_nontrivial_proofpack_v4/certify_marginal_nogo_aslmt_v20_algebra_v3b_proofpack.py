import argparse
import hashlib
import json
from datetime import datetime
from pathlib import Path

import torch

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


def _payload_ctx(ctx: Ctx) -> dict:
    return {
        "cx": int(ctx.cx),
        "cy": int(ctx.cy),
        "t": int(ctx.t),
        "occ_half": int(ctx.occ_half),
        "img_size": int(ctx.img_size),
        "ood": bool(ctx.ood),
        "seed": int(ctx.seed),
    }


def main() -> None:
    p = argparse.ArgumentParser(
        description="Certify marginal no-go (environment-only) for v20 algebra v3b proofpack."
    )
    p.add_argument("--out-jsonl", type=str, required=True)
    p.add_argument("--split", choices=["iid", "ood"], required=True)
    p.add_argument("--episodes", type=int, default=64)
    p.add_argument("--seed-base", type=int, default=0)
    p.add_argument("--n-classes", type=int, required=True)
    p.add_argument("--img-size", type=int, default=64)
    p.add_argument("--pair-n-ctx", type=int, default=64)
    args = p.parse_args()

    out_jsonl = Path(args.out_jsonl)
    split = str(args.split)
    ood = split == "ood"

    _seed_everything(int(args.seed_base))

    run_meta = {
        "run_tag": f"v20_algebra_v3b_marginal_nogo_{split}",
        "timestamp": _now_ts(),
        "sha256": {
            "certify_script": _sha256_file(Path(__file__).resolve()),
            "render_script": _sha256_file(HERE / "render_aslmt_v20_algebra_v3b_paired_ctx_nscalable_spaced2_64.py"),
        },
        "config": {
            "split": split,
            "episodes": int(args.episodes),
            "seed_base": int(args.seed_base),
            "n_classes": int(args.n_classes),
            "img_size": int(args.img_size),
            "pair_n_ctx": int(args.pair_n_ctx),
        },
    }

    recs: list[dict] = []
    n_classes = int(args.n_classes)

    for ep_id in range(int(args.episodes)):
        ctxs = _make_ctxs(
            n_ctx=int(args.pair_n_ctx),
            seed=int(args.seed_base) + int(ep_id),
            ood=bool(ood),
            img_size=int(args.img_size),
            n_classes=int(args.n_classes),
        )

        vios: list[dict] = []
        for ctx_i, ctx in enumerate(ctxs):
            k_fixed = int(ctx.seed & 1)
            h0 = int(ctx.seed % int(n_classes))
            h1 = int((h0 + 1) % int(n_classes))

            ex0 = render(ctx, h=int(h0), k=int(k_fixed), n_classes=int(n_classes))
            ex1 = render(ctx, h=int(h1), k=int(k_fixed), n_classes=int(n_classes))

            # Marginal no-go for image-only: same image, different hidden target.
            if torch.allclose(ex0["image"], ex1["image"]) and (not torch.allclose(ex0["hidden_target"], ex1["hidden_target"])):
                pass
            else:
                vios.append(
                    {
                        "prop": "marginal_image_nogo_failed",
                        "detail": "expected same image but different hidden_target when varying h under fixed k",
                        "episode_id": int(ep_id),
                        "ctx_i": int(ctx_i),
                        "payload": {"ctx": _payload_ctx(ctx), "h0": int(h0), "h1": int(h1), "k_fixed": int(k_fixed)},
                    }
                )

            # Marginal no-go for cue-only: same cue, different hidden target when varying k under fixed h.
            h_fixed = int((ctx.seed * 3 + 1) % int(n_classes))
            cu0 = render(ctx, h=int(h_fixed), k=0, n_classes=int(n_classes))
            cu1 = render(ctx, h=int(h_fixed), k=1, n_classes=int(n_classes))
            if torch.allclose(cu0["cue_image"], cu1["cue_image"]) and (not torch.allclose(cu0["hidden_target"], cu1["hidden_target"])):
                pass
            else:
                vios.append(
                    {
                        "prop": "marginal_cue_nogo_failed",
                        "detail": "expected same cue but different hidden_target when varying k under fixed h",
                        "episode_id": int(ep_id),
                        "ctx_i": int(ctx_i),
                        "payload": {"ctx": _payload_ctx(ctx), "h_fixed": int(h_fixed)},
                    }
                )

        recs.append(
            {
                "run_meta": run_meta,
                "episode_id": int(ep_id),
                "episode": {
                    "ood": bool(ood),
                    "seed": int(args.seed_base) + int(ep_id),
                    "ctxs": [_payload_ctx(c) for c in ctxs],
                },
                "result": {"n_ctx": int(len(ctxs)), "violations": vios, "n_violations": int(len(vios))},
            }
        )

    _write_jsonl(out_jsonl, recs)
    print(f"WROTE {str(out_jsonl)} lines={len(recs)}")


if __name__ == "__main__":
    main()

