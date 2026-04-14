import argparse
import hashlib
import json
import os
from dataclasses import asdict, dataclass
from datetime import datetime
from pathlib import Path
from typing import Any

import torch


@dataclass(frozen=True)
class Ctx:
    cx: int
    cy: int
    t: int
    occ_half: int
    img_size: int = 32
    ood: bool = False
    seed: int = 0


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _draw_rect(mask: torch.Tensor, x0: int, y0: int, x1: int, y1: int, img_size: int, value: float = 1.0) -> None:
    x0 = max(0, min(img_size, x0))
    x1 = max(0, min(img_size, x1))
    y0 = max(0, min(img_size, y0))
    y1 = max(0, min(img_size, y1))
    if x1 > x0 and y1 > y0:
        mask[y0:y1, x0:x1] = value


def _draw_hbar(mask: torch.Tensor, cy: int, x0: int, x1: int, thickness: int, img_size: int) -> None:
    _draw_rect(mask, x0, cy - thickness // 2, x1, cy + (thickness + 1) // 2, img_size)


def _draw_vbar(mask: torch.Tensor, cx: int, y0: int, y1: int, thickness: int, img_size: int) -> None:
    _draw_rect(mask, cx - thickness // 2, y0, cx + (thickness + 1) // 2, y1, img_size)


def render(ctx: Ctx, *, h: int, k: int) -> dict[str, torch.Tensor]:
    """Deterministic render for a fixed geometric ctx and bits h,k."""

    H = int(ctx.img_size)
    W = int(ctx.img_size)

    scaffold = torch.zeros((H, W), dtype=torch.float32)
    occlusion_mask = torch.zeros((H, W), dtype=torch.float32)

    cx = int(ctx.cx)
    cy = int(ctx.cy)
    t = int(ctx.t)
    occ_half = int(ctx.occ_half)

    ox0, ox1 = cx - occ_half, cx + occ_half
    oy0, oy1 = cy - occ_half, cy + occ_half
    _draw_rect(occlusion_mask, ox0, oy0, ox1, oy1, H, 1.0)

    # Visible scaffold stubs outside occluder.
    _draw_vbar(scaffold, cx, 0, oy0, t, H)
    _draw_vbar(scaffold, cx, oy1, H, t, H)
    _draw_hbar(scaffold, cy, 0, ox0, t, H)
    _draw_hbar(scaffold, cy, ox1, W, t, H)

    # Present bit k is carried only by decision-time image (outside occluder).
    present_mark = torch.zeros_like(scaffold)
    if int(k) == 1:
        _draw_rect(present_mark, 1, 1, 5, 5, H, 1.0)

    # Hidden bit h is carried only by cue.
    cue = torch.zeros_like(scaffold)
    inner_margin = 1 if not ctx.ood else 2
    ix0, ix1 = ox0 + inner_margin, ox1 - inner_margin
    iy0, iy1 = oy0 + inner_margin, oy1 - inner_margin

    if int(h) == 0:
        _draw_vbar(cue, ix0 + 2, iy0, iy1, max(2, t), H)
    else:
        _draw_hbar(cue, iy0 + 2, ix0, ix1, max(2, t), H)

    # Target inside occluder depends on XOR.
    y = int(h) ^ int(k)
    target_full = torch.zeros_like(scaffold)
    if y == 0:
        _draw_vbar(target_full, cx, oy0, oy1, max(2, t), H)
        _draw_hbar(target_full, cy, ox0, ox1, max(2, t), H)
    else:
        _draw_hbar(target_full, iy0 + t // 2, ix0, ix1, t, H)
        _draw_hbar(target_full, iy1 - t // 2, ix0, ix1, t, H)
        _draw_vbar(target_full, ix0 + t // 2, iy0, iy1, t, H)
        _draw_vbar(target_full, ix1 - t // 2, iy0, iy1, t, H)

    hidden_target = (target_full * occlusion_mask).clamp(0.0, 1.0)

    visible = (scaffold + present_mark).clamp(0.0, 1.0) * (1.0 - occlusion_mask)
    image = torch.clamp(visible + occlusion_mask, 0.0, 1.0)

    # Deterministic OOD nuisance: flips in cue only (must not depend on k).
    if ctx.ood:
        g = torch.Generator()
        g.manual_seed(int(ctx.seed) + 1000 * int(h))
        n_flips = int(torch.randint(low=10, high=21, size=(1,), generator=g).item())
        ys = torch.randint(low=0, high=H, size=(n_flips,), generator=g)
        xs = torch.randint(low=0, high=W, size=(n_flips,), generator=g)
        cue[ys, xs] = 1.0 - cue[ys, xs]

    return {
        "cue_image": cue.unsqueeze(0),
        "image": image.unsqueeze(0),
        "hidden_target": hidden_target.unsqueeze(0),
        "occlusion_mask": occlusion_mask.unsqueeze(0),
        "h": torch.tensor(int(h), dtype=torch.long),
        "k": torch.tensor(int(k), dtype=torch.long),
        "y": torch.tensor(int(y), dtype=torch.long),
    }


def _jsonable(x: Any) -> Any:
    if isinstance(x, (str, int, float, bool)) or x is None:
        return x
    if isinstance(x, dict):
        return {str(k): _jsonable(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [_jsonable(v) for v in x]
    return str(x)


def main() -> None:
    p = argparse.ArgumentParser(description="Render deterministic paired ctx witnesses for ASLMT v8.")
    p.add_argument("--cx", type=int, default=16)
    p.add_argument("--cy", type=int, default=16)
    p.add_argument("--t", type=int, default=2)
    p.add_argument("--occ-half", type=int, default=6)
    p.add_argument("--img-size", type=int, default=32)
    p.add_argument("--ood", action="store_true")
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--out-dir", type=str, default="")
    args = p.parse_args()

    script_path = Path(__file__).resolve()
    script_sha = _sha256_file(script_path)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    suf = f"{ts}_{script_sha[:16]}"

    aslmt_dir = script_path.parents[1]
    runs_dir = aslmt_dir / "runs"
    out_dir = Path(args.out_dir).expanduser().resolve() if args.out_dir else (runs_dir / f"aslmt_v8_paired_ctx_{suf}")
    out_dir.mkdir(parents=True, exist_ok=False)

    ctx = Ctx(cx=args.cx, cy=args.cy, t=args.t, occ_half=args.occ_half, img_size=args.img_size, ood=bool(args.ood), seed=int(args.seed))

    # Image-barrier pair: same image (k fixed), different target (flip h).
    k_fixed = 0
    x_im0 = render(ctx, h=0, k=k_fixed)
    x_im1 = render(ctx, h=1, k=k_fixed)

    # Cue-barrier pair: same cue (h fixed), different target (flip k).
    h_fixed = 0
    x_cu0 = render(ctx, h=h_fixed, k=0)
    x_cu1 = render(ctx, h=h_fixed, k=1)

    checks = {
        "image_barrier": {
            "image_equal": bool(torch.equal(x_im0["image"], x_im1["image"])),
            "target_equal": bool(torch.equal(x_im0["hidden_target"], x_im1["hidden_target"])),
        },
        "cue_barrier": {
            "cue_equal": bool(torch.equal(x_cu0["cue_image"], x_cu1["cue_image"])),
            "target_equal": bool(torch.equal(x_cu0["hidden_target"], x_cu1["hidden_target"])),
        },
    }

    tensors_path = out_dir / f"paired_ctx_tensors_{suf}.pt"
    manifest_path = out_dir / f"paired_ctx_manifest_{suf}.json"
    console_path = out_dir / f"paired_ctx_console_{suf}.txt"

    payload = {
        "ctx": asdict(ctx),
        "checks": checks,
        "image_pair": {"x": x_im0, "x_prime": x_im1, "k_fixed": k_fixed},
        "cue_pair": {"x": x_cu0, "x_prime": x_cu1, "h_fixed": h_fixed},
    }
    torch.save(payload, tensors_path)

    manifest = {
        "kind": "aslmt_v8_paired_ctx",
        "timestamp": ts,
        "script": {"path": str(script_path), "sha256": script_sha},
        "cmd": " ".join([os.path.basename(__file__)] + [str(a) for a in os.sys.argv[1:]]),
        "ctx": asdict(ctx),
        "checks": checks,
        "outputs": {"tensors_pt": str(tensors_path), "manifest_json": str(manifest_path), "console_txt": str(console_path)},
    }
    with open(manifest_path, "w", encoding="utf-8") as f:
        f.write(json.dumps(_jsonable(manifest), indent=2) + "\n")

    with open(console_path, "w", encoding="utf-8") as f:
        f.write(f"CMD: {manifest['cmd']}\n")
        f.write(f"SCRIPT_SHA256: {script_sha}\n")
        f.write(json.dumps(_jsonable(checks)) + "\n")

    print(json.dumps(_jsonable(manifest), indent=2))


if __name__ == "__main__":
    main()
