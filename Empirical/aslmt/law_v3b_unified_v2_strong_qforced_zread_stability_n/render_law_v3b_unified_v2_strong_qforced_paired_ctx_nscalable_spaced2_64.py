import argparse
import hashlib
import json
import os
from dataclasses import asdict, dataclass
from datetime import datetime
from math import ceil, sqrt
from pathlib import Path
from typing import Any

import torch


POS_STRIDE: int = 2
HIDDEN_THICKNESS: int = 2
DEFAULT_IMG_SIZE: int = 64


@dataclass(frozen=True)
class Ctx:
    cx: int
    cy: int
    t: int
    occ_half: int
    img_size: int = DEFAULT_IMG_SIZE
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


def _draw_vbar(mask: torch.Tensor, cx: torch.Tensor | int, y0: int, y1: int, thickness: int, img_size: int) -> None:
    _draw_rect(mask, int(cx) - thickness // 2, y0, int(cx) + (thickness + 1) // 2, y1, img_size)


def _cue_marker_pos(*, h: int, n_classes: int, img_size: int) -> tuple[int, int]:
    n_classes = int(n_classes)
    assert n_classes >= 2
    hh = int(h) % n_classes

    step = 4
    margin = 1
    g = int(ceil(sqrt(n_classes)))
    col = int(hh % g)
    row = int(hh // g)
    x = margin + col * step
    y = margin + row * step
    x = max(0, min(int(img_size) - 2, x))
    y = max(0, min(int(img_size) - 2, y))
    return int(x), int(y)


def render(ctx: Ctx, *, h: int, k: int, n_classes: int) -> dict[str, torch.Tensor]:
    """
    n-scalable + spaced2 (large image) variant.

    Same unified witness structure as v9_unified:
      - `h` is visible only in `cue_image` via a 2x2 marker,
      - `k` is not visible in `image` (strong regime),
      - the hidden target depends on both:
          `k` chooses orientation, `h` chooses position inside the occluder.
    """
    n_classes = int(n_classes)
    assert n_classes >= 2

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

    _draw_vbar(scaffold, cx, 0, oy0, t, H)
    _draw_vbar(scaffold, cx, oy1, H, t, H)
    _draw_hbar(scaffold, cy, 0, ox0, t, H)
    _draw_hbar(scaffold, cy, ox1, W, t, H)

    hh = int(h) % int(n_classes)
    cue = torch.zeros_like(scaffold)
    mx, my = _cue_marker_pos(h=hh, n_classes=n_classes, img_size=H)
    _draw_rect(cue, mx, my, mx + 2, my + 2, H, 1.0)

    inner_margin = 1 if not ctx.ood else 2
    ix0, ix1 = ox0 + inner_margin, ox1 - inner_margin
    iy0, iy1 = oy0 + inner_margin, oy1 - inner_margin

    Lx = int((ix1 - ix0) - 4)
    Ly = int((iy1 - iy0) - 4)
    needed = int(POS_STRIDE) * int(n_classes - 1) + 1
    if Lx < needed or Ly < needed:
        raise ValueError(
            f"ctx does not support n={n_classes} under stride={int(POS_STRIDE)}: "
            f"needed={needed}, Lx={Lx}, Ly={Ly}, occ_half={occ_half}, img_size={H}, ood={ctx.ood}"
        )

    target_full = torch.zeros_like(scaffold)
    if int(k) == 0:
        bar_x = ix0 + 2 + int(POS_STRIDE) * int(hh)
        _draw_vbar(target_full, bar_x, oy0, oy1, int(HIDDEN_THICKNESS), H)
    else:
        bar_y = iy0 + 2 + int(POS_STRIDE) * int(hh)
        _draw_hbar(target_full, bar_y, ox0, ox1, int(HIDDEN_THICKNESS), H)

    hidden_target = (target_full * occlusion_mask).clamp(0.0, 1.0)

    visible = scaffold.clamp(0.0, 1.0) * (1.0 - occlusion_mask)
    image = torch.clamp(visible + occlusion_mask, 0.0, 1.0)

    if ctx.ood:
        g = torch.Generator()
        g.manual_seed(int(ctx.seed) + 1000 * int(hh))
        n_flips = int(torch.randint(low=10, high=21, size=(1,), generator=g).item())

        forbidden = set()
        for yy in (my, my + 1):
            for xx in (mx, mx + 1):
                if 0 <= yy < H and 0 <= xx < W:
                    forbidden.add((int(yy), int(xx)))

        flips: list[tuple[int, int]] = []
        max_tries = 100000
        tries = 0
        while len(flips) < n_flips and tries < max_tries:
            tries += 1
            yy = int(torch.randint(low=0, high=H, size=(1,), generator=g).item())
            xx = int(torch.randint(low=0, high=W, size=(1,), generator=g).item())
            if (yy, xx) in forbidden:
                continue
            flips.append((yy, xx))
            for dy in (-1, 0, 1):
                for dx in (-1, 0, 1):
                    y2 = yy + dy
                    x2 = xx + dx
                    if 0 <= y2 < H and 0 <= x2 < W:
                        forbidden.add((int(y2), int(x2)))

        if len(flips) < n_flips:
            raise ValueError(f"could not sample {n_flips} non-adjacent flips under img_size={H}")

        ys = torch.tensor([p[0] for p in flips], dtype=torch.long)
        xs = torch.tensor([p[1] for p in flips], dtype=torch.long)
        cue[ys, xs] = 1.0 - cue[ys, xs]

    return {
        "cue_image": cue.unsqueeze(0),
        "image": image.unsqueeze(0),
        "hidden_target": hidden_target.unsqueeze(0),
        "occlusion_mask": occlusion_mask.unsqueeze(0),
        "h": torch.tensor(int(hh), dtype=torch.long),
        "k": torch.tensor(int(k), dtype=torch.long),
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
    p = argparse.ArgumentParser(description="Render paired-ctx witnesses for ASLMT v3b_unified_v2_strong_qforced (n-scalable, spaced2, 64x64).")
    p.add_argument("--n-classes", type=int, default=16)
    p.add_argument("--cx", type=int, default=32)
    p.add_argument("--cy", type=int, default=32)
    p.add_argument("--t", type=int, default=2)
    p.add_argument("--occ-half", type=int, default=20)
    p.add_argument("--img-size", type=int, default=DEFAULT_IMG_SIZE)
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
    out_dir = Path(args.out_dir).expanduser().resolve() if args.out_dir else (runs_dir / f"aslmt_law_v3b_unified_v2_strong_qforced_paired_ctx_{suf}")
    out_dir.mkdir(parents=True, exist_ok=False)

    ctx = Ctx(cx=args.cx, cy=args.cy, t=args.t, occ_half=args.occ_half, img_size=args.img_size, ood=bool(args.ood), seed=int(args.seed))
    n = int(args.n_classes)

    k_fixed = 0
    x_im0 = render(ctx, h=0, k=k_fixed, n_classes=n)
    x_im1 = render(ctx, h=1, k=k_fixed, n_classes=n)
    out = {
        "ctx": asdict(ctx),
        "n_classes": int(n),
        "k_fixed": int(k_fixed),
        "im0": {k: _jsonable(v.shape) for k, v in x_im0.items()},
        "im1": {k: _jsonable(v.shape) for k, v in x_im1.items()},
        "script_sha256": str(script_sha),
    }

    (out_dir / "paired_ctx_shapes.json").write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    if os.environ.get("ASLMT_RENDER_SAVE_TENSORS", ""):
        torch.save(x_im0, out_dir / "im0.pt")
        torch.save(x_im1, out_dir / "im1.pt")


if __name__ == "__main__":
    main()

