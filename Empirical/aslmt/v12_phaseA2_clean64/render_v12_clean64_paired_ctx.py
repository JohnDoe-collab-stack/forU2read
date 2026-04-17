from __future__ import annotations

from dataclasses import dataclass

import torch


POS_STRIDE = 2


@dataclass(frozen=True)
class Ctx:
    cx: int
    cy: int
    occ_half: int
    t: int
    img_size: int
    ood: bool
    seed: int


def _zeros(*, img_size: int) -> torch.Tensor:
    return torch.zeros((1, int(img_size), int(img_size)), dtype=torch.float32)


def _draw_square(mask: torch.Tensor, *, cx: int, cy: int, half: int, v: float) -> None:
    H = int(mask.shape[-2])
    W = int(mask.shape[-1])
    x0 = max(0, int(cx) - int(half))
    x1 = min(W - 1, int(cx) + int(half))
    y0 = max(0, int(cy) - int(half))
    y1 = min(H - 1, int(cy) + int(half))
    mask[:, y0 : y1 + 1, x0 : x1 + 1] = float(v)


def _draw_bar_vertical(mask: torch.Tensor, *, cx: int, cy: int, occ_half: int, inner: int, bar_x: int, t: int, v: float) -> None:
    H = int(mask.shape[-2])
    W = int(mask.shape[-1])
    x0 = int(bar_x)
    x1 = int(bar_x) + int(t) - 1
    y0 = int(cy) - int(occ_half) + int(inner)
    y1 = int(cy) + int(occ_half) - int(inner)
    x0 = max(0, x0)
    x1 = min(W - 1, x1)
    y0 = max(0, y0)
    y1 = min(H - 1, y1)
    mask[:, y0 : y1 + 1, x0 : x1 + 1] = float(v)


def _draw_bar_horizontal(mask: torch.Tensor, *, cx: int, cy: int, occ_half: int, inner: int, bar_y: int, t: int, v: float) -> None:
    H = int(mask.shape[-2])
    W = int(mask.shape[-1])
    y0 = int(bar_y)
    y1 = int(bar_y) + int(t) - 1
    x0 = int(cx) - int(occ_half) + int(inner)
    x1 = int(cx) + int(occ_half) - int(inner)
    x0 = max(0, x0)
    x1 = min(W - 1, x1)
    y0 = max(0, y0)
    y1 = min(H - 1, y1)
    mask[:, y0 : y1 + 1, x0 : x1 + 1] = float(v)


def min_occ_half_for_n(*, n_classes: int, inner: int, t_max: int) -> int:
    n = int(n_classes)
    needed = (2 * int(inner)) + int(POS_STRIDE) * int(n - 1) + int(t_max)
    return int((needed + 1) // 2) + 1


def render(*, ctx: Ctx, h: int, k: int, n_classes: int, inner: int = 2) -> dict[str, torch.Tensor]:
    """
    Returns a dict with:
      - image: (1,H,W) visible-only (depends on ctx and k, never on h)
      - cue_image: (1,H,W) cue-only (depends on ctx and h, never on k)
      - hidden_target: (1,H,W) target (depends on ctx, h, k)
      - h, k: scalar tensors (int64)
    """
    H = int(ctx.img_size)
    W = int(ctx.img_size)
    n = int(n_classes)
    h = int(h)
    k = int(k)
    if not (0 <= h < n):
        raise ValueError(f"h out of range: h={h} n={n}")
    if k not in (0, 1):
        raise ValueError(f"k must be 0/1, got k={k}")

    image = _zeros(img_size=H)
    cue = _zeros(img_size=H)
    tgt = _zeros(img_size=H)

    # Visible image: occluder only + deterministic k-band, independent of h.
    _draw_square(image, cx=int(ctx.cx), cy=int(ctx.cy), half=int(ctx.occ_half), v=1.0)
    if k == 1:
        image[:, 0:3, :] = 1.0

    # Cue image: deterministic 2×2 marker encoding h, independent of k.
    left = int(ctx.cx) - int(ctx.occ_half)
    top = int(ctx.cy) - int(ctx.occ_half)
    mx = left + int(inner) + int(POS_STRIDE) * int(h)
    my = top + int(inner)
    cue[:, my : my + 2, mx : mx + 2] = 1.0

    # Target: orientation chosen by k, position chosen by h.
    if k == 0:
        bar_x = left + int(inner) + int(POS_STRIDE) * int(h)
        _draw_bar_vertical(
            tgt,
            cx=int(ctx.cx),
            cy=int(ctx.cy),
            occ_half=int(ctx.occ_half),
            inner=int(inner),
            bar_x=int(bar_x),
            t=int(ctx.t),
            v=1.0,
        )
    else:
        bar_y = top + int(inner) + int(POS_STRIDE) * int(h)
        _draw_bar_horizontal(
            tgt,
            cx=int(ctx.cx),
            cy=int(ctx.cy),
            occ_half=int(ctx.occ_half),
            inner=int(inner),
            bar_y=int(bar_y),
            t=int(ctx.t),
            v=1.0,
        )

    return {
        "image": image,
        "cue_image": cue,
        "hidden_target": tgt,
        "h": torch.tensor(int(h), dtype=torch.long),
        "k": torch.tensor(int(k), dtype=torch.long),
    }

