import render_law_v3b_unified_v2_strong_qforced_paired_ctx_nscalable_spaced2_64 as base


Ctx = base.Ctx
POS_STRIDE = base.POS_STRIDE


def render(ctx: Ctx, *, h: int, k: int, n_classes: int):
    out = base.render(ctx, h=int(h), k=int(k), n_classes=int(n_classes))
    # Leak h into the image by drawing the cue marker on the visible image.
    H = int(out["image"].shape[-2])
    W = int(out["image"].shape[-1])
    mx, my = base._cue_marker_pos(h=int(h) % int(n_classes), n_classes=int(n_classes), img_size=int(H))
    img = out["image"].clone()
    x0 = max(0, min(W, int(mx)))
    y0 = max(0, min(H, int(my)))
    x1 = max(0, min(W, int(mx) + 2))
    y1 = max(0, min(H, int(my) + 2))
    if x1 > x0 and y1 > y0:
        # Flip a small 2x2 patch so that varying `h` necessarily changes `image`.
        img[0, y0:y1, x0:x1] = 1.0 - img[0, y0:y1, x0:x1]
    out["image"] = img
    return out


__all__ = ["Ctx", "POS_STRIDE", "render"]
