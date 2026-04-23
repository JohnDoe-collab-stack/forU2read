import torch

import render_law_v3b_unified_v2_strong_qforced_paired_ctx_nscalable_spaced2_64 as base


Ctx = base.Ctx
POS_STRIDE = base.POS_STRIDE


def render(ctx: Ctx, *, h: int, k: int, n_classes: int) -> dict[str, torch.Tensor]:
    out = base.render(ctx, h=int(h), k=int(k), n_classes=int(n_classes))
    out["cue_image"] = torch.zeros_like(out["cue_image"])
    return out


__all__ = ["Ctx", "POS_STRIDE", "render"]

