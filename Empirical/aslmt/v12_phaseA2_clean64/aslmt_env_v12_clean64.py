from __future__ import annotations

from dataclasses import dataclass

import torch
from torch.utils.data import Dataset

from render_v12_clean64_paired_ctx import Ctx, min_occ_half_for_n, render


@dataclass(frozen=True)
class EnvCfg:
    n_classes: int
    ood: bool
    img_size: int
    seed: int
    size: int


def _ctx_for_i(*, i: int, cfg: EnvCfg) -> Ctx:
    g = torch.Generator()
    g.manual_seed(int(cfg.seed) + int(i))

    # Thickness distribution.
    t = int(torch.randint(low=2, high=(5 if bool(cfg.ood) else 4), size=(1,), generator=g).item())

    inner = 2
    occ_min = int(min_occ_half_for_n(n_classes=int(cfg.n_classes), inner=inner, t_max=4))
    margin = 4
    max_occ = (int(cfg.img_size) // 2) - margin
    if occ_min > max_occ:
        raise ValueError(f"img_size={cfg.img_size} too small for n_classes={cfg.n_classes} (occ_min={occ_min} > max_occ={max_occ})")

    # Small but valid range.
    hi_occ = min(max_occ + 1, occ_min + (3 if bool(cfg.ood) else 2))
    occ_half = int(torch.randint(low=int(occ_min), high=int(hi_occ), size=(1,), generator=g).item())

    # Center range that keeps the occluder inside the image.
    lo = int(occ_half) + margin
    hi = int(cfg.img_size) - int(occ_half) - margin
    cx = int(torch.randint(low=lo, high=hi + 1, size=(1,), generator=g).item())
    cy = int(torch.randint(low=lo, high=hi + 1, size=(1,), generator=g).item())

    return Ctx(cx=int(cx), cy=int(cy), occ_half=int(occ_half), t=int(t), img_size=int(cfg.img_size), ood=bool(cfg.ood), seed=int(cfg.seed + i))


class V12Clean64Dataset(Dataset):
    def __init__(self, *, size: int, n_classes: int, ood: bool, img_size: int, seed: int):
        self.cfg = EnvCfg(size=int(size), n_classes=int(n_classes), ood=bool(ood), img_size=int(img_size), seed=int(seed))

    def __len__(self) -> int:
        return int(self.cfg.size)

    def __getitem__(self, idx: int) -> dict[str, torch.Tensor]:
        cfg = self.cfg
        i = int(idx)
        ctx = _ctx_for_i(i=i, cfg=cfg)
        g = torch.Generator()
        g.manual_seed(int(cfg.seed) + 10_000 + int(i))
        h = int(torch.randint(low=0, high=int(cfg.n_classes), size=(1,), generator=g).item())
        k = int(torch.randint(low=0, high=2, size=(1,), generator=g).item())
        x = render(ctx=ctx, h=int(h), k=int(k), n_classes=int(cfg.n_classes))
        return x

