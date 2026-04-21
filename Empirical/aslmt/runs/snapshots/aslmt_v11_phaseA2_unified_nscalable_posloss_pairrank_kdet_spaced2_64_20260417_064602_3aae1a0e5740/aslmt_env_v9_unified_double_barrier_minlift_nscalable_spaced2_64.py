import random

from torch.utils.data import Dataset

from render_v9_unified_paired_ctx_nscalable_spaced2_64 import Ctx, POS_STRIDE, render


def _min_occ_half_for_n(*, n_classes: int, ood: bool) -> int:
    """
    Ensure both orientations have enough discrete positions under POS_STRIDE.

    In the renderer (with `inner_margin=1` IID, `inner_margin=2` OOD):
      L = (ix1-ix0)-4 = 2*occ_half - 6    (IID)
      L = 2*occ_half - 8                 (OOD)

    We require:
      L >= needed = POS_STRIDE*(n-1)+1
    """
    n = int(n_classes)
    needed = int(POS_STRIDE) * int(n - 1) + 1
    if ood:
        return int((needed + 9) // 2)  # ceil((needed+8)/2)
    return int((needed + 7) // 2)  # ceil((needed+6)/2)


class V9UnifiedDoubleBarrierMinLiftDatasetNScalableSpaced2_64(Dataset):
    """
    Unified witness (n-scalable, spaced2, 64x64):

    - same double-barrier + min-lift structure as v9_unified,
    - but with a larger default image so Phase A2 can target larger `n`
      (e.g. `n=8,12,16`) without structural invalidity.
    """

    def __init__(self, *, size: int, n_classes: int, ood: bool, img_size: int = 64, seed: int = 0):
        self.size = int(size)
        self.n_classes = int(n_classes)
        self.ood = bool(ood)
        self.img_size = int(img_size)
        self.seed = int(seed)
        assert self.n_classes >= 2

    def __len__(self) -> int:
        return self.size

    def __getitem__(self, idx: int):
        min_occ_half = _min_occ_half_for_n(n_classes=self.n_classes, ood=self.ood)
        # Keep a small range around the minimum while guaranteeing validity.
        occ_half = random.randint(min_occ_half, min_occ_half + (2 if self.ood else 1))

        # Ensure occluder fits comfortably inside the image.
        # We sample the center conditional on the chosen occ_half.
        margin = 4
        lo = occ_half + margin
        hi = self.img_size - occ_half - margin
        if hi < lo:
            raise ValueError(
                f"img_size={int(self.img_size)} too small for n={int(self.n_classes)} "
                f"(need occ_half>={int(min_occ_half)}, got occ_half={int(occ_half)})"
            )
        cx = random.randint(lo, hi)
        cy = random.randint(lo, hi)

        t = random.randint(2, 3 if not self.ood else 4)

        h = random.randint(0, self.n_classes - 1)
        k = random.randint(0, 1)

        ctx = Ctx(cx=cx, cy=cy, t=t, occ_half=occ_half, img_size=self.img_size, ood=self.ood, seed=self.seed + idx)
        return render(ctx, h=h, k=k, n_classes=self.n_classes)

