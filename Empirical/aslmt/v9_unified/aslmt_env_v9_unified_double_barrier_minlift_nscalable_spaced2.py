import random

from torch.utils.data import Dataset

from render_v9_unified_paired_ctx_nscalable_spaced2 import Ctx, POS_STRIDE, render


def _min_occ_half_for_n(*, n_classes: int, ood: bool) -> int:
    """
    Ensure both orientations have enough discrete positions under POS_STRIDE.

    In the renderer, the number of unit positions available is:
      L = (ix1-ix0)-4 = 2*occ_half - 6    (IID, inner_margin=1)
      L = 2*occ_half - 8                 (OOD, inner_margin=2)

    Under spacing, we need:
      L >= needed = POS_STRIDE*(n-1)+1
    """
    n = int(n_classes)
    needed = int(POS_STRIDE) * int(n - 1) + 1
    if ood:
        # 2*occ_half - 8 >= needed  => occ_half >= (needed+8)/2
        return int((needed + 9) // 2)
    # 2*occ_half - 6 >= needed  => occ_half >= (needed+6)/2
    return int((needed + 7) // 2)


class V9UnifiedDoubleBarrierMinLiftDatasetNScalableSpaced2(Dataset):
    """
    Unified witness (n-scalable, spaced2): same as v9_unified_nscalable, but with
    a spaced hidden-position map to reduce target overlap on the image-barrier.
    """

    def __init__(self, *, size: int, n_classes: int, ood: bool, img_size: int = 32, seed: int = 0):
        self.size = int(size)
        self.n_classes = int(n_classes)
        self.ood = bool(ood)
        self.img_size = int(img_size)
        self.seed = int(seed)
        assert self.n_classes >= 2

    def __len__(self) -> int:
        return self.size

    def __getitem__(self, idx: int):
        cx = random.randint(12, 20)
        cy = random.randint(12, 20)
        t = random.randint(2, 3 if not self.ood else 4)

        min_occ_half = _min_occ_half_for_n(n_classes=self.n_classes, ood=self.ood)
        # keep a small range while guaranteeing validity
        max_occ_half = min(10, min_occ_half + (2 if self.ood else 1))
        occ_half = random.randint(min_occ_half, max_occ_half)

        h = random.randint(0, self.n_classes - 1)
        k = random.randint(0, 1)

        ctx = Ctx(cx=cx, cy=cy, t=t, occ_half=occ_half, img_size=self.img_size, ood=self.ood, seed=self.seed + idx)
        return render(ctx, h=h, k=k, n_classes=self.n_classes)

