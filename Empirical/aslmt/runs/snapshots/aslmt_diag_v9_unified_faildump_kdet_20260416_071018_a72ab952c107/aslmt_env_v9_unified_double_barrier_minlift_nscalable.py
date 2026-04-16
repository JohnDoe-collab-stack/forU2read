import random

from torch.utils.data import Dataset

from render_v9_unified_paired_ctx_nscalable import Ctx, render


def _min_occ_half_for_n(*, n_classes: int, ood: bool) -> int:
    """
    Ensure both orientations have at least n distinct positions.

    In the renderer (n-scalable), the number of discrete positions available is:
      L = (ix1-ix0)-4 = 2*occ_half - 6    (IID, inner_margin=1)
      L = 2*occ_half - 8                 (OOD, inner_margin=2)

    We require L >= n_classes for both x/y orientations, so we enforce a lower bound
    on occ_half at sampling time.
    """
    n = int(n_classes)
    if ood:
        # 2*occ_half - 8 >= n  => occ_half >= (n+8)/2
        return int((n + 9) // 2)
    # 2*occ_half - 6 >= n  => occ_half >= (n+6)/2
    return int((n + 7) // 2)


class V9UnifiedDoubleBarrierMinLiftDatasetNScalable(Dataset):
    """
    Unified witness (n-scalable): same idea as v9_unified, but the context sampling
    is constrained as a function of n so that the image-barrier is structurally valid.
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

