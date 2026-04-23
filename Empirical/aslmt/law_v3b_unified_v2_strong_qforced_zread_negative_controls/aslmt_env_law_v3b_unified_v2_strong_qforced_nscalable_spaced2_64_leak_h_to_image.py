import random

from torch.utils.data import Dataset

from render_law_v3b_unified_v2_strong_qforced_paired_ctx_nscalable_spaced2_64_leak_h_to_image import (
    Ctx,
    POS_STRIDE,
    render,
)


def _min_occ_half_for_n(*, n_classes: int, ood: bool) -> int:
    n = int(n_classes)
    needed = int(POS_STRIDE) * int(n - 1) + 1
    if ood:
        return int((needed + 9) // 2)
    return int((needed + 7) // 2)


class LawV3bUnifiedV2StrongQForcedDatasetNScalableSpaced2_64(Dataset):
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
        occ_half = random.randint(min_occ_half, min_occ_half + (2 if self.ood else 1))

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


__all__ = ["LawV3bUnifiedV2StrongQForcedDatasetNScalableSpaced2_64"]

