import random

from torch.utils.data import Dataset

from render_vN_paired_ctx import Ctx, render


class VNMinLiftDoubleBarrierDataset(Dataset):
    """
    vN generalization of v8:

    Hidden class `h ∈ {0..n-1}` appears only in `cue_image`.
    Present bit `k ∈ {0,1}` appears only in `image`.
    Target inside occluder depends on both (h,k).
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
        occ_half = random.randint(5, 6) if not self.ood else random.randint(7, 9)

        h = random.randint(0, self.n_classes - 1)
        k = random.randint(0, 1)

        ctx = Ctx(cx=cx, cy=cy, t=t, occ_half=occ_half, img_size=self.img_size, ood=self.ood, seed=self.seed + idx)
        return render(ctx, h=h, k=k, n_classes=self.n_classes)

