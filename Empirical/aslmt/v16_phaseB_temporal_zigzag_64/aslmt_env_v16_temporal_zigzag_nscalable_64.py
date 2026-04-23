import random

from torch.utils.data import Dataset

from render_v16_temporal_zigzag_paired_ctx_64 import Ctx, render, sample_ctx


class V16TemporalZigzagDatasetNScalable64(Dataset):
    """
    Phase B family T1 (temporal zigzag, 64x64).

    The dataset is structurally valid by construction for all `n` such that the
    cue start encoding fits under `POS_STRIDE` in the renderer.
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
        ctx = sample_ctx(idx=idx, n_classes=self.n_classes, ood=self.ood, img_size=self.img_size, seed_base=self.seed)
        h = random.randint(0, self.n_classes - 1)
        k = random.randint(0, 1)
        return render(ctx, h=h, k=k, n_classes=self.n_classes)

