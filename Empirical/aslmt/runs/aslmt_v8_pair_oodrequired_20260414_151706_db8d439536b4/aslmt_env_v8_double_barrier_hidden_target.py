import random
import torch
from torch.utils.data import Dataset, DataLoader


class DoubleBarrierHiddenTargetSequenceDataset(Dataset):
    """
    Temporal witness with a *double* structural barrier.

    Two independent bits:
    - h (hidden/past): present only in cue_image
    - k (present): present only in image

    Target inside occluder depends on both via XOR:
      y = h XOR k
      y=0 -> PLUS, y=1 -> RING

    Therefore:
    - image-only is insufficient (fix k, flip h -> same image, different target)
    - cue-only is insufficient (fix h, flip k -> same cue, different target)
    - (cue, image) is sufficient.
    """

    def __init__(self, size: int, ood: bool = False, img_size: int = 32):
        self.size = int(size)
        self.ood = bool(ood)
        self.img_size = int(img_size)

    def __len__(self) -> int:
        return self.size

    def _draw_rect(self, mask: torch.Tensor, x0: int, y0: int, x1: int, y1: int, value: float = 1.0) -> None:
        x0 = max(0, min(self.img_size, x0))
        x1 = max(0, min(self.img_size, x1))
        y0 = max(0, min(self.img_size, y0))
        y1 = max(0, min(self.img_size, y1))
        if x1 > x0 and y1 > y0:
            mask[y0:y1, x0:x1] = value

    def _draw_hbar(self, mask: torch.Tensor, cy: int, x0: int, x1: int, thickness: int) -> None:
        self._draw_rect(mask, x0, cy - thickness // 2, x1, cy + (thickness + 1) // 2)

    def _draw_vbar(self, mask: torch.Tensor, cx: int, y0: int, y1: int, thickness: int) -> None:
        self._draw_rect(mask, cx - thickness // 2, y0, cx + (thickness + 1) // 2, y1)

    def __getitem__(self, idx: int):
        H = self.img_size
        W = self.img_size

        scaffold = torch.zeros((H, W), dtype=torch.float32)
        occlusion_mask = torch.zeros((H, W), dtype=torch.float32)

        # Geometry.
        cx = random.randint(12, 20)
        cy = random.randint(12, 20)
        t = random.randint(2, 3 if not self.ood else 4)

        # Occluder size: OOD is larger.
        occ_half = random.randint(5, 6) if not self.ood else random.randint(7, 9)
        ox0, ox1 = cx - occ_half, cx + occ_half
        oy0, oy1 = cy - occ_half, cy + occ_half
        self._draw_rect(occlusion_mask, ox0, oy0, ox1, oy1, 1.0)

        # Visible scaffold stubs outside occluder (independent of h,k).
        self._draw_vbar(scaffold, cx, 0, oy0, t)  # top stub
        self._draw_vbar(scaffold, cx, oy1, H, t)  # bottom stub
        self._draw_hbar(scaffold, cy, 0, ox0, t)  # left stub
        self._draw_hbar(scaffold, cy, ox1, W, t)  # right stub

        # Present bit k (carried only by final image, outside occluder).
        k = random.randint(0, 1)
        present_mark = torch.zeros_like(scaffold)
        if k == 1:
            # Small corner patch far from occluder ranges.
            self._draw_rect(present_mark, 1, 1, 5, 5, 1.0)

        # Hidden bit h (carried only by cue image).
        h = random.randint(0, 1)
        cue = torch.zeros_like(scaffold)
        inner_margin = 1 if not self.ood else 2
        ix0, ix1 = ox0 + inner_margin, ox1 - inner_margin
        iy0, iy1 = oy0 + inner_margin, oy1 - inner_margin

        # A cue pattern that reveals h but is not equal to the target completion.
        if h == 0:
            # A left vertical tick inside occluder.
            self._draw_vbar(cue, ix0 + 2, iy0, iy1, max(2, t))
        else:
            # A top horizontal tick inside occluder.
            self._draw_hbar(cue, iy0 + 2, ix0, ix1, max(2, t))

        # Target inside occluder depends on y = h XOR k.
        y = int(h) ^ int(k)
        target_full = torch.zeros_like(scaffold)
        if y == 0:
            # PLUS completion (fully inside the occluder).
            self._draw_vbar(target_full, cx, oy0, oy1, max(2, t))
            self._draw_hbar(target_full, cy, ox0, ox1, max(2, t))
        else:
            # RING completion (fully inside the occluder).
            self._draw_hbar(target_full, iy0 + t // 2, ix0, ix1, t)
            self._draw_hbar(target_full, iy1 - t // 2, ix0, ix1, t)
            self._draw_vbar(target_full, ix0 + t // 2, iy0, iy1, t)
            self._draw_vbar(target_full, ix1 - t // 2, iy0, iy1, t)

        hidden_target = (target_full * occlusion_mask).clamp(0.0, 1.0)

        # Decision-time observable image: scaffold outside occluder + occluder + present mark.
        visible = (scaffold + present_mark).clamp(0.0, 1.0) * (1.0 - occlusion_mask)
        image = torch.clamp(visible + occlusion_mask, 0.0, 1.0)

        # OOD nuisance: sparse distractor flips in cue only.
        if self.ood:
            for _ in range(random.randint(10, 20)):
                yy = random.randint(0, H - 1)
                xx = random.randint(0, W - 1)
                cue[yy, xx] = 1.0 - cue[yy, xx]

        return {
            "cue_image": cue.unsqueeze(0),
            "image": image.unsqueeze(0),
            "hidden_target": hidden_target.unsqueeze(0),
            "occlusion_mask": occlusion_mask.unsqueeze(0),
            "h": torch.tensor(int(h), dtype=torch.long),
            "k": torch.tensor(int(k), dtype=torch.long),
            "y": torch.tensor(int(y), dtype=torch.long),
        }


def get_dataloaders(batch_size: int = 128, steps: int = 3000):
    train_ds = DoubleBarrierHiddenTargetSequenceDataset(size=batch_size * steps, ood=False)
    iid_ds = DoubleBarrierHiddenTargetSequenceDataset(size=1024, ood=False)
    ood_ds = DoubleBarrierHiddenTargetSequenceDataset(size=1024, ood=True)

    train_dl = DataLoader(train_ds, batch_size=batch_size, shuffle=True)
    iid_dl = DataLoader(iid_ds, batch_size=1024, shuffle=False)
    ood_dl = DataLoader(ood_ds, batch_size=1024, shuffle=False)
    return train_dl, iid_dl, ood_dl
