import random
import torch
from torch.utils.data import Dataset, DataLoader


class PerfectAmodalHiddenTargetSequenceDataset(Dataset):
    """
    Temporal witness for amodal completion with a strict visible-only barrier at decision time.

    Frames:
    - cue_image: reveals the hidden completion class (only inside the occluder)
    - image: final visible image (scaffold + occluder), independent of the hidden class

    Target:
    - hidden_target: the hidden completion *inside the occluder only*.

    This makes the metric measure the real barrier: resolving the occluded content,
    not reconstructing the visible scaffold.
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
        amodal_mask = torch.zeros((H, W), dtype=torch.float32)
        occlusion_mask = torch.zeros((H, W), dtype=torch.float32)

        # Center and thickness.
        cx = random.randint(12, 20)
        cy = random.randint(12, 20)
        t = random.randint(2, 3 if not self.ood else 4)

        # Occluder size: OOD is larger.
        occ_half = random.randint(5, 6) if not self.ood else random.randint(7, 9)
        ox0, ox1 = cx - occ_half, cx + occ_half
        oy0, oy1 = cy - occ_half, cy + occ_half
        self._draw_rect(occlusion_mask, ox0, oy0, ox1, oy1, 1.0)

        # Visible scaffold outside the occluder: identical for both classes.
        self._draw_vbar(amodal_mask, cx, 0, oy0, t)  # top stub
        self._draw_vbar(amodal_mask, cx, oy1, H, t)  # bottom stub
        self._draw_hbar(amodal_mask, cy, 0, ox0, t)  # left stub
        self._draw_hbar(amodal_mask, cy, ox1, W, t)  # right stub

        # Hidden completion inside the occluder.
        hidden_label = random.randint(0, 1)
        hidden = torch.zeros_like(amodal_mask)

        inner_margin = 1 if not self.ood else 2
        ix0, ix1 = ox0 + inner_margin, ox1 - inner_margin
        iy0, iy1 = oy0 + inner_margin, oy1 - inner_margin

        if hidden_label == 0:
            # PLUS completion (fully inside the occluder).
            self._draw_vbar(hidden, cx, oy0, oy1, max(2, t))
            self._draw_hbar(hidden, cy, ox0, ox1, max(2, t))
        else:
            # RING completion (fully inside the occluder).
            self._draw_hbar(hidden, iy0 + t // 2, ix0, ix1, t)
            self._draw_hbar(hidden, iy1 - t // 2, ix0, ix1, t)
            self._draw_vbar(hidden, ix0 + t // 2, iy0, iy1, t)
            self._draw_vbar(hidden, ix1 - t // 2, iy0, iy1, t)

        amodal_mask = torch.clamp(amodal_mask + hidden, 0.0, 1.0)
        visible_mask = amodal_mask * (1.0 - occlusion_mask)

        # Final visible image: visible scaffold + occluder only, independent of hidden_label.
        image = torch.clamp(visible_mask + occlusion_mask, 0.0, 1.0)

        # Cue reveals only the hidden completion pattern.
        cue_image = hidden.clone()

        # Hidden-only target (inside occluder region).
        hidden_target = hidden * occlusion_mask

        # OOD nuisance: add sparse distractor flips in cue only (keep final image barrier strict).
        if self.ood:
            for _ in range(random.randint(10, 20)):
                y = random.randint(0, H - 1)
                x = random.randint(0, W - 1)
                cue_image[y, x] = 1.0 - cue_image[y, x]

        return {
            "cue_image": cue_image.unsqueeze(0),
            "image": image.unsqueeze(0),
            "hidden_target": hidden_target.unsqueeze(0),
            "occlusion_mask": occlusion_mask.unsqueeze(0),
            "hidden_label": torch.tensor(hidden_label, dtype=torch.long),
        }


def get_dataloaders(batch_size: int = 128, steps: int = 3000):
    train_ds = PerfectAmodalHiddenTargetSequenceDataset(size=batch_size * steps, ood=False)
    iid_ds = PerfectAmodalHiddenTargetSequenceDataset(size=1024, ood=False)
    ood_ds = PerfectAmodalHiddenTargetSequenceDataset(size=1024, ood=True)

    train_dl = DataLoader(train_ds, batch_size=batch_size, shuffle=True)
    iid_dl = DataLoader(iid_ds, batch_size=1024, shuffle=False)
    ood_dl = DataLoader(ood_ds, batch_size=1024, shuffle=False)
    return train_dl, iid_dl, ood_dl

