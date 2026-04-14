import torch
import torch.nn as nn
import torch.nn.functional as F


class _SmallCNN(nn.Module):
    def __init__(self, in_ch: int, hid: int = 32):
        super().__init__()
        self.net = nn.Sequential(
            nn.Conv2d(in_ch, hid, 3, padding=1),
            nn.GELU(),
            nn.Conv2d(hid, hid, 3, padding=1),
            nn.GELU(),
            nn.Conv2d(hid, hid, 3, padding=1),
            nn.GELU(),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x)


class VNImageOnlyBaseline(nn.Module):
    def __init__(self, hid: int = 32):
        super().__init__()
        self.enc = _SmallCNN(1, hid=hid)
        self.head = nn.Conv2d(hid, 1, 1)

    def forward(self, image: torch.Tensor) -> torch.Tensor:
        return self.head(self.enc(image))


class VNCueOnlyBaseline(nn.Module):
    def __init__(self, hid: int = 32):
        super().__init__()
        self.enc = _SmallCNN(1, hid=hid)
        self.head = nn.Conv2d(hid, 1, 1)

    def forward(self, cue_image: torch.Tensor) -> torch.Tensor:
        return self.head(self.enc(cue_image))


class VNMinLiftModelA(nn.Module):
    """
    Model A with an explicit *discrete* mediator `z ∈ {0..z_classes-1}`.

    - cue_image -> z_logits -> hard one-hot z
    - output depends only on (image, z), not on cue_image directly
    """

    def __init__(self, *, z_classes: int, hid: int = 32):
        super().__init__()
        self.z_classes = int(z_classes)
        assert self.z_classes >= 1

        # IMPORTANT: cue encodes `h` via *marker position*, so the z-readout must
        # not collapse spatial coordinates (e.g. via global average pooling).
        self.cue_enc = _SmallCNN(1, hid=hid)
        self.cue_to_logits = nn.Linear(hid * 32 * 32, self.z_classes)

        self.img_enc = _SmallCNN(1, hid=hid)

        self.dec = nn.Sequential(
            nn.Conv2d(hid + self.z_classes, hid, 3, padding=1),
            nn.GELU(),
            nn.Conv2d(hid, hid, 3, padding=1),
            nn.GELU(),
            nn.Conv2d(hid, 1, 1),
        )

    def _z_from_cue(self, cue_image: torch.Tensor) -> torch.Tensor:
        h = self.cue_enc(cue_image)
        logits = self.cue_to_logits(h.flatten(1))
        # Deterministic hard mediator with a straight-through estimator:
        # - forward uses argmax one-hot
        # - backward uses softmax gradients
        z_soft = F.softmax(logits, dim=-1)
        idx = torch.argmax(z_soft, dim=-1)
        z_hard = F.one_hot(idx, num_classes=self.z_classes).to(dtype=z_soft.dtype)
        return z_hard - z_soft.detach() + z_soft

    def _decode(self, image: torch.Tensor, z: torch.Tensor) -> torch.Tensor:
        img_h = self.img_enc(image)
        z_map = z[:, :, None, None].expand(z.shape[0], z.shape[1], img_h.shape[2], img_h.shape[3])
        x = torch.cat([img_h, z_map], dim=1)
        return self.dec(x)

    def forward(self, cue_image: torch.Tensor, image: torch.Tensor) -> torch.Tensor:
        z = self._z_from_cue(cue_image)
        return self._decode(image, z)

    def swap_forward(self, cue_image: torch.Tensor, image: torch.Tensor, perm: torch.Tensor) -> torch.Tensor:
        z = self._z_from_cue(cue_image)
        z_swap = z[perm]
        return self._decode(image, z_swap)

    def ablated_forward(self, cue_image: torch.Tensor, image: torch.Tensor) -> torch.Tensor:
        B = cue_image.shape[0]
        z = torch.zeros((B, self.z_classes), device=cue_image.device, dtype=cue_image.dtype)
        return self._decode(image, z)
