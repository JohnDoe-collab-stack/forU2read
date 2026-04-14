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


def _conv_block(in_ch: int, out_ch: int) -> nn.Sequential:
    return nn.Sequential(
        nn.Conv2d(in_ch, out_ch, 3, padding=1),
        nn.GELU(),
        nn.Conv2d(out_ch, out_ch, 3, padding=1),
        nn.GELU(),
    )


class _UNet32(nn.Module):
    """A small U-Net for 32x32 inputs (global receptive field via downsampling)."""

    def __init__(self, in_ch: int, base: int = 32):
        super().__init__()
        b = int(base)
        self.d1 = _conv_block(in_ch, b)
        self.p1 = nn.MaxPool2d(2)  # 32 -> 16
        self.d2 = _conv_block(b, 2 * b)
        self.p2 = nn.MaxPool2d(2)  # 16 -> 8
        self.d3 = _conv_block(2 * b, 4 * b)
        self.p3 = nn.MaxPool2d(2)  # 8 -> 4

        self.mid = _conv_block(4 * b, 8 * b)

        self.u3 = nn.ConvTranspose2d(8 * b, 4 * b, 2, stride=2)  # 4 -> 8
        self.c3 = _conv_block(8 * b, 4 * b)
        self.u2 = nn.ConvTranspose2d(4 * b, 2 * b, 2, stride=2)  # 8 -> 16
        self.c2 = _conv_block(4 * b, 2 * b)
        self.u1 = nn.ConvTranspose2d(2 * b, b, 2, stride=2)  # 16 -> 32
        self.c1 = _conv_block(2 * b, b)

        self.out = nn.Conv2d(b, 1, 1)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        x1 = self.d1(x)
        x2 = self.d2(self.p1(x1))
        x3 = self.d3(self.p2(x2))
        xm = self.mid(self.p3(x3))

        y3 = self.u3(xm)
        y3 = self.c3(torch.cat([y3, x3], dim=1))
        y2 = self.u2(y3)
        y2 = self.c2(torch.cat([y2, x2], dim=1))
        y1 = self.u1(y2)
        y1 = self.c1(torch.cat([y1, x1], dim=1))
        return self.out(y1)


class VNImageOnlyBaseline(nn.Module):
    def __init__(self, hid: int = 32):
        super().__init__()
        # image + (x,y) coordinate channels
        self.net = _UNet32(3, base=int(hid))

    def forward(self, image: torch.Tensor) -> torch.Tensor:
        return self.net(image)


class VNCueOnlyBaseline(nn.Module):
    def __init__(self, hid: int = 32):
        super().__init__()
        # cue + (x,y) coordinate channels
        self.net = _UNet32(3, base=int(hid))

    def forward(self, cue_image: torch.Tensor) -> torch.Tensor:
        return self.net(cue_image)


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
        # cue + (x,y) coordinate channels: h is encoded via marker position.
        self.cue_enc = _SmallCNN(3, hid=hid)
        self.cue_to_logits = nn.Linear(hid * 32 * 32, self.z_classes)

        # image(+coords) + constant z-map decoded by a global-RF U-Net, so the model
        # can place spatial structure inside a locally-constant occluder region.
        self.dec = _UNet32(3 + self.z_classes, base=int(hid))

    def z_logits(self, cue_image: torch.Tensor) -> torch.Tensor:
        """Logits for the discrete mediator z (depends on cue only)."""
        h = self.cue_enc(cue_image)
        return self.cue_to_logits(h.flatten(1))

    def _z_from_cue(self, cue_image: torch.Tensor) -> torch.Tensor:
        logits = self.z_logits(cue_image)
        # Deterministic hard mediator with a straight-through estimator:
        # - forward uses argmax one-hot
        # - backward uses softmax gradients
        z_soft = F.softmax(logits, dim=-1)
        idx = torch.argmax(z_soft, dim=-1)
        z_hard = F.one_hot(idx, num_classes=self.z_classes).to(dtype=z_soft.dtype)
        return z_hard - z_soft.detach() + z_soft

    def _decode(self, image: torch.Tensor, z: torch.Tensor) -> torch.Tensor:
        z_map = z[:, :, None, None].expand(z.shape[0], z.shape[1], image.shape[2], image.shape[3])
        x = torch.cat([image, z_map], dim=1)
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
