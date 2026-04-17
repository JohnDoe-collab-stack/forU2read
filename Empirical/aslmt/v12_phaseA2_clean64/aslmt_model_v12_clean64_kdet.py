from __future__ import annotations

import torch
import torch.nn as nn
import torch.nn.functional as F


def _dense_2x2_argmax(cue_ch: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
    """
    cue_ch: (B,1,H,W) in [0,1]
    Returns (x0,y0,score) for the best 2×2 window.
    """
    B, C, H, W = cue_ch.shape
    if int(C) != 1:
        raise ValueError(f"_dense_2x2_argmax expects C==1, got {tuple(cue_ch.shape)}")
    s = cue_ch[:, :, 0 : H - 1, 0 : W - 1] + cue_ch[:, :, 1:H, 0 : W - 1] + cue_ch[:, :, 0 : H - 1, 1:W] + cue_ch[:, :, 1:H, 1:W]
    s = s[:, 0]  # (B,H-1,W-1)
    flat = s.reshape(int(B), -1)
    idx = torch.argmax(flat, dim=1)  # (B,)
    y0 = idx // int(W - 1)
    x0 = idx % int(W - 1)
    score = flat[torch.arange(int(B), device=cue_ch.device), idx]
    return x0, y0, score


class _CueMarkerToXYDet(nn.Module):
    def forward(self, cue: torch.Tensor) -> torch.Tensor:
        # cue: (B,3,H,W) = (cue, x, y)
        B, C, H, W = cue.shape
        if int(C) != 3:
            raise ValueError(f"_CueMarkerToXYDet expects 3 channels (cue,x,y), got {tuple(cue.shape)}")
        cue_ch = cue[:, 0:1]
        x_ch = cue[:, 1:2]
        y_ch = cue[:, 2:3]

        x0, y0, score = _dense_2x2_argmax(cue_ch)

        xs = []
        ys = []
        for dy in (0, 1):
            for dx in (0, 1):
                xs.append(x_ch[torch.arange(B, device=cue.device), 0, (y0 + dy), (x0 + dx)])
                ys.append(y_ch[torch.arange(B, device=cue.device), 0, (y0 + dy), (x0 + dx)])
        x_mean = torch.stack(xs, dim=1).mean(dim=1, keepdim=True)
        y_mean = torch.stack(ys, dim=1).mean(dim=1, keepdim=True)
        conf = score / 4.0
        return torch.cat([x_mean, y_mean, conf], dim=1)


class _ConvBlock(nn.Module):
    def __init__(self, cin: int, cout: int):
        super().__init__()
        self.net = nn.Sequential(
            nn.Conv2d(int(cin), int(cout), 3, padding=1),
            nn.GELU(),
            nn.Conv2d(int(cout), int(cout), 3, padding=1),
            nn.GELU(),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x)


class _UNetSmall(nn.Module):
    def __init__(self, cin: int, base: int = 32):
        super().__init__()
        b = int(base)
        self.d0 = _ConvBlock(int(cin), b)
        self.p0 = nn.MaxPool2d(2)
        self.d1 = _ConvBlock(b, 2 * b)
        self.p1 = nn.MaxPool2d(2)
        self.mid = _ConvBlock(2 * b, 4 * b)
        self.u1 = nn.Upsample(scale_factor=2, mode="nearest")
        self.u1c = _ConvBlock(4 * b + 2 * b, 2 * b)
        self.u0 = nn.Upsample(scale_factor=2, mode="nearest")
        self.u0c = _ConvBlock(2 * b + b, b)
        self.out = nn.Conv2d(b, 1, 1)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        x0 = self.d0(x)
        x1 = self.d1(self.p0(x0))
        xm = self.mid(self.p1(x1))
        y1 = self.u1c(torch.cat([self.u1(xm), x1], dim=1))
        y0 = self.u0c(torch.cat([self.u0(y1), x0], dim=1))
        return self.out(y0)


class V12Clean64ModelA(nn.Module):
    """
    - z from cue only (det marker -> xy -> z logits)
    - k from image deterministically (top band)
    - decoder conditioned on (image, z, k)
    """

    def __init__(self, *, z_classes: int, hid: int = 32):
        super().__init__()
        self.z_classes = int(z_classes)
        self.cue_to_xy = _CueMarkerToXYDet()
        self.z_mlp = nn.Sequential(nn.Linear(3, 64), nn.GELU(), nn.Linear(64, self.z_classes))
        self.dec = _UNetSmall(3 + self.z_classes + 2, base=int(hid))

    def z_logits(self, cue_image: torch.Tensor) -> torch.Tensor:
        marker = self.cue_to_xy(cue_image)
        return self.z_mlp(marker)

    @staticmethod
    def k_hat_from_image(image: torch.Tensor) -> torch.Tensor:
        if int(image.shape[1]) != 3:
            raise ValueError(f"k_hat_from_image expects 3 channels (visible,x,y), got {tuple(image.shape)}")
        band = image[:, 0:1, 0:3, :]
        m = band.mean(dim=(1, 2, 3))
        return (m > 0.5).to(dtype=torch.long)

    def _z_from_cue(self, cue_image: torch.Tensor) -> torch.Tensor:
        logits = self.z_logits(cue_image)
        z_soft = F.softmax(logits, dim=-1)
        idx = torch.argmax(z_soft, dim=-1)
        z_hard = F.one_hot(idx, num_classes=self.z_classes).to(dtype=z_soft.dtype)
        return z_hard - z_soft.detach() + z_soft

    def _k_from_image(self, image: torch.Tensor) -> torch.Tensor:
        k = self.k_hat_from_image(image)
        return F.one_hot(k, num_classes=2).to(dtype=image.dtype)

    def _decode(self, image: torch.Tensor, z: torch.Tensor, k_oh: torch.Tensor) -> torch.Tensor:
        z_map = z[:, :, None, None].expand(z.shape[0], z.shape[1], image.shape[2], image.shape[3])
        k_map = k_oh[:, :, None, None].expand(k_oh.shape[0], k_oh.shape[1], image.shape[2], image.shape[3])
        x = torch.cat([image, z_map, k_map], dim=1)
        return self.dec(x)

    def forward(self, cue_image: torch.Tensor, image: torch.Tensor) -> torch.Tensor:
        z = self._z_from_cue(cue_image)
        k_oh = self._k_from_image(image)
        return self._decode(image, z, k_oh)

    def swap_forward(self, cue_image: torch.Tensor, image: torch.Tensor, perm: torch.Tensor) -> torch.Tensor:
        z = self._z_from_cue(cue_image)
        z_swap = z[perm]
        k_oh = self._k_from_image(image)
        return self._decode(image, z_swap, k_oh)

    def ablated_forward(self, cue_image: torch.Tensor, image: torch.Tensor) -> torch.Tensor:
        B = int(cue_image.shape[0])
        z = torch.zeros((B, self.z_classes), device=cue_image.device, dtype=cue_image.dtype)
        k_oh = self._k_from_image(image)
        return self._decode(image, z, k_oh)


class V12Clean64ImageOnlyBaseline(nn.Module):
    def __init__(self):
        super().__init__()
        self.net = _UNetSmall(3, base=32)

    def forward(self, image: torch.Tensor) -> torch.Tensor:
        return self.net(image)


class V12Clean64CueOnlyBaseline(nn.Module):
    def __init__(self):
        super().__init__()
        self.net = _UNetSmall(3, base=32)

    def forward(self, cue: torch.Tensor) -> torch.Tensor:
        return self.net(cue)

