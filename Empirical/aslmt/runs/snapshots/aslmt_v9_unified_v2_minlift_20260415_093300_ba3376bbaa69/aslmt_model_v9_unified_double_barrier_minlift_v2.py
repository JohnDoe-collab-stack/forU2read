import torch
import torch.nn as nn
import torch.nn.functional as F


def _conv_block(in_ch: int, out_ch: int) -> nn.Sequential:
    return nn.Sequential(
        nn.Conv2d(in_ch, out_ch, 3, padding=1),
        nn.GELU(),
        nn.Conv2d(out_ch, out_ch, 3, padding=1),
        nn.GELU(),
    )


class _UNet32(nn.Module):
    def __init__(self, in_ch: int, base: int = 32):
        super().__init__()
        b = int(base)
        self.d1 = _conv_block(in_ch, b)
        self.p1 = nn.MaxPool2d(2)
        self.d2 = _conv_block(b, 2 * b)
        self.p2 = nn.MaxPool2d(2)
        self.d3 = _conv_block(2 * b, 4 * b)
        self.p3 = nn.MaxPool2d(2)

        self.mid = _conv_block(4 * b, 8 * b)

        self.u3 = nn.ConvTranspose2d(8 * b, 4 * b, 2, stride=2)
        self.c3 = _conv_block(8 * b, 4 * b)
        self.u2 = nn.ConvTranspose2d(4 * b, 2 * b, 2, stride=2)
        self.c2 = _conv_block(4 * b, 2 * b)
        self.u1 = nn.ConvTranspose2d(2 * b, b, 2, stride=2)
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


class V9ImageOnlyBaseline(nn.Module):
    def __init__(self, hid: int = 32):
        super().__init__()
        self.net = _UNet32(3, base=int(hid))

    def forward(self, image: torch.Tensor) -> torch.Tensor:
        return self.net(image)


class V9CueOnlyBaseline(nn.Module):
    def __init__(self, hid: int = 32):
        super().__init__()
        self.net = _UNet32(3, base=int(hid))

    def forward(self, cue_image: torch.Tensor) -> torch.Tensor:
        return self.net(cue_image)


def _dense_2x2_argmax(cue_ch: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
    B, C, H, W = cue_ch.shape
    if int(C) != 1:
        raise ValueError(f"_dense_2x2_argmax expects (B,1,H,W), got {tuple(cue_ch.shape)}")
    k = torch.ones((1, 1, 2, 2), device=cue_ch.device, dtype=cue_ch.dtype)
    s = F.conv2d(cue_ch, k, padding=0)  # (B,1,H-1,W-1)
    flat = s.flatten(1)
    idx = torch.argmax(flat, dim=1)  # (B,)
    y0 = idx // (W - 1)
    x0 = idx % (W - 1)
    score = flat.gather(1, idx[:, None])  # (B,1)
    return x0.to(torch.long), y0.to(torch.long), score


class _CueMarkerToXYDet(nn.Module):
    def __init__(self):
        super().__init__()

    def forward(self, cue: torch.Tensor) -> torch.Tensor:
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


class V9MinLiftModelA(nn.Module):
    """
    v2: inject an explicit learned visible-bit summary (k) into the decoder input,
    so the cue-barrier becomes stable without relying on the raw pixel readout.
    """

    def __init__(self, *, z_classes: int, hid: int = 32):
        super().__init__()
        self.z_classes = int(z_classes)
        assert self.z_classes >= 1

        self.cue_to_xy = _CueMarkerToXYDet()
        self.z_mlp = nn.Sequential(
            nn.Linear(3, 64),
            nn.GELU(),
            nn.Linear(64, self.z_classes),
        )

        self.k_head = nn.Sequential(
            nn.Conv2d(3, 16, 3, padding=1),
            nn.GELU(),
            nn.Conv2d(16, 16, 3, padding=1),
            nn.GELU(),
            nn.AdaptiveAvgPool2d(1),
        )
        self.k_fc = nn.Linear(16, 2)

        self.dec = _UNet32(3 + self.z_classes + 2, base=int(hid))

    def z_logits(self, cue_image: torch.Tensor) -> torch.Tensor:
        marker = self.cue_to_xy(cue_image)
        return self.z_mlp(marker)

    def k_logits(self, image: torch.Tensor) -> torch.Tensor:
        feat = self.k_head(image).flatten(1)
        return self.k_fc(feat)

    def _z_from_cue(self, cue_image: torch.Tensor) -> torch.Tensor:
        logits = self.z_logits(cue_image)
        z_soft = F.softmax(logits, dim=-1)
        idx = torch.argmax(z_soft, dim=-1)
        z_hard = F.one_hot(idx, num_classes=self.z_classes).to(dtype=z_soft.dtype)
        return z_hard - z_soft.detach() + z_soft

    def _k_from_image(self, image: torch.Tensor) -> torch.Tensor:
        logits = self.k_logits(image)
        k_soft = F.softmax(logits, dim=-1)
        idx = torch.argmax(k_soft, dim=-1)
        k_hard = F.one_hot(idx, num_classes=2).to(dtype=k_soft.dtype)
        return k_hard - k_soft.detach() + k_soft

    def _decode(self, image: torch.Tensor, z: torch.Tensor, k: torch.Tensor) -> torch.Tensor:
        z_map = z[:, :, None, None].expand(z.shape[0], z.shape[1], image.shape[2], image.shape[3])
        k_map = k[:, :, None, None].expand(k.shape[0], k.shape[1], image.shape[2], image.shape[3])
        x = torch.cat([image, z_map, k_map], dim=1)
        return self.dec(x)

    def forward(self, cue_image: torch.Tensor, image: torch.Tensor) -> torch.Tensor:
        z = self._z_from_cue(cue_image)
        k = self._k_from_image(image)
        return self._decode(image, z, k)

    def swap_forward(self, cue_image: torch.Tensor, image: torch.Tensor, perm: torch.Tensor) -> torch.Tensor:
        z = self._z_from_cue(cue_image)
        z_swap = z[perm]
        k = self._k_from_image(image)
        return self._decode(image, z_swap, k)

    def ablated_forward(self, cue_image: torch.Tensor, image: torch.Tensor) -> torch.Tensor:
        B = cue_image.shape[0]
        z = torch.zeros((B, self.z_classes), device=cue_image.device, dtype=cue_image.dtype)
        k = self._k_from_image(image)
        return self._decode(image, z, k)

