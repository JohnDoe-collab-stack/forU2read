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


class LawV3bUnifiedV2StrongQForcedImageOnlyBaseline(nn.Module):
    def __init__(self, hid: int = 32):
        super().__init__()
        self.net = _UNet32(3, base=int(hid))

    def forward(self, image: torch.Tensor) -> torch.Tensor:
        return self.net(image)


class LawV3bUnifiedV2StrongQForcedCueOnlyBaseline(nn.Module):
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


class LawV3bUnifiedV2StrongQForcedQueryModelA(nn.Module):
    """
    Negative control: force query action to constant 0.

    Intended to fail strict `solid` verification (`q_acc` and action-rate constraints).
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

        self.dec = _UNet32(3 + self.z_classes + 2, base=int(hid))
        self.query_from_z = nn.Linear(self.z_classes, 2)

    def logits_query(self, cue_image: torch.Tensor) -> torch.Tensor:
        B = int(cue_image.shape[0])
        logits = torch.tensor([10.0, 0.0], device=cue_image.device, dtype=cue_image.dtype)
        return logits[None, :].expand(B, 2)

    def chosen_action(self, cue_image: torch.Tensor) -> torch.Tensor:
        logits = self.logits_query(cue_image)
        return torch.argmax(logits, dim=-1).to(dtype=torch.long)

    def z_logits(self, cue_image: torch.Tensor) -> torch.Tensor:
        marker = self.cue_to_xy(cue_image)
        return self.z_mlp(marker)

    def _z_from_cue(self, cue_image: torch.Tensor) -> torch.Tensor:
        logits = self.z_logits(cue_image)
        z_soft = F.softmax(logits, dim=-1)
        idx = torch.argmax(z_soft, dim=-1)
        z_hard = F.one_hot(idx, num_classes=self.z_classes).to(dtype=z_soft.dtype)
        return z_hard - z_soft.detach() + z_soft

    @staticmethod
    def _res_from_res_bit(res_bit: torch.Tensor, *, dtype: torch.dtype) -> torch.Tensor:
        r = res_bit.to(dtype=torch.long)
        return F.one_hot(r, num_classes=2).to(dtype=dtype)

    def _decode(self, image: torch.Tensor, z: torch.Tensor, r_oh: torch.Tensor) -> torch.Tensor:
        z_map = z[:, :, None, None].expand(z.shape[0], z.shape[1], image.shape[2], image.shape[3])
        r_map = r_oh[:, :, None, None].expand(r_oh.shape[0], r_oh.shape[1], image.shape[2], image.shape[3])
        x = torch.cat([image, z_map, r_map], dim=1)
        return self.dec(x)

    def forward_with_res_bit(self, cue_image: torch.Tensor, image: torch.Tensor, *, res_bit: torch.Tensor) -> torch.Tensor:
        z = self._z_from_cue(cue_image)
        r_oh = self._res_from_res_bit(res_bit, dtype=image.dtype)
        return self._decode(image, z, r_oh)

    def swap_forward_with_res_bit(
        self, cue_image: torch.Tensor, image: torch.Tensor, *, res_bit: torch.Tensor, perm: torch.Tensor
    ) -> torch.Tensor:
        z = self._z_from_cue(cue_image)
        z_swap = z[perm]
        r_oh = self._res_from_res_bit(res_bit, dtype=image.dtype)
        return self._decode(image, z_swap, r_oh)

    def ablated_forward_with_res_bit(self, cue_image: torch.Tensor, image: torch.Tensor, *, res_bit: torch.Tensor) -> torch.Tensor:
        B = cue_image.shape[0]
        z = torch.zeros((B, self.z_classes), device=cue_image.device, dtype=cue_image.dtype)
        r_oh = self._res_from_res_bit(res_bit, dtype=image.dtype)
        return self._decode(image, z, r_oh)


__all__ = [
    "LawV3bUnifiedV2StrongQForcedQueryModelA",
    "LawV3bUnifiedV2StrongQForcedImageOnlyBaseline",
    "LawV3bUnifiedV2StrongQForcedCueOnlyBaseline",
]

