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


class LawV3bUnifiedV1ImageOnlyBaseline(nn.Module):
    def __init__(self, hid: int = 32):
        super().__init__()
        self.net = _UNet32(3, base=int(hid))

    def forward(self, image: torch.Tensor) -> torch.Tensor:
        return self.net(image)


class LawV3bUnifiedV1CueOnlyBaseline(nn.Module):
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


class LawV3bUnifiedV1QueryModelA(nn.Module):
    """
    v3b-style unified variant:

    - `z` carries the missing hidden information (`h`) from cue only.
    - `k` is visible in `image` and is extracted deterministically.
    - The decoder is explicitly conditioned on both `z` and `k_hat`.

    This prevents the failure mode "k is read but segmentation ignores k".
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

        # Condition decoder on: (image, z one-hot, k one-hot)
        self.dec = _UNet32(3 + self.z_classes + 2, base=int(hid))

        # v3b-style query head: choose whether to request the decision-time image.
        # This head must not read the image; it is computed from cue-only state.
        #
        # We implement the policy as a deterministic function of the cue-marker confidence:
        # request_image := (conf > 0).
        # This makes the action a function of internal (cue-derived) state, while keeping the
        # policy stable without introducing an extra supervised signal.
        self.query_mlp = nn.Sequential(
            nn.Linear(3, 32),
            nn.GELU(),
            nn.Linear(32, 2),
        )

    def logits_query(self, cue_image: torch.Tensor) -> torch.Tensor:
        marker = self.cue_to_xy(cue_image)
        return self.query_mlp(marker)

    def chosen_action(self, cue_image: torch.Tensor) -> torch.Tensor:
        """
        v3b-style query action chosen from cue-only internal state.

        Returns: (B,) long tensor with values 0 (no-query) or 1 (query-image).
        """
        marker = self.cue_to_xy(cue_image)
        conf = marker[:, 2]  # (B,)
        return (conf > 0.0).to(dtype=torch.long)

    @staticmethod
    def _response_image_under(*, image: torch.Tensor, action: torch.Tensor) -> torch.Tensor:
        """
        Action-conditioned response.

        If action==1: return the full image (visible,x,y).
        If action==0: zero only the visible channel but keep x,y geometry intact.
        """
        if int(image.shape[1]) != 3:
            raise ValueError(f"_response_image_under expects 3 channels (visible,x,y), got {tuple(image.shape)}")
        a = action.to(device=image.device, dtype=image.dtype).view(-1, 1, 1, 1)  # (B,1,1,1)
        vis = image[:, 0:1] * a
        return torch.cat([vis, image[:, 1:2], image[:, 2:3]], dim=1)

    def z_logits(self, cue_image: torch.Tensor) -> torch.Tensor:
        marker = self.cue_to_xy(cue_image)
        return self.z_mlp(marker)

    @staticmethod
    def k_hat_from_image(image: torch.Tensor) -> torch.Tensor:
        """
        Deterministic extraction of k from the decision-time response image.

        image: (B,3,H,W) = (visible, x, y)
        k is encoded as a full-width bright band on rows [0:3] in channel 0 when k=1.
        """
        if int(image.shape[1]) != 3:
            raise ValueError(f"k_hat_from_image expects 3 channels (visible,x,y), got {tuple(image.shape)}")
        band = image[:, 0:1, 0:3, :]  # (B,1,3,W)
        m = band.mean(dim=(1, 2, 3))  # (B,)
        return (m > 0.5).to(dtype=torch.long)

    def _z_from_cue(self, cue_image: torch.Tensor) -> torch.Tensor:
        logits = self.z_logits(cue_image)
        z_soft = F.softmax(logits, dim=-1)
        idx = torch.argmax(z_soft, dim=-1)
        z_hard = F.one_hot(idx, num_classes=self.z_classes).to(dtype=z_soft.dtype)
        return z_hard - z_soft.detach() + z_soft

    def _k_from_image(self, image: torch.Tensor) -> torch.Tensor:
        k = self.k_hat_from_image(image)
        k_oh = F.one_hot(k, num_classes=2).to(dtype=image.dtype)
        return k_oh

    def _decode(self, image: torch.Tensor, z: torch.Tensor, k_oh: torch.Tensor) -> torch.Tensor:
        z_map = z[:, :, None, None].expand(z.shape[0], z.shape[1], image.shape[2], image.shape[3])
        k_map = k_oh[:, :, None, None].expand(k_oh.shape[0], k_oh.shape[1], image.shape[2], image.shape[3])
        x = torch.cat([image, z_map, k_map], dim=1)
        return self.dec(x)

    def forward(self, cue_image: torch.Tensor, image: torch.Tensor) -> torch.Tensor:
        # v3b-style: query action from cue-only state; response conditioned on action.
        action = self.chosen_action(cue_image)
        resp = self._response_image_under(image=image, action=action)
        z = self._z_from_cue(cue_image)
        k_oh = self._k_from_image(resp)
        return self._decode(resp, z, k_oh)

    def forward_under(self, cue_image: torch.Tensor, image: torch.Tensor, *, action: torch.Tensor) -> torch.Tensor:
        resp = self._response_image_under(image=image, action=action)
        z = self._z_from_cue(cue_image)
        k_oh = self._k_from_image(resp)
        return self._decode(resp, z, k_oh)

    def swap_forward(self, cue_image: torch.Tensor, image: torch.Tensor, perm: torch.Tensor) -> torch.Tensor:
        action = self.chosen_action(cue_image)
        resp = self._response_image_under(image=image, action=action)
        z = self._z_from_cue(cue_image)
        z_swap = z[perm]
        k_oh = self._k_from_image(resp)
        return self._decode(resp, z_swap, k_oh)

    def ablated_forward(self, cue_image: torch.Tensor, image: torch.Tensor) -> torch.Tensor:
        B = cue_image.shape[0]
        action = self.chosen_action(cue_image)
        resp = self._response_image_under(image=image, action=action)
        z = torch.zeros((B, self.z_classes), device=cue_image.device, dtype=cue_image.dtype)
        k_oh = self._k_from_image(resp)
        return self._decode(resp, z, k_oh)
