#!/usr/bin/env python3
from __future__ import annotations

import copy

import torch
import torch.nn as nn
import torch.nn.functional as F


class _Attention(nn.Module):
    def __init__(self, dim: int, num_heads: int = 4):
        super().__init__()
        self.num_heads = int(num_heads)
        self.scale = (dim // self.num_heads) ** -0.5
        self.qkv = nn.Linear(dim, dim * 3, bias=False)
        self.proj = nn.Linear(dim, dim)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        B, N, C = x.shape
        qkv = self.qkv(x).reshape(B, N, 3, self.num_heads, C // self.num_heads).permute(2, 0, 3, 1, 4)
        q, k, v = qkv[0], qkv[1], qkv[2]
        attn = (q @ k.transpose(-2, -1)) * self.scale
        attn = attn.softmax(dim=-1)
        out = (attn @ v).transpose(1, 2).reshape(B, N, C)
        return self.proj(out)


class _TransformerBlock(nn.Module):
    def __init__(self, dim: int, num_heads: int = 4, mlp_ratio: float = 4.0):
        super().__init__()
        self.norm1 = nn.LayerNorm(dim)
        self.attn = _Attention(dim, num_heads=num_heads)
        self.norm2 = nn.LayerNorm(dim)
        hidden_dim = int(dim * float(mlp_ratio))
        self.mlp = nn.Sequential(nn.Linear(dim, hidden_dim), nn.GELU(), nn.Linear(hidden_dim, dim))

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        x = x + self.attn(self.norm1(x))
        x = x + self.mlp(self.norm2(x))
        return x


class _SimpleViT(nn.Module):
    def __init__(
        self,
        img_size: int = 32,
        patch_size: int = 4,
        in_chans: int = 1,
        embed_dim: int = 96,
        depth: int = 3,
        num_heads: int = 4,
    ):
        super().__init__()
        self.patch_embed = nn.Conv2d(in_chans, embed_dim, kernel_size=patch_size, stride=patch_size)
        num_patches = (img_size // patch_size) ** 2
        self.pos_embed = nn.Parameter(torch.zeros(1, num_patches, embed_dim))
        self.blocks = nn.ModuleList([_TransformerBlock(dim=embed_dim, num_heads=num_heads) for _ in range(int(depth))])
        self.norm = nn.LayerNorm(embed_dim)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        x = self.patch_embed(x).flatten(2).transpose(1, 2)
        x = x + self.pos_embed
        for blk in self.blocks:
            x = blk(x)
        return self.norm(x)


class LawV5bAmodalCausalJEPA(nn.Module):
    """
    Model A:
    - encoder(x_visible) -> pooled -> z
    - head reads *only z* (state-locked)
    - JEPA predictor uses z + per-patch position embedding to predict target-encoder(full-mask) tokens.
    """

    def __init__(self, *, embed_dim: int = 96, d_latent: int = 128, ema_decay: float = 0.99, img_size: int = 32, patch_size: int = 4):
        super().__init__()
        self.ema_decay = float(ema_decay)

        self.encoder = _SimpleViT(img_size=img_size, patch_size=patch_size, in_chans=1, embed_dim=embed_dim, depth=3, num_heads=4)
        self.gate_proj = nn.Sequential(
            nn.Linear(embed_dim, d_latent),
            nn.LayerNorm(d_latent),
            nn.GELU(),
            nn.Linear(d_latent, d_latent),
        )

        self.target_encoder = copy.deepcopy(self.encoder)
        for p in self.target_encoder.parameters():
            p.requires_grad = False

        self.predictor = nn.Sequential(
            nn.Linear(d_latent + embed_dim, embed_dim * 2),
            nn.LayerNorm(embed_dim * 2),
            nn.GELU(),
            nn.Linear(embed_dim * 2, embed_dim),
        )

        # state-lock: decode from z only
        self.amodal_head = nn.Sequential(
            nn.Linear(d_latent, 256),
            nn.LayerNorm(256),
            nn.GELU(),
            nn.Linear(256, img_size * img_size),
        )

        self._img_size = int(img_size)

    @torch.no_grad()
    def ema_update(self) -> None:
        m = self.ema_decay
        for p_t, p in zip(self.target_encoder.parameters(), self.encoder.parameters()):
            p_t.data.mul_(m).add_(p.data, alpha=(1.0 - m))

    def compute_latent(self, x: torch.Tensor) -> torch.Tensor:
        h = self.encoder(x)  # [B, N, E]
        z = self.gate_proj(h.mean(dim=1))
        return z

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        z = self.compute_latent(x)
        out = self.amodal_head(z)
        return out.view(-1, 1, self._img_size, self._img_size)

    def swap_forward(self, x: torch.Tensor, perm: torch.Tensor) -> torch.Tensor:
        z = self.compute_latent(x)
        out = self.amodal_head(z[perm])
        return out.view(-1, 1, self._img_size, self._img_size)

    def jepa_forward(self, *, x_visible: torch.Tensor, full_mask: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        z = self.compute_latent(x_visible)  # [B, D]
        with torch.no_grad():
            t_full = self.target_encoder(full_mask)
            t_full = F.normalize(t_full, dim=-1)
        B, N, _ = t_full.shape
        z_exp = z.unsqueeze(1).expand(B, N, -1)
        pos = self.target_encoder.pos_embed.expand(B, N, -1)
        p_full = self.predictor(torch.cat([z_exp, pos], dim=-1))
        p_full = F.normalize(p_full, dim=-1)
        return p_full, t_full, z


class LawV5bVisibleOnlyLocalFCN(nn.Module):
    """
    Local baseline B1 (shallow):
    - strictly local FCN (bounded receptive field)
    - no global latent `z`
    """

    def __init__(self, *, width: int = 64):
        super().__init__()
        w = int(width)
        self.net = nn.Sequential(
            nn.Conv2d(1, w, kernel_size=3, padding=1),
            nn.GELU(),
            nn.Conv2d(w, w, kernel_size=3, padding=1),
            nn.GELU(),
            nn.Conv2d(w, w, kernel_size=3, padding=1),
            nn.GELU(),
            nn.Conv2d(w, 1, kernel_size=3, padding=1),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x)


class LawV5bVisibleOnlyLocalFCNWideRF9(nn.Module):
    """
    Local baseline B2 (wider, RF-fixed):
    - strictly local FCN with the **same receptive field bound** as B1 (RF=9),
      but with much higher channel capacity.
    - uses extra 1x1 layers to increase capacity without increasing receptive field.

    This is deliberate: v5b tests a *declared r-local class* (here, effectively RF=9),
    not "any conv of any depth".
    """

    def __init__(self, *, width: int = 256):
        super().__init__()
        w = int(width)
        # 3x3 conv count = 4 => RF = 1 + 2*4 = 9.
        self.net = nn.Sequential(
            nn.Conv2d(1, w, kernel_size=3, padding=1),
            nn.GELU(),
            nn.Conv2d(w, w, kernel_size=3, padding=1),
            nn.GELU(),
            nn.Conv2d(w, w, kernel_size=3, padding=1),
            nn.GELU(),
            # capacity boosters (do not expand RF)
            nn.Conv2d(w, w, kernel_size=1),
            nn.GELU(),
            nn.Conv2d(w, w, kernel_size=1),
            nn.GELU(),
            nn.Conv2d(w, 1, kernel_size=3, padding=1),
        )
        self.receptive_field = 9

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x)


class LawV5bVisibleOnlyWindowMLP(nn.Module):
    """
    Local baseline B3 (window-local MLP):
    - partitions the image into non-overlapping windows
    - applies the same per-window MLP
    - no cross-window communication (strict window locality)
    """

    def __init__(self, *, img_size: int = 32, window: int = 8, hidden: int = 256):
        super().__init__()
        self.img_size = int(img_size)
        self.window = int(window)
        if self.img_size % self.window != 0:
            raise ValueError("img_size must be divisible by window")
        d = self.window * self.window
        h = int(hidden)
        self.mlp = nn.Sequential(nn.Linear(d, h), nn.GELU(), nn.Linear(h, d))

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        # x: [B, 1, H, W]
        B, C, H, W = x.shape
        if C != 1 or H != self.img_size or W != self.img_size:
            raise ValueError("unexpected input shape")
        ws = self.window
        # [B, 1, H/ws, W/ws, ws, ws]
        xw = x.unfold(2, ws, ws).unfold(3, ws, ws)
        # [B, H/ws, W/ws, ws*ws]
        xw = xw.contiguous().view(B, 1, H // ws, W // ws, ws * ws).squeeze(1)
        flat = xw.view(B * (H // ws) * (W // ws), ws * ws)
        y = self.mlp(flat)
        y = y.view(B, H // ws, W // ws, ws, ws)
        # stitch back
        y = y.permute(0, 1, 3, 2, 4).contiguous().view(B, 1, H, W)
        return y


def local_baseline_builders(*, img_size: int = 32) -> dict[str, nn.Module]:
    return {
        "B1_local_fcn": LawV5bVisibleOnlyLocalFCN(width=64),
        "B2_local_fcn_wide_rf9": LawV5bVisibleOnlyLocalFCNWideRF9(width=256),
        "B3_window_mlp8": LawV5bVisibleOnlyWindowMLP(img_size=img_size, window=8, hidden=256),
    }
