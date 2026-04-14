import copy
import torch
import torch.nn as nn
import torch.nn.functional as F


class Attention(nn.Module):
    def __init__(self, dim: int, num_heads: int = 4):
        super().__init__()
        self.num_heads = int(num_heads)
        self.scale = (dim // num_heads) ** -0.5
        self.qkv = nn.Linear(dim, dim * 3, bias=False)
        self.proj = nn.Linear(dim, dim)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        B, N, C = x.shape
        qkv = self.qkv(x).reshape(B, N, 3, self.num_heads, C // self.num_heads).permute(2, 0, 3, 1, 4)
        q, k, v = qkv[0], qkv[1], qkv[2]
        attn = (q @ k.transpose(-2, -1)) * self.scale
        attn = attn.softmax(dim=-1)
        x = (attn @ v).transpose(1, 2).reshape(B, N, C)
        return self.proj(x)


class TransformerBlock(nn.Module):
    def __init__(self, dim: int, num_heads: int = 4, mlp_ratio: float = 4.0):
        super().__init__()
        self.norm1 = nn.LayerNorm(dim)
        self.attn = Attention(dim, num_heads=num_heads)
        self.norm2 = nn.LayerNorm(dim)
        hidden_dim = int(dim * mlp_ratio)
        self.mlp = nn.Sequential(
            nn.Linear(dim, hidden_dim),
            nn.GELU(),
            nn.Linear(hidden_dim, dim),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        x = x + self.attn(self.norm1(x))
        x = x + self.mlp(self.norm2(x))
        return x


class SimpleViT(nn.Module):
    def __init__(self, img_size: int = 32, patch_size: int = 4, in_chans: int = 1, embed_dim: int = 96, depth: int = 3, num_heads: int = 4):
        super().__init__()
        self.patch_size = int(patch_size)
        self.num_patches = (img_size // patch_size) ** 2
        self.patch_embed = nn.Conv2d(in_chans, embed_dim, kernel_size=patch_size, stride=patch_size)
        self.pos_embed = nn.Parameter(torch.zeros(1, self.num_patches, embed_dim))
        self.blocks = nn.ModuleList([TransformerBlock(embed_dim, num_heads=num_heads) for _ in range(depth)])
        self.norm = nn.LayerNorm(embed_dim)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        x = self.patch_embed(x)
        x = x.flatten(2).transpose(1, 2)
        x = x + self.pos_embed
        for blk in self.blocks:
            x = blk(x)
        return self.norm(x)


class V7PerfectAmodalCausalJEPA(nn.Module):
    """
    Same architecture shape as v6, but v7 trains/evaluates against a hidden-only target.
    """

    def __init__(self, embed_dim: int = 96, d_latent: int = 128, ema_decay: float = 0.99):
        super().__init__()
        self.embed_dim = int(embed_dim)
        self.d_latent = int(d_latent)
        self.ema_decay = float(ema_decay)

        self.encoder = SimpleViT(embed_dim=embed_dim, depth=3, num_heads=4)
        self.state_gru = nn.GRUCell(embed_dim, d_latent)

        self.target_encoder = copy.deepcopy(self.encoder)
        for p in self.target_encoder.parameters():
            p.requires_grad = False

        self.predictor = nn.Sequential(
            nn.Linear(d_latent + embed_dim, embed_dim * 2),
            nn.LayerNorm(embed_dim * 2),
            nn.GELU(),
            nn.Linear(embed_dim * 2, embed_dim),
        )

        # Predict a 32x32 mask from the internal state only.
        self.mask_head = nn.Sequential(
            nn.Linear(d_latent, 256),
            nn.LayerNorm(256),
            nn.GELU(),
            nn.Linear(256, 1024),
        )

    @torch.no_grad()
    def ema_update(self) -> None:
        m = self.ema_decay
        for p_t, p in zip(self.target_encoder.parameters(), self.encoder.parameters()):
            p_t.data.mul_(m).add_(p.data, alpha=(1.0 - m))

    def init_latent(self, batch_size: int, device: torch.device) -> torch.Tensor:
        return torch.zeros((batch_size, self.d_latent), device=device)

    def encode_frame(self, x: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor]:
        toks = self.encoder(x)
        pooled = toks.mean(dim=1)
        return toks, pooled

    def step_state(self, z: torch.Tensor, x: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor]:
        toks, pooled = self.encode_frame(x)
        z_next = self.state_gru(pooled, z)
        return toks, z_next

    def rollout_state(self, cue_image: torch.Tensor, image: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor]:
        z0 = self.init_latent(cue_image.shape[0], cue_image.device)
        _, z1 = self.step_state(z0, cue_image)
        _, z2 = self.step_state(z1, image)
        return z1, z2

    def forward(self, cue_image: torch.Tensor, image: torch.Tensor) -> torch.Tensor:
        _, z2 = self.rollout_state(cue_image, image)
        out = self.mask_head(z2)
        return out.view(-1, 1, 32, 32)

    def swap_forward(self, cue_image: torch.Tensor, image: torch.Tensor, perm: torch.Tensor) -> torch.Tensor:
        _, z2 = self.rollout_state(cue_image, image)
        z_swap = z2[perm]
        out = self.mask_head(z_swap)
        return out.view(-1, 1, 32, 32)

    def ablated_forward(self, cue_image: torch.Tensor, image: torch.Tensor) -> torch.Tensor:
        B = cue_image.shape[0]
        z = torch.zeros((B, self.d_latent), device=cue_image.device)
        out = self.mask_head(z)
        return out.view(-1, 1, 32, 32)

    def jepa_forward(self, cue_image: torch.Tensor, image: torch.Tensor, x_full: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        _, z2 = self.rollout_state(cue_image, image)
        with torch.no_grad():
            t_full = self.target_encoder(x_full)
            t_full = F.normalize(t_full, dim=-1)
        B, N, _ = t_full.shape
        pos_emb = self.target_encoder.pos_embed.expand(B, N, -1)
        z_expand = z2.unsqueeze(1).expand(B, N, -1)
        pred = self.predictor(torch.cat([z_expand, pos_emb], dim=-1))
        pred = F.normalize(pred, dim=-1)
        return pred, t_full, z2


class V7PerfectVisibleOnlyBaseline(nn.Module):
    """
    Capacity-matched global baseline: final-image-only, no cue, no recurrent state.
    """

    def __init__(self, embed_dim: int = 96, d_latent: int = 128):
        super().__init__()
        self.encoder = SimpleViT(embed_dim=embed_dim, depth=3, num_heads=4)
        self.proj = nn.Sequential(
            nn.Linear(embed_dim, d_latent),
            nn.LayerNorm(d_latent),
            nn.GELU(),
            nn.Linear(d_latent, d_latent),
        )
        self.mask_head = nn.Sequential(
            nn.Linear(d_latent, 256),
            nn.LayerNorm(256),
            nn.GELU(),
            nn.Linear(256, 1024),
        )

    def forward(self, image: torch.Tensor) -> torch.Tensor:
        h = self.encoder(image)
        pooled = h.mean(dim=1)
        z = self.proj(pooled)
        out = self.mask_head(z)
        return out.view(-1, 1, 32, 32)

