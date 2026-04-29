import math
from dataclasses import dataclass

import torch
import torch.nn as nn


@dataclass(frozen=True)
class AlgebraModelCfg:
    n_views: int
    obs_vocab: int
    y_classes: int
    z_classes: int
    emb: int = 64
    hid: int = 128
    steps: int = 2


class V18AlgebraVisibleOnlyBaseline(nn.Module):
    """
    Baseline (visible-only): sees only the base observation id (no cue, no transcript).
    """

    def __init__(self, *, obs_vocab: int, y_classes: int, emb: int = 64, hid: int = 128):
        super().__init__()
        self.e = nn.Embedding(int(obs_vocab), int(emb))
        self.mlp = nn.Sequential(nn.Linear(int(emb), int(hid)), nn.GELU(), nn.Linear(int(hid), int(y_classes)))

    def forward(self, base_obs: torch.Tensor) -> torch.Tensor:
        x = self.e(base_obs.to(torch.long))
        return self.mlp(x)


class V18AlgebraCueOnlyBaseline(nn.Module):
    """
    Baseline (cue-only): sees cue tables + σ definition, but not base_obs nor responses.
    It can only predict the marginal mode of σ.
    """

    def __init__(self, *, obs_vocab: int, y_classes: int, emb: int = 64, hid: int = 128):
        super().__init__()
        self.sig_e = nn.Embedding(int(y_classes), int(emb))
        self.mlp = nn.Sequential(nn.Linear(int(emb), int(hid)), nn.GELU(), nn.Linear(int(hid), int(y_classes)))

    def forward(self, tables: torch.Tensor, sigma: torch.Tensor) -> torch.Tensor:
        s = self.sig_e(sigma.to(torch.long)).mean(dim=1)
        return self.mlp(s)

