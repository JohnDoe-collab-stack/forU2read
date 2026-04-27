import torch
import torch.nn as nn
import torch.nn.functional as F


class V18AlgebraTotalModelA(nn.Module):
    """
    Minimal active solver:

    - mediator z derived from visible cue (h),
    - query head reads z (zread spirit),
    - decoder reads (h, z, responses) to predict y.
    """

    def __init__(self, *, n_classes: int, z_classes: int, m_actions: int, k_dim: int, hid: int = 64):
        super().__init__()
        self.n_classes = int(n_classes)
        self.z_classes = int(z_classes)
        self.m_actions = int(m_actions)
        self.k_dim = int(k_dim)

        self.emb_h = nn.Embedding(self.n_classes, int(hid))
        self.z_head = nn.Linear(int(hid), self.z_classes)

        # Query from discrete z.
        # We output k_dim action logits: one action choice per k component.
        self.query_from_z = nn.Linear(self.z_classes, self.m_actions * self.k_dim)

        # Decoder: predict y from (h embedding, response bits).
        self.dec = nn.Sequential(
            nn.Linear(int(hid) + int(self.k_dim), int(hid)),
            nn.GELU(),
            nn.Linear(int(hid), 2),
        )

    def z_logits(self, h: torch.Tensor) -> torch.Tensor:
        eh = self.emb_h(h.to(torch.long))
        return self.z_head(eh)

    def logits_query(self, h: torch.Tensor) -> torch.Tensor:
        z_logits = self.z_logits(h).detach()
        idx = torch.argmax(z_logits, dim=-1).to(torch.long)
        z_oh = F.one_hot(idx, num_classes=self.z_classes).to(dtype=z_logits.dtype)
        logits = self.query_from_z(z_oh)  # (B, m_actions*k_dim)
        return logits.view(logits.shape[0], self.k_dim, self.m_actions)  # (B,k_dim,m_actions)

    def chosen_action(self, h: torch.Tensor) -> torch.Tensor:
        logits = self.logits_query(h)  # (B,k_dim,m_actions)
        return torch.argmax(logits, dim=-1).to(dtype=torch.long)  # (B,k_dim)

    def forward_with_responses(self, h: torch.Tensor, responses: torch.Tensor) -> torch.Tensor:
        eh = self.emb_h(h.to(torch.long))
        x = torch.cat([eh, responses.to(dtype=eh.dtype)], dim=1)
        return self.dec(x)


class V18VisibleOnlyBaseline(nn.Module):
    def __init__(self, *, n_classes: int, hid: int = 64):
        super().__init__()
        self.emb_h = nn.Embedding(int(n_classes), int(hid))
        self.head = nn.Linear(int(hid), 2)

    def forward(self, h: torch.Tensor) -> torch.Tensor:
        return self.head(self.emb_h(h.to(torch.long)))
