import math
from dataclasses import dataclass

import torch
import torch.nn as nn
import torch.nn.functional as F


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
    Baseline B_img analogue: sees only the base observation id (no cue, no query transcript).
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
    Baseline B_cue analogue: sees cue tables + σ definition, but not the base observation nor responses.
    It can only predict the marginal mode of σ.
    """

    def __init__(self, *, obs_vocab: int, y_classes: int, emb: int = 64, hid: int = 128):
        super().__init__()
        self.obs_e = nn.Embedding(int(obs_vocab), int(emb))
        self.sig_e = nn.Embedding(int(y_classes), int(emb))
        self.mlp = nn.Sequential(nn.Linear(int(emb), int(hid)), nn.GELU(), nn.Linear(int(hid), int(y_classes)))

    def forward(self, tables: torch.Tensor, sigma: torch.Tensor) -> torch.Tensor:
        # summarize σ as a bag of embeddings (no access to x)
        s = self.sig_e(sigma.to(torch.long)).mean(dim=1)
        return self.mlp(s)


class V18AlgebraMultistepModelA(nn.Module):
    """
    Model A (zread): a discrete mediator z controls the query policy.

    Inputs per batch item:
      - tables: (V,N) view labels for every state (cue definition of interfaces)
      - sigma : (N,) σ labels for every state (cue definition of target)
      - base_obs: scalar (initial interface observation O_base(x))
      - transcript: chosen actions + obtained responses (query loop)
    """

    def __init__(self, cfg: AlgebraModelCfg):
        super().__init__()
        self.cfg = cfg

        V = int(cfg.n_views)
        y_classes = int(cfg.y_classes)
        z_classes = int(cfg.z_classes)
        hid = int(cfg.hid)
        # mediator from a summary of the current candidate set and per-view refinement scores
        # (depends on base + responses and reads the cue tables)
        self.z_mlp = nn.Sequential(nn.Linear(y_classes + V + 4, hid), nn.GELU(), nn.Linear(hid, z_classes))
        self.query_from_z = nn.Linear(z_classes, V)

        # y head: reads σ-weighted candidate distribution + z
        self.y_head = nn.Sequential(nn.Linear(y_classes + z_classes, hid), nn.GELU(), nn.Linear(hid, y_classes))

    def _state_dist(
        self,
        *,
        tables: torch.Tensor,  # (B,V,N)
        base_obs: torch.Tensor,  # (B,)
        actions: torch.Tensor,  # (B,T)
        responses: torch.Tensor,  # (B,T)
        t: int,
    ) -> torch.Tensor:
        """
        Soft distribution over x ∈ X given transcript up to step t (exclusive).
        """
        B, V, N = tables.shape
        # Exact candidate set under the observed transcript (deterministic; no learnable shortcut).
        m = (tables[:, 0, :] == base_obs.to(torch.long)[:, None])
        for i in range(int(t)):
            a = actions[:, i].to(torch.long).clamp(0, V - 1)
            r = responses[:, i].to(torch.long)
            lbl = tables[torch.arange(B, device=tables.device), a, :]  # (B,N)
            m = m & (lbl == r[:, None])
        w = m.to(dtype=torch.float32)
        z = w.sum(dim=-1, keepdim=True).clamp_min(1.0)
        return w / z

    def _sigma_dist(self, *, sigma: torch.Tensor, state_dist: torch.Tensor, y_classes: int) -> torch.Tensor:
        """
        Distribution over σ(x) induced by state_dist.
        """
        B, N = state_dist.shape
        y = int(y_classes)
        sig = sigma.to(torch.long)
        oh = F.one_hot(sig, num_classes=y).to(dtype=state_dist.dtype)  # (B,N,y)
        p = (state_dist[:, :, None] * oh).sum(dim=1)  # (B,y)
        return p

    def z_logits(
        self,
        *,
        tables: torch.Tensor,
        sigma: torch.Tensor,
        base_obs: torch.Tensor,
        actions: torch.Tensor,
        responses: torch.Tensor,
        t: int,
    ) -> torch.Tensor:
        """
        z depends on the current residual ambiguity (via σ-distribution under candidate set).
        """
        B, V, N = tables.shape
        state_dist = self._state_dist(tables=tables, base_obs=base_obs, actions=actions, responses=responses, t=int(t))
        p_sig = self._sigma_dist(sigma=sigma, state_dist=state_dist, y_classes=int(self.cfg.y_classes))  # (B,y)

        # candidate mask for refinement stats
        cand = (state_dist > 0.0)  # (B,N)

        # per-view refinement score: unique label count within the current candidate set
        # normalized to [0,1] by dividing by obs_vocab upper bound (loose).
        uniq_scores = []
        for j in range(int(V)):
            lbl = tables[:, j, :].to(torch.long)
            # compute unique count per batch element (small N, so loop is fine)
            c = []
            for b in range(int(B)):
                vals = lbl[b][cand[b]]
                c.append(float(torch.unique(vals).numel()))
            uniq_scores.append(torch.tensor(c, device=tables.device, dtype=torch.float32)[:, None])
        uniq = torch.cat(uniq_scores, dim=1)  # (B,V)
        uniq_norm = uniq / float(max(2, int(self.cfg.obs_vocab)))

        ent = -(p_sig.clamp_min(1e-9) * p_sig.clamp_min(1e-9).log()).sum(dim=-1, keepdim=True)  # (B,1)
        top2 = torch.topk(p_sig, k=min(2, p_sig.shape[-1]), dim=-1).values
        if int(top2.shape[-1]) == 1:
            top2 = torch.cat([top2, torch.zeros_like(top2)], dim=-1)
        mass = state_dist.max(dim=-1, keepdim=True).values

        feat = torch.cat([p_sig, uniq_norm, ent, top2[:, 0:1], top2[:, 1:2], mass], dim=-1)  # (B, y+V+4)
        return self.z_mlp(feat)

    def _z_from_logits(self, z_logits: torch.Tensor) -> torch.Tensor:
        z_soft = F.softmax(z_logits, dim=-1)
        idx = torch.argmax(z_soft, dim=-1)
        z_hard = F.one_hot(idx, num_classes=int(self.cfg.z_classes)).to(dtype=z_soft.dtype)
        return z_hard - z_soft.detach() + z_soft

    def logits_query(
        self,
        *,
        tables: torch.Tensor,
        sigma: torch.Tensor,
        base_obs: torch.Tensor,
        actions: torch.Tensor,
        responses: torch.Tensor,
        t: int,
    ) -> torch.Tensor:
        z_logits = self.z_logits(tables=tables, sigma=sigma, base_obs=base_obs, actions=actions, responses=responses, t=int(t))
        z_soft = F.softmax(z_logits, dim=-1)
        return self.query_from_z(z_soft)

    def chosen_action(
        self,
        *,
        tables: torch.Tensor,
        sigma: torch.Tensor,
        base_obs: torch.Tensor,
        actions: torch.Tensor,
        responses: torch.Tensor,
        t: int,
        forbid_view0: bool = True,
    ) -> torch.Tensor:
        logits = self.logits_query(tables=tables, sigma=sigma, base_obs=base_obs, actions=actions, responses=responses, t=int(t))
        logits = logits.clone()
        if forbid_view0 and logits.shape[-1] >= 1:
            logits[:, 0] = -1e9
        # prevent repeating already-chosen views
        if int(t) > 0:
            used = actions[:, : int(t)].to(torch.long).clamp(0, logits.shape[-1] - 1)
            mask = torch.zeros_like(logits, dtype=torch.bool)
            mask.scatter_(1, used, True)
            logits = logits.masked_fill(mask, -1e9)
        return torch.argmax(logits, dim=-1).to(torch.long)

    def predict_y(
        self,
        *,
        tables: torch.Tensor,
        sigma: torch.Tensor,
        base_obs: torch.Tensor,
        actions: torch.Tensor,
        responses: torch.Tensor,
        t: int,
        z_override: torch.Tensor | None = None,
    ) -> torch.Tensor:
        state_dist = self._state_dist(tables=tables, base_obs=base_obs, actions=actions, responses=responses, t=int(t))
        p_sig = self._sigma_dist(sigma=sigma, state_dist=state_dist, y_classes=int(self.cfg.y_classes))
        z_logits = self.z_logits(tables=tables, sigma=sigma, base_obs=base_obs, actions=actions, responses=responses, t=int(t))
        z = self._z_from_logits(z_logits) if z_override is None else z_override
        feat = torch.cat([p_sig, z], dim=-1)
        return self.y_head(feat)

    def rollout(
        self,
        *,
        tables: torch.Tensor,  # (B,V,N)
        sigma: torch.Tensor,  # (B,N)
        x: torch.Tensor,  # (B,)
        base_obs: torch.Tensor,  # (B,)
        steps: int,
        forbid_view0: bool = True,
        z_swap_perm: torch.Tensor | None = None,
        z_ablate: bool = False,
    ) -> dict[str, torch.Tensor]:
        """
        Perform a discrete query loop and return logits for y at the end.

        z_swap_perm: if provided, swap the mediator used by the query policy according to perm.
        z_ablate: if true, set z used by the query policy to zero.
        """
        B, V, N = tables.shape
        T = int(steps)
        actions = torch.zeros((B, T), device=tables.device, dtype=torch.long)
        responses = torch.zeros((B, T), device=tables.device, dtype=torch.long)

        for t in range(T):
            # compute z for current step
            z_logits = self.z_logits(tables=tables, sigma=sigma, base_obs=base_obs, actions=actions, responses=responses, t=int(t)).detach()
            z = F.one_hot(torch.argmax(z_logits, dim=-1), num_classes=int(self.cfg.z_classes)).to(dtype=z_logits.dtype)
            if z_swap_perm is not None:
                z = z[z_swap_perm]
            if z_ablate:
                z = torch.zeros_like(z)

            logits = self.query_from_z(z).clone()
            if forbid_view0 and logits.shape[-1] >= 1:
                logits[:, 0] = -1e9
            if int(t) > 0:
                used = actions[:, : int(t)].to(torch.long).clamp(0, V - 1)
                mask = torch.zeros_like(logits, dtype=torch.bool)
                mask.scatter_(1, used, True)
                logits = logits.masked_fill(mask, -1e9)
            a = torch.argmax(logits, dim=-1).to(torch.long)
            actions[:, t] = a

            # env response for chosen view: O_a(x)
            rr = tables[torch.arange(B, device=tables.device), a, x.to(torch.long)]
            responses[:, t] = rr.to(torch.long)

        y_logits = self.predict_y(tables=tables, sigma=sigma, base_obs=base_obs, actions=actions, responses=responses, t=T)
        return {"y_logits": y_logits, "actions": actions, "responses": responses}
