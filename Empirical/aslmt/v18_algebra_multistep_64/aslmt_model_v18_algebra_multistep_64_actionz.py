import torch
import torch.nn as nn
import torch.nn.functional as F

from aslmt_model_v18_algebra_multistep_64 import (
    AlgebraModelCfg,
    V18AlgebraCueOnlyBaseline,
    V18AlgebraVisibleOnlyBaseline,
)


class V18AlgebraMultistepModelA_ActionZ(nn.Module):
    """
    Variant where the discrete mediator z is the action itself (one-hot over views).

    This keeps the contract:
      cue+transcript -> discrete z -> query action

    and removes an unnecessary extra discrete bottleneck between z and the action.
    """

    def __init__(self, cfg: AlgebraModelCfg):
        super().__init__()
        self.cfg = cfg

        V = int(cfg.n_views)
        y_classes = int(cfg.y_classes)
        hid = int(cfg.hid)

        # z_logits lives in R^V and is discretized to a one-hot action code.
        self.z_mlp = nn.Sequential(nn.Linear(y_classes + V + 4, hid), nn.GELU(), nn.Linear(hid, V))

        # y head: reads σ-weighted candidate distribution + z (action-code)
        self.y_head = nn.Sequential(nn.Linear(y_classes + V, hid), nn.GELU(), nn.Linear(hid, y_classes))

    def _state_dist(
        self,
        *,
        tables: torch.Tensor,  # (B,V,N)
        base_obs: torch.Tensor,  # (B,)
        actions: torch.Tensor,  # (B,T)
        responses: torch.Tensor,  # (B,T)
        t: int,
    ) -> torch.Tensor:
        B, V, N = tables.shape
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
        B, V, N = tables.shape
        state_dist = self._state_dist(tables=tables, base_obs=base_obs, actions=actions, responses=responses, t=int(t))
        p_sig = self._sigma_dist(sigma=sigma, state_dist=state_dist, y_classes=int(self.cfg.y_classes))  # (B,y)

        cand = (state_dist > 0.0)  # (B,N)
        uniq_scores = []
        for j in range(int(V)):
            lbl = tables[:, j, :].to(torch.long)
            c = []
            for b in range(int(B)):
                vals = lbl[b][cand[b]]
                c.append(float(torch.unique(vals).numel()))
            uniq_scores.append(torch.tensor(c, device=tables.device, dtype=torch.float32)[:, None])
        uniq = torch.cat(uniq_scores, dim=1)  # (B,V)
        # keep raw counts (1 vs 2) to maximize signal
        uniq_raw = uniq

        ent = -(p_sig.clamp_min(1e-9) * p_sig.clamp_min(1e-9).log()).sum(dim=-1, keepdim=True)  # (B,1)
        top2 = torch.topk(p_sig, k=min(2, p_sig.shape[-1]), dim=-1).values
        if int(top2.shape[-1]) == 1:
            top2 = torch.cat([top2, torch.zeros_like(top2)], dim=-1)
        mass = state_dist.max(dim=-1, keepdim=True).values

        feat = torch.cat([p_sig, uniq_raw, ent, top2[:, 0:1], top2[:, 1:2], mass], dim=-1)  # (B, y+V+4)
        return self.z_mlp(feat)

    def _z_from_logits(self, z_logits: torch.Tensor) -> torch.Tensor:
        z_soft = F.softmax(z_logits, dim=-1)
        idx = torch.argmax(z_soft, dim=-1)
        z_hard = F.one_hot(idx, num_classes=z_soft.shape[-1]).to(dtype=z_soft.dtype)
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
        z = self._z_from_logits(z_logits)
        # query logits are literally the action code
        return z

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
        B, V, N = tables.shape
        T = int(steps)
        actions = torch.zeros((B, T), device=tables.device, dtype=torch.long)
        responses = torch.zeros((B, T), device=tables.device, dtype=torch.long)

        for t in range(T):
            z_logits = self.z_logits(tables=tables, sigma=sigma, base_obs=base_obs, actions=actions, responses=responses, t=int(t)).detach()
            z = F.one_hot(torch.argmax(z_logits, dim=-1), num_classes=V).to(dtype=z_logits.dtype)
            if z_swap_perm is not None:
                z = z[z_swap_perm]
            if z_ablate:
                z = torch.zeros_like(z)

            logits = z.clone()
            if forbid_view0 and logits.shape[-1] >= 1:
                logits[:, 0] = -1e9
            if int(t) > 0:
                used = actions[:, : int(t)].to(torch.long).clamp(0, V - 1)
                mask = torch.zeros_like(logits, dtype=torch.bool)
                mask.scatter_(1, used, True)
                logits = logits.masked_fill(mask, -1e9)
            a = torch.argmax(logits, dim=-1).to(torch.long)
            actions[:, t] = a

            rr = tables[torch.arange(B, device=tables.device), a, x.to(torch.long)]
            responses[:, t] = rr.to(torch.long)

        y_logits = self.predict_y(tables=tables, sigma=sigma, base_obs=base_obs, actions=actions, responses=responses, t=T)
        return {"y_logits": y_logits, "actions": actions, "responses": responses}

