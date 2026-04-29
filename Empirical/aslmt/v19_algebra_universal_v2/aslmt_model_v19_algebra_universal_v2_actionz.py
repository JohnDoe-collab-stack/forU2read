import torch
import torch.nn as nn
import torch.nn.functional as F

from aslmt_oracle_v19_algebra_universal_v2_common import HorizonOracleCfg, oracle_action_values


class V19AlgebraVisibleOnlyBaseline(nn.Module):
    def __init__(self, *, obs_vocab: int, y_classes: int, hid: int = 64):
        super().__init__()
        self.emb = nn.Embedding(int(obs_vocab), int(hid))
        self.head = nn.Linear(int(hid), int(y_classes))

    def forward(self, base_obs: torch.Tensor) -> torch.Tensor:
        x = self.emb(base_obs.to(torch.long))
        return self.head(x)


class V19AlgebraCueOnlyBaseline(nn.Module):
    """
    Cue-only: read (tables, sigma) but no transcript. In a non-trivial closure task it should
    remain near chance because x is hidden and base_obs is not supplied.
    """

    def __init__(self, *, n_views: int, n_states: int, obs_vocab: int, y_classes: int, hid: int = 64):
        super().__init__()
        self.n_views = int(n_views)
        self.n_states = int(n_states)
        self.obs_vocab = int(obs_vocab)
        self.y_classes = int(y_classes)
        self.hid = int(hid)

        self.tbl_emb = nn.Embedding(int(obs_vocab), int(hid))
        self.sig_emb = nn.Embedding(int(y_classes), int(hid))
        self.mlp = nn.Sequential(nn.Linear(int(hid) * 2, int(hid)), nn.GELU(), nn.Linear(int(hid), int(y_classes)))

    def forward(self, tables: torch.Tensor, sigma: torch.Tensor) -> torch.Tensor:
        t = self.tbl_emb(tables.to(torch.long)).mean(dim=(1, 2))
        s = self.sig_emb(sigma.to(torch.long)).mean(dim=1)
        return self.mlp(torch.cat([t, s], dim=-1))


class V19AlgebraUniversalModelA_ActionZ(nn.Module):
    """
    v19 universal solver (v2):

    - policy logits are computed from a horizon-consistent oracle feature triple:
        (expected_steps_to_closure, expected_final_ambiguity, expected_final_size)
    - discrete mediator z is used as an action code (action-as-z)
    - STOP is part of the action space (id=V) but is only attractive when closure already holds.

    y prediction remains a constructive reference: it is computed exactly from the candidate mask.
    """

    def __init__(self, *, n_views: int, y_classes: int, obs_vocab: int, hid: int = 128):
        super().__init__()
        self.n_views = int(n_views)
        self.y_classes = int(y_classes)
        self.obs_vocab = int(obs_vocab)
        self.hid = int(hid)

        # Per-action MLP: (exp_steps, exp_amb, exp_sz) -> logit
        self.query_mlp = nn.Sequential(nn.Linear(3, int(hid)), nn.GELU(), nn.Linear(int(hid), 1))

    def _z_from_logits(self, z_logits: torch.Tensor) -> torch.Tensor:
        z_soft = F.softmax(z_logits, dim=-1)
        idx = torch.argmax(z_soft, dim=-1)
        z_hard = F.one_hot(idx, num_classes=z_soft.shape[-1]).to(dtype=z_soft.dtype)
        return z_hard - z_soft.detach() + z_soft

    def logits_query(
        self,
        *,
        tables: torch.Tensor,  # (B,V,N)
        sigma: torch.Tensor,  # (B,N)
        base_obs: torch.Tensor,  # (B,)
        actions: torch.Tensor,  # (B,T)
        responses: torch.Tensor,  # (B,T)
        t: int,
        max_steps: int,
    ) -> torch.Tensor:
        B, V, N = tables.shape
        out = torch.zeros((B, V + 1), device=tables.device, dtype=torch.float32)  # +STOP
        oracle_cfg = HorizonOracleCfg(forbid_view0=True, allow_stop_only_if_closed=True)
        for b in range(int(B)):
            actions_prefix = [int(a.item()) for a in actions[b, : int(t)]]
            responses_prefix = [int(r.item()) for r in responses[b, : int(t)]]
            rem = int(max_steps) - int(t)
            steps, amb, sz = oracle_action_values(
                tables=tables[b],
                sigma=sigma[b],
                base_obs=int(base_obs[b].item()),
                actions_prefix=actions_prefix,
                responses_prefix=responses_prefix,
                remaining_steps=int(rem),
                cfg=oracle_cfg,
                include_stop=True,
            )
            feat = torch.stack([steps, amb, sz], dim=-1).to(device=tables.device, dtype=torch.float32)  # (V+1,3)
            feat = feat.clamp(min=-1e3, max=1e3)
            logits = self.query_mlp(feat).squeeze(-1)
            out[b] = logits
        return out

    def predict_y(
        self,
        *,
        tables: torch.Tensor,  # (B,V,N)
        sigma: torch.Tensor,  # (B,N)
        base_obs: torch.Tensor,  # (B,)
        actions: torch.Tensor,  # (B,T)
        responses: torch.Tensor,  # (B,T)
        t: int,
    ) -> torch.Tensor:
        B, V, N = tables.shape
        t = int(t)

        m = (tables[:, 0, :] == base_obs.to(torch.long)[:, None])
        for i in range(int(t)):
            a = actions[:, i].to(torch.long)
            is_stop = a.eq(int(V))
            a = a.clamp(0, int(V) - 1)
            r = responses[:, i].to(torch.long)
            lbl = tables[torch.arange(B, device=tables.device), a, :]
            m_step = (lbl == r[:, None])
            m = m & torch.where(is_stop[:, None], torch.ones_like(m_step, dtype=torch.bool), m_step)

        w = m.to(dtype=torch.float32)
        z = w.sum(dim=-1, keepdim=True).clamp_min(1.0)
        state_dist = w / z

        oh = F.one_hot(sigma.to(torch.long), num_classes=int(self.y_classes)).to(dtype=state_dist.dtype)
        p_sig = (state_dist[:, :, None] * oh).sum(dim=1)
        return torch.log(p_sig.clamp_min(1e-9))

    def rollout(
        self,
        *,
        tables: torch.Tensor,  # (B,V,N)
        sigma: torch.Tensor,  # (B,N)
        x: torch.Tensor,  # (B,)
        base_obs: torch.Tensor,  # (B,)
        max_steps: int,
        forbid_view0: bool = True,
        z_swap_perm: torch.Tensor | None = None,
        z_ablate: bool = False,
    ) -> dict[str, torch.Tensor]:
        B, V, N = tables.shape
        max_steps = int(max_steps)

        actions = torch.full((B, max_steps), fill_value=int(V), device=tables.device, dtype=torch.long)
        responses = torch.zeros((B, max_steps), device=tables.device, dtype=torch.long)
        stopped = torch.zeros((B,), device=tables.device, dtype=torch.bool)

        for t in range(int(max_steps)):
            z_logits = self.logits_query(
                tables=tables,
                sigma=sigma,
                base_obs=base_obs,
                actions=actions,
                responses=responses,
                t=int(t),
                max_steps=int(max_steps),
            ).detach()
            z = self._z_from_logits(z_logits)
            if z_swap_perm is not None:
                z = z[z_swap_perm]
            if z_ablate:
                z = torch.zeros_like(z)

            logits = z.clone()
            if bool(forbid_view0) and logits.shape[-1] >= 1:
                logits[:, 0] = -1e9
            if int(t) > 0:
                used = actions[:, : int(t)].to(torch.long)
                used_views = used.clamp(0, int(V) - 1)
                mask = torch.zeros_like(logits, dtype=torch.bool)
                mask.scatter_(1, used_views, True)
                logits = logits.masked_fill(mask, -1e9)

            a = torch.argmax(logits, dim=-1).to(torch.long)
            a = torch.where(stopped, torch.tensor(int(V), device=tables.device, dtype=torch.long), a)
            actions[:, t] = a

            is_stop = a.eq(int(V))
            stopped = stopped | is_stop

            a_clamped = a.clamp(0, int(V) - 1)
            r = tables[torch.arange(B, device=tables.device), a_clamped, x.to(torch.long)]
            r = torch.where(is_stop, torch.zeros_like(r), r)
            responses[:, t] = r.to(torch.long)

        y_logits = self.predict_y(tables=tables, sigma=sigma, base_obs=base_obs, actions=actions, responses=responses, t=int(max_steps))
        return {"actions": actions, "responses": responses, "y_logits": y_logits}
