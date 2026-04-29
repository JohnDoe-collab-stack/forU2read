import torch
import torch.nn as nn
import torch.nn.functional as F


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
    v19 universal solver (v3):

    - policy logits are computed by a learned MLP from *non-oracle* features extracted
      from the current transcript:
        (current ambiguity, per-action 1-step expected ambiguity/size, time-remaining)
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

        # Per-action MLP, fed with local (1-step) features; see `logits_query`.
        self.query_mlp = nn.Sequential(nn.Linear(6, int(hid)), nn.GELU(), nn.Linear(int(hid), 1))

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
        t = int(t)
        max_steps = int(max_steps)
        rem = float(max(0, int(max_steps) - int(t)))

        # Candidate mask induced by transcript prefix (base + t queried view/responses).
        m = (tables[:, 0, :] == base_obs.to(torch.long)[:, None])
        for i in range(int(t)):
            a_i = actions[:, i].to(torch.long)
            is_stop = a_i.eq(int(V))
            a_i = a_i.clamp(0, int(V) - 1)
            r_i = responses[:, i].to(torch.long)
            lbl = tables[torch.arange(B, device=tables.device), a_i, :]
            m_step = (lbl == r_i[:, None])
            m = m & torch.where(is_stop[:, None], torch.ones_like(m_step, dtype=torch.bool), m_step)

        # Current ambiguity: number of unique sigma values on candidate set.
        # (With y_classes=2 in this protocol, this is 0/1/2.)
        s0 = (sigma.to(torch.long) == 0) & m
        s1 = (sigma.to(torch.long) == 1) & m
        amb0 = (s0.any(dim=-1).to(torch.float32) + s1.any(dim=-1).to(torch.float32))  # (B,)

        # Per-action one-step expected ambiguity/size from the current candidate set.
        # We compute counts per label in obs_vocab.
        obs_vocab = int(self.obs_vocab)
        a_space = int(V) + 1  # +STOP
        out = torch.zeros((B, a_space), device=tables.device, dtype=torch.float32)

        cand_sz0 = m.to(torch.float32).sum(dim=-1).clamp_min(1.0)  # (B,)

        for a in range(int(V)):
            labels = tables[:, int(a), :].to(torch.long)  # (B,N)
            labels = labels.clamp(0, obs_vocab - 1)
            # counts[b,l] = #{x in cand | label(x)=l}
            oh = F.one_hot(labels, num_classes=obs_vocab).to(torch.float32)  # (B,N,L)
            counts = (oh * m[:, :, None].to(torch.float32)).sum(dim=1)  # (B,L)
            p = counts / cand_sz0[:, None]

            # For each label l, ambiguity after observing l is whether sigma has both values in that slice.
            # Compute slice masks: m & (label==l)
            # Efficiently: compute counts for sigma==0 and sigma==1 per label.
            s0_counts = (oh * s0[:, :, None].to(torch.float32)).sum(dim=1)  # (B,L)
            s1_counts = (oh * s1[:, :, None].to(torch.float32)).sum(dim=1)  # (B,L)
            amb_l = ((s0_counts > 0).to(torch.float32) + (s1_counts > 0).to(torch.float32))  # (B,L)
            exp_amb = (p * amb_l).sum(dim=-1)  # (B,)
            exp_sz = (p * counts).sum(dim=-1)  # (B,) == expected candidate size after one query

            feat = torch.stack(
                [
                    amb0,  # current ambiguity
                    cand_sz0,  # current candidate size
                    exp_amb,  # expected ambiguity after querying a
                    exp_sz,  # expected candidate size after querying a
                    torch.full_like(amb0, float(a)),  # action id (lets MLP break symmetries)
                    torch.full_like(amb0, float(rem)),  # remaining steps (scalar context)
                ],
                dim=-1,
            )  # (B,6)
            out[:, int(a)] = self.query_mlp(feat).squeeze(-1)

        # STOP logit: prefer STOP only when already closed (amb0==1).
        stop_feat = torch.stack(
            [
                amb0,
                cand_sz0,
                amb0,  # exp_amb if stop = current
                cand_sz0,  # exp_sz if stop = current
                torch.full_like(amb0, float(V)),
                torch.full_like(amb0, float(rem)),
            ],
            dim=-1,
        )
        out[:, int(V)] = self.query_mlp(stop_feat).squeeze(-1)
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
