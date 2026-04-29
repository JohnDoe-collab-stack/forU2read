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
    Cue-only: read (tables, sigma) but no transcript. This is a strong baseline; in non-trivial tasks
    it should remain near chance because x is hidden and the base observation is not supplied.
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
        # tables: (B,V,N), sigma: (B,N)
        B, V, N = tables.shape
        if int(V) != int(self.n_views) or int(N) != int(self.n_states):
            # allow varying N at runtime; just embed whatever.
            pass
        t = self.tbl_emb(tables.to(torch.long)).mean(dim=(1, 2))  # (B,hid)
        s = self.sig_emb(sigma.to(torch.long)).mean(dim=1)  # (B,hid)
        x = torch.cat([t, s], dim=-1)
        return self.mlp(x)


class V19AlgebraUniversalModelA_ActionZ(nn.Module):
    """
    v19 universal solver:

    - discrete mediator z is used as an action code (action-as-z)
    - query head produces logits over actions in {0..V-1} plus STOP=V
    - y head predicts σ(x) from the final transcript (candidate-set distribution)

    This model is still a constructive reference: y prediction is computed exactly from candidate mask.
    """

    def __init__(self, *, n_views: int, y_classes: int, obs_vocab: int, hid: int = 128):
        super().__init__()
        self.n_views = int(n_views)
        self.y_classes = int(y_classes)
        self.obs_vocab = int(obs_vocab)
        self.hid = int(hid)

        # action logits will be mapped to a one-hot z, then used as action.
        self.query_mlp = nn.Sequential(nn.Linear(2, int(hid)), nn.GELU(), nn.Linear(int(hid), 1))

    def _candidate_mask(
        self,
        *,
        tables: torch.Tensor,  # (V,N)
        base_obs: int,
        actions: list[int],
        responses: list[int],
    ) -> torch.Tensor:
        V, _ = tables.shape
        m = tables[0].eq(int(base_obs))
        for a, r in zip(actions, responses):
            a = int(a)
            # STOP is encoded as a==V; it carries no refinement constraint.
            if a == int(V):
                continue
            if a < 0 or a > int(V) - 1:
                raise ValueError(f"action out of range: {a}")
            m = m & tables[a].eq(int(r))
        return m

    def _sigma_amb(self, *, sigma: torch.Tensor, mask: torch.Tensor) -> int:
        vals = sigma[mask]
        if int(vals.numel()) == 0:
            return 0
        return int(torch.unique(vals).numel())

    def _score_one_step(
        self,
        *,
        tables: torch.Tensor,  # (V,N)
        sigma: torch.Tensor,  # (N,)
        base_obs: int,
        actions_prefix: list[int],
        responses_prefix: list[int],
        forbid_view0: bool,
        include_stop: bool,
    ) -> tuple[torch.Tensor, torch.Tensor]:
        """
        Score actions by expected ambiguity after taking that action now.
        Returns exp_amb, exp_sz (both shaped (V+stop,)).
        """
        V, _ = tables.shape
        A = int(V) + (1 if bool(include_stop) else 0)
        cand0 = self._candidate_mask(
            tables=tables,
            base_obs=int(base_obs),
            actions=list(actions_prefix),
            responses=list(responses_prefix),
        )
        idx0 = cand0.nonzero(as_tuple=False).flatten()
        exp_amb = torch.zeros((A,), dtype=torch.float32)
        exp_sz = torch.zeros((A,), dtype=torch.float32)
        if int(idx0.numel()) == 0:
            return exp_amb, exp_sz

        used = {int(a) for a in actions_prefix}
        total0 = float(idx0.numel())

        # view actions
        for a in range(int(V)):
            if forbid_view0 and a == 0:
                exp_amb[a] = 1e9
                exp_sz[a] = 1e9
                continue
            if int(a) in used:
                exp_amb[a] = 1e9
                exp_sz[a] = 1e9
                continue
            labels = tables[int(a), idx0].to(torch.long)
            uniq = torch.unique(labels)
            ea = 0.0
            es = 0.0
            for r in uniq.tolist():
                r = int(r)
                cand1 = cand0 & tables[int(a)].eq(r)
                sz1 = int(cand1.to(torch.long).sum().item())
                if sz1 <= 0:
                    continue
                p = float(sz1) / total0
                ea += p * float(self._sigma_amb(sigma=sigma, mask=cand1))
                es += p * float(sz1)
            exp_amb[a] = float(ea)
            exp_sz[a] = float(es)

        # STOP action: ambiguity if we stop now
        if bool(include_stop):
            stop = int(V)
            exp_amb[stop] = float(self._sigma_amb(sigma=sigma, mask=cand0))
            exp_sz[stop] = float(idx0.numel())

        return exp_amb, exp_sz

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
        for b in range(int(B)):
            actions_prefix = [int(a.item()) for a in actions[b, :t]]
            responses_prefix = [int(r.item()) for r in responses[b, :t]]
            amb, sz = self._score_one_step(
                tables=tables[b].detach().cpu(),
                sigma=sigma[b].detach().cpu(),
                base_obs=int(base_obs[b].item()),
                actions_prefix=actions_prefix,
                responses_prefix=responses_prefix,
                forbid_view0=True,
                include_stop=True,
            )
            feat = torch.stack([amb, sz], dim=-1).to(device=tables.device, dtype=torch.float32)  # (V+1,2)
            logits = self.query_mlp(feat).squeeze(-1)  # (V+1,)
            out[b] = logits
        return out

    def _z_from_logits(self, z_logits: torch.Tensor) -> torch.Tensor:
        z_soft = F.softmax(z_logits, dim=-1)
        idx = torch.argmax(z_soft, dim=-1)
        z_hard = F.one_hot(idx, num_classes=z_soft.shape[-1]).to(dtype=z_soft.dtype)
        return z_hard - z_soft.detach() + z_soft

    def predict_y(
        self,
        *,
        tables: torch.Tensor,  # (B,V,N)
        sigma: torch.Tensor,  # (B,N)
        base_obs: torch.Tensor,  # (B,)
        actions: torch.Tensor,  # (B,T) (stop included maybe)
        responses: torch.Tensor,  # (B,T)
        t: int,
    ) -> torch.Tensor:
        """
        Compute exact σ-distribution under candidate mask, then return logits.
        """
        B, V, N = tables.shape
        t = int(t)

        # exact candidate set mask
        m = (tables[:, 0, :] == base_obs.to(torch.long)[:, None])
        for i in range(int(t)):
            a = actions[:, i].to(torch.long)
            # ignore STOP in candidate refinement (it has no response)
            is_stop = a.eq(int(V))
            a = a.clamp(0, int(V) - 1)
            r = responses[:, i].to(torch.long)
            lbl = tables[torch.arange(B, device=tables.device), a, :]  # (B,N)
            m_step = (lbl == r[:, None])
            m = m & torch.where(is_stop[:, None], torch.ones_like(m_step, dtype=torch.bool), m_step)

        w = m.to(dtype=torch.float32)
        z = w.sum(dim=-1, keepdim=True).clamp_min(1.0)
        state_dist = w / z

        oh = F.one_hot(sigma.to(torch.long), num_classes=int(self.y_classes)).to(dtype=state_dist.dtype)  # (B,N,y)
        p_sig = (state_dist[:, :, None] * oh).sum(dim=1)  # (B,y)
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

        actions = torch.full((B, max_steps), fill_value=int(V), device=tables.device, dtype=torch.long)  # default STOP
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

            # action-as-z: logits = z
            logits = z.clone()
            if bool(forbid_view0) and logits.shape[-1] >= 1:
                logits[:, 0] = -1e9
            # Disallow repeated view queries (STOP can repeat).
            if int(t) > 0:
                used = actions[:, : int(t)].to(torch.long)
                used_views = used.clamp(0, int(V) - 1)
                # mask only for non-stop actions
                mask = torch.zeros_like(logits, dtype=torch.bool)
                mask.scatter_(1, used_views, True)
                logits = logits.masked_fill(mask, -1e9)

            a = torch.argmax(logits, dim=-1).to(torch.long)
            # once stopped, keep STOP
            a = torch.where(stopped, torch.tensor(int(V), device=tables.device, dtype=torch.long), a)
            actions[:, t] = a

            is_stop = a.eq(int(V))
            stopped = stopped | is_stop

            # response only for non-stop
            a_clamped = a.clamp(0, int(V) - 1)
            r = tables[torch.arange(B, device=tables.device), a_clamped, x.to(torch.long)]
            r = torch.where(is_stop, torch.zeros_like(r), r)
            responses[:, t] = r.to(torch.long)

        y_logits = self.predict_y(
            tables=tables, sigma=sigma, base_obs=base_obs, actions=actions, responses=responses, t=int(max_steps)
        )
        return {"actions": actions, "responses": responses, "y_logits": y_logits}
