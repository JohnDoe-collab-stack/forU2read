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
    Cue-only: read (tables, sigma) but no transcript. Should remain near chance because x is hidden
    and base_obs is not supplied.
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
    v19 universal solver (v4):

    Goal: remove algorithmic/oracle-derived policy features.

    - The policy is a learned encoder over *raw* inputs:
        tables, sigma, base_obs, transcript(action,response)
      No oracle calls, no hard-coded ambiguity/count computations.

    - The model forms a soft belief over states via attention between a transcript encoding and per-state embeddings.
      Then it chooses the next view via an action head that conditions on the belief and raw table rows.

    - y prediction is learned *through* the belief (not via exact candidate masking).

    action-as-z remains: z is a straight-through one-hot; action = argmax(z).
    """

    def __init__(
        self,
        *,
        n_views: int,
        n_states: int,
        y_classes: int,
        obs_vocab: int,
        hid: int = 128,
        n_heads: int = 4,
        n_layers: int = 2,
    ):
        super().__init__()
        self.n_views = int(n_views)
        self.n_states = int(n_states)
        self.y_classes = int(y_classes)
        self.obs_vocab = int(obs_vocab)
        self.hid = int(hid)

        # Tokens
        self.view_emb = nn.Embedding(int(n_views) + 1, int(hid))  # +STOP id=V
        self.lbl_emb = nn.Embedding(int(obs_vocab), int(hid))
        self.sig_emb = nn.Embedding(int(y_classes), int(hid))

        # Transcript encoder (sequence length = 1 + max_steps, but we feed full tensors and mask by t)
        enc_layer = nn.TransformerEncoderLayer(
            d_model=int(hid),
            nhead=int(n_heads),
            dim_feedforward=int(hid) * 4,
            activation="gelu",
            batch_first=True,
            norm_first=True,
        )
        self.tr_enc = nn.TransformerEncoder(enc_layer, num_layers=int(n_layers))

        # State encoder: combine all view labels + sigma into a per-state embedding
        self.state_mlp = nn.Sequential(nn.Linear(int(hid) * 2, int(hid)), nn.GELU(), nn.Linear(int(hid), int(hid)))

        # Belief attention
        self.q_proj = nn.Linear(int(hid), int(hid), bias=False)
        self.k_proj = nn.Linear(int(hid), int(hid), bias=False)

        # Action head: for each action, consume (context, expected-label-embedding-under-belief, action-id-embedding)
        self.act_mlp = nn.Sequential(nn.Linear(int(hid) * 3, int(hid)), nn.GELU(), nn.Linear(int(hid), 1))

    def _z_from_logits(self, z_logits: torch.Tensor) -> torch.Tensor:
        z_soft = F.softmax(z_logits, dim=-1)
        idx = torch.argmax(z_soft, dim=-1)
        z_hard = F.one_hot(idx, num_classes=z_soft.shape[-1]).to(dtype=z_soft.dtype)
        return z_hard - z_soft.detach() + z_soft

    def _encode_transcript(
        self,
        *,
        base_obs: torch.Tensor,  # (B,)
        actions: torch.Tensor,  # (B,Tmax)
        responses: torch.Tensor,  # (B,Tmax)
        t: int,
    ) -> torch.Tensor:
        """
        Encode transcript prefix into a context vector (B,hid).
        We represent base as token 0; then each step i as token i+1.
        Only first (1+t) tokens are "real"; others are padded with zeros and masked.
        """
        B = int(base_obs.shape[0])
        Tmax = int(actions.shape[1])
        t = int(t)

        # tokens: (B, 1+Tmax, hid)
        tok = torch.zeros((B, 1 + Tmax, int(self.hid)), device=base_obs.device, dtype=torch.float32)

        # base token: view 0 + label base_obs
        tok[:, 0] = self.view_emb(torch.zeros_like(base_obs, dtype=torch.long)) + self.lbl_emb(base_obs.to(torch.long))

        # step tokens: view id + response label
        if Tmax > 0:
            a = actions.to(torch.long).clamp(0, int(self.n_views))  # allow STOP id
            r = responses.to(torch.long).clamp(0, int(self.obs_vocab) - 1)
            tok[:, 1:] = self.view_emb(a) + self.lbl_emb(r)

        # padding mask: True means "pad" for TransformerEncoder
        pad = torch.ones((B, 1 + Tmax), device=base_obs.device, dtype=torch.bool)
        pad[:, : 1 + t] = False

        h = self.tr_enc(tok, src_key_padding_mask=pad)  # (B,1+Tmax,hid)
        # Use the last real token position as context.
        idx = torch.full((B,), int(t), device=base_obs.device, dtype=torch.long)
        ctx = h[torch.arange(B, device=base_obs.device), idx]
        return ctx

    def _state_embeddings(self, *, tables: torch.Tensor, sigma: torch.Tensor) -> torch.Tensor:
        """
        Per-state embedding (B,N,hid) from raw tables+sigma.
        """
        B, V, N = tables.shape
        # embed labels for all views then pool across views
        lbl = self.lbl_emb(tables.to(torch.long).clamp(0, int(self.obs_vocab) - 1))  # (B,V,N,hid)
        view_ids = torch.arange(int(V), device=tables.device, dtype=torch.long)[None, :, None].expand(B, V, N)
        vemb = self.view_emb(view_ids)  # (B,V,N,hid)
        x = (lbl + vemb).mean(dim=1)  # (B,N,hid)
        s = self.sig_emb(sigma.to(torch.long).clamp(0, int(self.y_classes) - 1))  # (B,N,hid)
        return self.state_mlp(torch.cat([x, s], dim=-1))  # (B,N,hid)

    def _belief(self, *, ctx: torch.Tensor, state: torch.Tensor) -> torch.Tensor:
        """
        Soft belief over N states: (B,N).
        """
        q = self.q_proj(ctx)[:, None, :]  # (B,1,hid)
        k = self.k_proj(state)  # (B,N,hid)
        scores = (q * k).sum(dim=-1) / (float(self.hid) ** 0.5)  # (B,N)
        return F.softmax(scores, dim=-1)

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
        Tmax = int(actions.shape[1])
        t = int(t)
        _ = int(max_steps)

        ctx = self._encode_transcript(base_obs=base_obs, actions=actions, responses=responses, t=int(t))
        state = self._state_embeddings(tables=tables, sigma=sigma)
        b = self._belief(ctx=ctx, state=state)  # (B,N)

        # For each action a, compute expected label embedding under the belief:
        # mu_a = E_{s~b}[ emb(view=a,label=tables[a,s]) ]  (no hard-coded ambiguity).
        out = torch.zeros((B, int(V) + 1), device=tables.device, dtype=torch.float32)
        for a in range(int(V)):
            labels = tables[:, int(a), :].to(torch.long).clamp(0, int(self.obs_vocab) - 1)  # (B,N)
            e = self.lbl_emb(labels) + self.view_emb(
                torch.full((B,), int(a), device=tables.device, dtype=torch.long)
            )[:, None, :]
            mu = (b[:, :, None] * e).sum(dim=1)  # (B,hid)
            aemb = self.view_emb(torch.full((B,), int(a), device=tables.device, dtype=torch.long))
            feat = torch.cat([ctx, mu, aemb], dim=-1)
            out[:, int(a)] = self.act_mlp(feat).squeeze(-1)

        # STOP action: let the network decide based on ctx + belief summary
        mu_stop = (b[:, :, None] * state).sum(dim=1)
        stop_emb = self.view_emb(torch.full((B,), int(V), device=tables.device, dtype=torch.long))
        out[:, int(V)] = self.act_mlp(torch.cat([ctx, mu_stop, stop_emb], dim=-1)).squeeze(-1)

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
        ctx = self._encode_transcript(base_obs=base_obs, actions=actions, responses=responses, t=int(t))
        state = self._state_embeddings(tables=tables, sigma=sigma)
        b = self._belief(ctx=ctx, state=state)  # (B,N)

        # y logits derived from belief expectation over sigma.
        oh = F.one_hot(sigma.to(torch.long), num_classes=int(self.y_classes)).to(dtype=b.dtype)  # (B,N,Y)
        p = (b[:, :, None] * oh).sum(dim=1).clamp_min(1e-9)  # (B,Y)
        return torch.log(p)

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
            )
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
                valid = used.ge(0) & used.lt(int(V))
                used_views = used.clamp(0, int(V) - 1)
                mask = torch.zeros_like(logits, dtype=torch.bool)
                mask.scatter_(1, used_views, valid)
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

        y_logits = self.predict_y(
            tables=tables, sigma=sigma, base_obs=base_obs, actions=actions, responses=responses, t=int(max_steps)
        )
        return {"actions": actions, "responses": responses, "y_logits": y_logits}

