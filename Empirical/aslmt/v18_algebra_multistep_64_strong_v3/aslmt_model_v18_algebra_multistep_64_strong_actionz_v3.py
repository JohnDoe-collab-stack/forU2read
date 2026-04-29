import torch
import torch.nn as nn
import torch.nn.functional as F

from aslmt_model_v18_algebra_multistep_64_strong_common import (
    AlgebraModelCfg,
    V18AlgebraCueOnlyBaseline,
    V18AlgebraVisibleOnlyBaseline,
)


def _unique_count(x: torch.Tensor) -> int:
    if int(x.numel()) == 0:
        return 0
    return int(torch.unique(x).numel())


class V18AlgebraMultistepModelA_ActionZ_Strong(nn.Module):
    """
    Strong query policy model (horizon-consistent):

    - When there are 2 query steps remaining, the query logits depend on a 2-step closure lookahead
      computed from (tables, σ, transcript).
    - When there is 1 query step remaining, the query logits depend on a 1-step expected ambiguity
      (no extra lookahead).

    This makes the selection depend on closure (multi-step), not on a local "uniq>1" heuristic.
    """

    def __init__(self, cfg: AlgebraModelCfg):
        super().__init__()
        self.cfg = cfg

        V = int(cfg.n_views)
        y_classes = int(cfg.y_classes)
        hid = int(cfg.hid)

        # Per-view MLP: (expected_final_ambiguity, expected_final_size) -> logit
        self.view_mlp = nn.Sequential(nn.Linear(2, hid), nn.GELU(), nn.Linear(hid, 1))

        # y head: reads σ-distribution under final candidate set + action-code
        self.y_head = nn.Sequential(nn.Linear(y_classes + V, hid), nn.GELU(), nn.Linear(hid, y_classes))

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
            if a < 0 or a >= int(V):
                raise ValueError(f"action out of range: {a} for n_views={V}")
            m = m & tables[a].eq(int(r))
        return m

    def _sigma_amb(self, *, sigma: torch.Tensor, mask: torch.Tensor) -> int:
        vals = sigma[mask]
        return _unique_count(vals)

    def _best_final_amb_after_one_more(
        self,
        *,
        tables: torch.Tensor,  # (V,N)
        sigma: torch.Tensor,  # (N,)
        cand: torch.Tensor,  # (N,) bool
        used: set[int],
        forbid_view0: bool,
    ) -> tuple[float, float]:
        """
        Given a current candidate mask (after observing the response of the previous action),
        compute the best expected final ambiguity achievable with exactly 1 remaining query.

        Returns:
          (best_expected_ambiguity, best_expected_final_size)
        """
        V, _ = tables.shape
        cand_idx = cand.nonzero(as_tuple=False).flatten()
        if int(cand_idx.numel()) == 0:
            return (0.0, 0.0)

        best = None
        for a in range(int(V)):
            if forbid_view0 and a == 0:
                continue
            if int(a) in used:
                continue

            labels = tables[int(a), cand_idx].to(torch.long)
            # enumerate possible responses r under the candidate set
            uniq_r = torch.unique(labels)
            total = float(cand_idx.numel())
            exp_amb = 0.0
            exp_sz = 0.0
            for r in uniq_r.tolist():
                r = int(r)
                m = cand & tables[int(a)].eq(r)
                sz = int(m.to(torch.long).sum().item())
                if sz <= 0:
                    continue
                p = float(sz) / total
                exp_amb += p * float(self._sigma_amb(sigma=sigma, mask=m))
                exp_sz += p * float(sz)

            score = (exp_amb, exp_sz, a)
            if best is None or score < best:
                best = score

        if best is None:
            # no action available
            return (float(self._sigma_amb(sigma=sigma, mask=cand)), float(int(cand.to(torch.long).sum().item())))

        return (float(best[0]), float(best[1]))

    def _score_views_one_step(
        self,
        *,
        tables: torch.Tensor,  # (V,N)
        sigma: torch.Tensor,  # (N,)
        base_obs: int,
        actions_prefix: list[int],
        responses_prefix: list[int],
        forbid_view0: bool,
    ) -> tuple[torch.Tensor, torch.Tensor]:
        """
        Score all views by expected σ-ambiguity after taking that view now, with no further queries.

        Returns:
          exp_amb: (V,) float tensor
          exp_sz : (V,) float tensor
        """
        V, _ = tables.shape
        cand0 = self._candidate_mask(
            tables=tables,
            base_obs=int(base_obs),
            actions=list(actions_prefix),
            responses=list(responses_prefix),
        )
        cand0_idx = cand0.nonzero(as_tuple=False).flatten()
        if int(cand0_idx.numel()) == 0:
            return (torch.zeros((V,), dtype=torch.float32), torch.zeros((V,), dtype=torch.float32))

        used = {int(a) for a in actions_prefix}
        total0 = float(cand0_idx.numel())

        exp_amb = torch.zeros((V,), dtype=torch.float32)
        exp_sz = torch.zeros((V,), dtype=torch.float32)

        for a in range(int(V)):
            if forbid_view0 and a == 0:
                exp_amb[a] = 1e9
                exp_sz[a] = 1e9
                continue
            if int(a) in used:
                exp_amb[a] = 1e9
                exp_sz[a] = 1e9
                continue

            labels = tables[int(a), cand0_idx].to(torch.long)
            uniq_r = torch.unique(labels)

            ea = 0.0
            es = 0.0
            for r in uniq_r.tolist():
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

        return (exp_amb, exp_sz)

    def _score_views_two_step(
        self,
        *,
        tables: torch.Tensor,  # (V,N)
        sigma: torch.Tensor,  # (N,)
        base_obs: int,
        actions_prefix: list[int],
        responses_prefix: list[int],
        forbid_view0: bool,
    ) -> tuple[torch.Tensor, torch.Tensor]:
        """
        Score all views by expected final ambiguity under a 2-step lookahead, starting from
        the current transcript prefix.

        Returns:
          exp_final_amb: (V,) float tensor
          exp_final_sz : (V,) float tensor
        """
        V, _ = tables.shape
        cand0 = self._candidate_mask(
            tables=tables,
            base_obs=int(base_obs),
            actions=list(actions_prefix),
            responses=list(responses_prefix),
        )
        cand0_idx = cand0.nonzero(as_tuple=False).flatten()
        if int(cand0_idx.numel()) == 0:
            return (torch.zeros((V,), dtype=torch.float32), torch.zeros((V,), dtype=torch.float32))

        used = {int(a) for a in actions_prefix}
        total0 = float(cand0_idx.numel())

        exp_amb = torch.zeros((V,), dtype=torch.float32)
        exp_sz = torch.zeros((V,), dtype=torch.float32)

        for a in range(int(V)):
            if forbid_view0 and a == 0:
                exp_amb[a] = 1e9
                exp_sz[a] = 1e9
                continue
            if int(a) in used:
                exp_amb[a] = 1e9
                exp_sz[a] = 1e9
                continue

            labels = tables[int(a), cand0_idx].to(torch.long)
            uniq_r = torch.unique(labels)

            ea = 0.0
            es = 0.0
            for r in uniq_r.tolist():
                r = int(r)
                cand1 = cand0 & tables[int(a)].eq(r)
                sz1 = int(cand1.to(torch.long).sum().item())
                if sz1 <= 0:
                    continue
                p = float(sz1) / total0

                # One-step remaining: choose best next action after seeing r.
                ba, bs = self._best_final_amb_after_one_more(
                    tables=tables,
                    sigma=sigma,
                    cand=cand1,
                    used=used | {int(a)},
                    forbid_view0=bool(forbid_view0),
                )
                ea += p * float(ba)
                es += p * float(bs)

            exp_amb[a] = float(ea)
            exp_sz[a] = float(es)

        return (exp_amb, exp_sz)

    def logits_query(
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
        if t < 0 or t >= int(self.cfg.steps):
            raise ValueError(f"t out of range: {t}")

        out = torch.zeros((B, V), device=tables.device, dtype=torch.float32)
        for b in range(int(B)):
            actions_prefix = [int(a.item()) for a in actions[b, :t]]
            responses_prefix = [int(r.item()) for r in responses[b, :t]]
            remaining = int(self.cfg.steps) - int(t)
            if remaining >= 2:
                amb, sz = self._score_views_two_step(
                    tables=tables[b].detach().cpu(),
                    sigma=sigma[b].detach().cpu(),
                    base_obs=int(base_obs[b].item()),
                    actions_prefix=actions_prefix,
                    responses_prefix=responses_prefix,
                    forbid_view0=True,
                )
            else:
                amb, sz = self._score_views_one_step(
                    tables=tables[b].detach().cpu(),
                    sigma=sigma[b].detach().cpu(),
                    base_obs=int(base_obs[b].item()),
                    actions_prefix=actions_prefix,
                    responses_prefix=responses_prefix,
                    forbid_view0=True,
                )
            feat = torch.stack([amb, sz], dim=-1).to(device=tables.device, dtype=torch.float32)  # (V,2)
            logits = self.view_mlp(feat).squeeze(-1)  # (V,)
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
        actions: torch.Tensor,  # (B,T)
        responses: torch.Tensor,  # (B,T)
        t: int,
        z_override: torch.Tensor | None = None,
    ) -> torch.Tensor:
        """
        After a transcript, compute the exact σ-distribution under the induced candidate set,
        then classify using a small head. This keeps the same "candidate → σ-distribution" contract as v18.
        """
        B, V, N = tables.shape
        t = int(t)

        # exact candidate set -> uniform state_dist
        m = (tables[:, 0, :] == base_obs.to(torch.long)[:, None])
        for i in range(int(t)):
            a = actions[:, i].to(torch.long).clamp(0, V - 1)
            r = responses[:, i].to(torch.long)
            lbl = tables[torch.arange(B, device=tables.device), a, :]  # (B,N)
            m = m & (lbl == r[:, None])
        w = m.to(dtype=torch.float32)
        z = w.sum(dim=-1, keepdim=True).clamp_min(1.0)
        state_dist = w / z

        y_classes = int(self.cfg.y_classes)
        oh = F.one_hot(sigma.to(torch.long), num_classes=y_classes).to(dtype=state_dist.dtype)  # (B,N,y)
        p_sig = (state_dist[:, :, None] * oh).sum(dim=1)  # (B,y)

        z_logits = self.logits_query(tables=tables, sigma=sigma, base_obs=base_obs, actions=actions, responses=responses, t=min(t, int(self.cfg.steps) - 1))
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
            z_logits = self.logits_query(tables=tables, sigma=sigma, base_obs=base_obs, actions=actions, responses=responses, t=int(t)).detach()
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
