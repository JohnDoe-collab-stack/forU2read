import argparse
import json
import math
import random
from dataclasses import dataclass
from pathlib import Path

import torch
import torch.nn.functional as F
from torch.utils.data import DataLoader

from aslmt_env_v19_algebra_universal_v4_9 import V19AlgebraUniversalDataset
from aslmt_model_v19_algebra_universal_v4_9_actionz import (
    V19AlgebraCueOnlyBaseline,
    V19AlgebraUniversalModelA_ActionZ,
    V19AlgebraVisibleOnlyBaseline,
)
from aslmt_oracle_v19_algebra_universal_v4_9_common import (
    HorizonOracleCfg,
    candidate_mask,
    oracle_allowed_actions,
    sigma_ambiguity,
)


def _seed_everything(seed: int) -> None:
    seed = int(seed)
    random.seed(seed)
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)


def _acc_from_logits(logits: torch.Tensor, y: torch.Tensor) -> float:
    pred = torch.argmax(logits, dim=-1)
    return float((pred == y.to(pred.device)).float().mean().item())


def _multi_positive_ce(*, logits: torch.Tensor, allowed: torch.Tensor) -> torch.Tensor:
    logp = F.log_softmax(logits, dim=-1)
    masked = logp.masked_fill(~allowed, -1e9)
    return -torch.logsumexp(masked, dim=-1).mean()


@dataclass(frozen=True)
class EvalCfg:
    n_eval: int = 512
    batch_size: int = 64


def _rollout_closure_diagnostics(
    *,
    tables: torch.Tensor,  # (B,V,N)
    sigma: torch.Tensor,  # (B,N)
    base_obs: torch.Tensor,  # (B,)
    actions: torch.Tensor,  # (B,T)
    responses: torch.Tensor,  # (B,T)
) -> dict[str, float]:
    """
    Protocol diagnostics for a rollout transcript.

    These are computed via the same candidate/refinement semantics as the oracle, so they
    directly reflect "closure = ambiguity==1" at STOP time / final time.
    """
    B, V, _ = tables.shape
    stop = int(V)

    tables_cpu = tables.detach().cpu()
    sigma_cpu = sigma.detach().cpu()
    base_obs_cpu = base_obs.detach().cpu()
    actions_cpu = actions.detach().cpu()
    responses_cpu = responses.detach().cpu()

    n_closed = 0
    amb_sum = 0.0
    n_stop = 0
    n_stop_when_closed = 0
    stop_t_sum = 0.0

    for b in range(int(B)):
        acts = [int(a) for a in actions_cpu[b].tolist()]
        resps = [int(r) for r in responses_cpu[b].tolist()]

        cand_final = candidate_mask(
            tables=tables_cpu[b],
            base_obs=int(base_obs_cpu[b].item()),
            actions=acts,
            responses=resps,
        )
        amb_final = float(sigma_ambiguity(sigma=sigma_cpu[b], cand_mask=cand_final))
        amb_sum += float(amb_final)
        if int(amb_final) == 1:
            n_closed += 1

        stop_t: int | None = None
        for t, a in enumerate(acts):
            if int(a) == int(stop):
                stop_t = int(t)
                break
        if stop_t is None:
            stop_t = int(len(acts))
        stop_t_sum += float(stop_t)

        if int(stop_t) < int(len(acts)):
            n_stop += 1
            acts_pref = acts[: int(stop_t)]
            resps_pref = resps[: int(stop_t)]
            cand_pref = candidate_mask(
                tables=tables_cpu[b],
                base_obs=int(base_obs_cpu[b].item()),
                actions=acts_pref,
                responses=resps_pref,
            )
            amb_pref = int(sigma_ambiguity(sigma=sigma_cpu[b], cand_mask=cand_pref))
            if int(amb_pref) == 1:
                n_stop_when_closed += 1

    stop_when_closed = (float(n_stop_when_closed) / float(n_stop)) if int(n_stop) > 0 else 0.0
    return {
        "closed_rate_roll": float(n_closed) / float(B),
        "final_ambiguity_mean": float(amb_sum) / float(B),
        "stop_rate": float(n_stop) / float(B),
        "stop_when_closed_rate": float(stop_when_closed),
        "mean_stop_t": float(stop_t_sum) / float(B),
    }


def _rollout_candidate_consistency(
    *,
    tables: torch.Tensor,  # (B,V,N)
    sigma: torch.Tensor,  # (B,N)
    base_obs: torch.Tensor,  # (B,)
    actions: torch.Tensor,  # (B,T)
    responses: torch.Tensor,  # (B,T)
    belief: torch.Tensor,  # (B,N)
    y_logits: torch.Tensor,  # (B,Y)
    y: torch.Tensor,  # (B,)
) -> dict[str, float]:
    """
    Measure the gap between:
      - objective closure (candidate ambiguity==1),
      - internalized closure (belief mass on candidate set).
    """
    B, V, _ = tables.shape
    tables_cpu = tables.detach().cpu()
    sigma_cpu = sigma.detach().cpu()
    base_obs_cpu = base_obs.detach().cpu()
    actions_cpu = actions.detach().cpu()
    responses_cpu = responses.detach().cpu()
    belief_cpu = belief.detach().cpu()

    pred = torch.argmax(y_logits.detach(), dim=-1).detach().cpu()
    y_cpu = y.detach().cpu().to(torch.long)

    mass_sum = 0.0
    mass_closed_sum = 0.0
    n_closed = 0
    n_closed_correct = 0

    for b in range(int(B)):
        acts = [int(a) for a in actions_cpu[b].tolist()]
        resps = [int(r) for r in responses_cpu[b].tolist()]
        cand = candidate_mask(
            tables=tables_cpu[b],
            base_obs=int(base_obs_cpu[b].item()),
            actions=acts,
            responses=resps,
        )
        amb = int(sigma_ambiguity(sigma=sigma_cpu[b], cand_mask=cand))
        cand_f = cand.to(torch.float32)
        mass = float((belief_cpu[b].to(torch.float32) * cand_f).sum().item())
        mass_sum += mass
        if amb == 1:
            n_closed += 1
            mass_closed_sum += mass
            if int(pred[b].item()) == int(y_cpu[b].item()):
                n_closed_correct += 1

    mass_mean = float(mass_sum) / float(B)
    mass_closed_mean = float(mass_closed_sum) / float(n_closed) if int(n_closed) > 0 else 0.0
    acc_given_closed = float(n_closed_correct) / float(n_closed) if int(n_closed) > 0 else 0.0
    return {
        "belief_mass_on_candidate": float(mass_mean),
        "belief_mass_on_candidate_given_closed": float(mass_closed_mean),
        "A_acc_given_closed": float(acc_given_closed),
    }


def _eval_split(
    *,
    modelA: V19AlgebraUniversalModelA_ActionZ,
    modelB_vis: V19AlgebraVisibleOnlyBaseline,
    modelB_cue: V19AlgebraCueOnlyBaseline,
    device: torch.device,
    n_states: int,
    n_views: int,
    y_classes: int,
    obs_vocab: int,
    max_steps: int,
    ood: bool,
    seed: int,
    cfg: EvalCfg,
) -> dict:
    ds = V19AlgebraUniversalDataset(
        size=int(cfg.n_eval),
        n_states=int(n_states),
        n_views=int(n_views),
        y_classes=int(y_classes),
        obs_vocab=int(obs_vocab),
        max_steps=int(max_steps),
        ood=bool(ood),
        seed=int(seed) + (999 if bool(ood) else 0),
    )
    dl = DataLoader(ds, batch_size=int(cfg.batch_size), shuffle=False, num_workers=0)

    A_acc = []
    Bvis_acc = []
    Bcue_acc = []
    Abl_acc = []
    Swap_acc = []
    swap_action_follow = []
    diag_keys = [
        "closed_rate_roll",
        "final_ambiguity_mean",
        "stop_rate",
        "stop_when_closed_rate",
        "mean_stop_t",
        "belief_mass_on_candidate",
        "belief_mass_on_candidate_given_closed",
        "A_acc_given_closed",
    ]
    diag_lists: dict[str, list[float]] = {k: [] for k in diag_keys}

    with torch.no_grad():
        for batch in dl:
            tables = batch["tables"].to(device)
            sigma = batch["sigma"].to(device)
            x = batch["x"].to(device)
            y = batch["y"].to(device)
            base_obs = batch["base_obs"].to(device)

            outA = modelA.rollout(tables=tables, sigma=sigma, x=x, base_obs=base_obs, max_steps=int(max_steps))
            A_acc.append(_acc_from_logits(outA["y_logits"], y))

            # Objective + internalization diagnostics saved to JSON for provenance.
            diag = _rollout_closure_diagnostics(
                tables=tables,
                sigma=sigma,
                base_obs=base_obs,
                actions=outA["actions"],
                responses=outA["responses"],
            )
            b_eval = modelA.belief(
                tables=tables,
                sigma=sigma,
                base_obs=base_obs,
                actions=outA["actions"],
                responses=outA["responses"],
                t=int(max_steps),
            )
            cons = _rollout_candidate_consistency(
                tables=tables,
                sigma=sigma,
                base_obs=base_obs,
                actions=outA["actions"],
                responses=outA["responses"],
                belief=b_eval,
                y_logits=outA["y_logits"],
                y=y,
            )
            for k in diag_keys:
                if k in diag:
                    diag_lists[k].append(float(diag[k]))
                if k in cons:
                    diag_lists[k].append(float(cons[k]))

            outBv = modelB_vis(base_obs)
            Bvis_acc.append(_acc_from_logits(outBv, y))

            outBc = modelB_cue(tables, sigma)
            Bcue_acc.append(_acc_from_logits(outBc, y))

            outAbl = modelA.rollout(
                tables=tables, sigma=sigma, x=x, base_obs=base_obs, max_steps=int(max_steps), z_ablate=True
            )
            Abl_acc.append(_acc_from_logits(outAbl["y_logits"], y))

            perm = torch.arange(tables.shape[0], device=device, dtype=torch.long).flip(0)
            outSwap = modelA.rollout(
                tables=tables, sigma=sigma, x=x, base_obs=base_obs, max_steps=int(max_steps), z_swap_perm=perm
            )
            Swap_acc.append(_acc_from_logits(outSwap["y_logits"], y))

            a0 = outA["actions"][:, 0]
            a0_sw = outSwap["actions"][:, 0]
            swap_action_follow.append(float((a0_sw == a0[perm]).float().mean().item()))

    def _mean(xs: list[float]) -> float:
        return float(sum(xs) / max(1, len(xs)))

    out = {
        "A_acc": _mean(A_acc),
        "B_vis_acc": _mean(Bvis_acc),
        "B_cue_acc": _mean(Bcue_acc),
        "A_abl_acc": _mean(Abl_acc),
        "A_swap_acc": _mean(Swap_acc),
        "swap_action_follow_rate": _mean(swap_action_follow),
    }
    for k in diag_keys:
        if diag_lists[k]:
            out[k] = _mean(diag_lists[k])
    return out


def main() -> None:
    p = argparse.ArgumentParser(
        description="ASLMT v19 algebra universal v4.9 trainer (compatibility-aware belief + closed-only readout loss)."
    )
    p.add_argument("--profile", type=str, default="solid", choices=["smoke", "solid"])
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--steps", type=int, default=6000)
    p.add_argument("--batch-size", type=int, default=64)
    p.add_argument("--lr", type=float, default=3e-4)
    p.add_argument("--n-states", type=int, required=True)
    p.add_argument("--n-views", type=int, default=8)
    p.add_argument("--y-classes", type=int, default=2)
    p.add_argument("--obs-vocab", type=int, default=16)
    p.add_argument("--max-steps", type=int, default=3)
    p.add_argument("--tf-decay-frac", type=float, default=0.65)
    p.add_argument("--w-y-closed", type=float, default=2.0)
    p.add_argument(
        "--w-cand",
        type=float,
        default=0.0,
        help="Optional belief→candidate consistency loss weight (set >0 to enable).",
    )
    p.add_argument("--master-jsonl", type=str, required=True)
    args = p.parse_args()

    profile = str(args.profile)
    steps = int(args.steps)
    batch_size = int(args.batch_size)
    if profile == "smoke":
        if steps == 6000:
            steps = 300
        if batch_size == 64:
            batch_size = 32

    device = torch.device(str(args.device))
    _seed_everything(int(args.seed))

    n_states = int(args.n_states)
    n_views = int(args.n_views)
    y_classes = int(args.y_classes)
    obs_vocab = int(args.obs_vocab)
    max_steps = int(args.max_steps)
    tf_decay_frac = float(args.tf_decay_frac)
    w_y_closed = float(args.w_y_closed)
    w_cand = float(args.w_cand)

    modelA = V19AlgebraUniversalModelA_ActionZ(
        n_views=int(n_views),
        n_states=int(n_states),
        y_classes=int(y_classes),
        obs_vocab=int(obs_vocab),
        hid=128,
        n_heads=4,
        n_layers=2,
    ).to(device)
    modelB_vis = V19AlgebraVisibleOnlyBaseline(obs_vocab=int(obs_vocab), y_classes=int(y_classes)).to(device)
    modelB_cue = V19AlgebraCueOnlyBaseline(
        n_views=int(n_views), n_states=int(n_states), obs_vocab=int(obs_vocab), y_classes=int(y_classes)
    ).to(device)

    opt = torch.optim.AdamW(list(modelA.parameters()) + list(modelB_vis.parameters()) + list(modelB_cue.parameters()), lr=float(args.lr))

    ds = V19AlgebraUniversalDataset(
        size=2048 if profile == "smoke" else 20000,
        n_states=int(n_states),
        n_views=int(n_views),
        y_classes=int(y_classes),
        obs_vocab=int(obs_vocab),
        max_steps=int(max_steps),
        ood=False,
        seed=int(args.seed) + 17,
    )
    dl = DataLoader(ds, batch_size=int(batch_size), shuffle=True, num_workers=0)
    it = iter(dl)

    oracle_cfg = HorizonOracleCfg(forbid_view0=True, allow_stop_only_if_closed=True)

    for step in range(1, int(steps) + 1):
        try:
            batch = next(it)
        except StopIteration:
            it = iter(dl)
            batch = next(it)

        tables = batch["tables"].to(device)
        sigma = batch["sigma"].to(device)
        x = batch["x"].to(device)
        y = batch["y"].to(device)
        base_obs = batch["base_obs"].to(device)

        B, V, N = tables.shape
        A = int(V) + 1  # +STOP

        actions_prefix = torch.full((B, max_steps), fill_value=int(V), device=device, dtype=torch.long)
        responses_prefix = torch.zeros((B, max_steps), device=device, dtype=torch.long)
        stopped = torch.zeros((B,), device=device, dtype=torch.bool)

        # Teacher forcing schedule (trajectory-level):
        # with `max_steps=3`, per-step TF would make fully teacher-forced trajectories occur with prob p^3.
        p_traj = max(0.0, 1.0 - float(step) / max(1.0, float(steps) * float(tf_decay_frac)))
        use_teacher_traj = (torch.rand((B,), device=device) < float(p_traj)).to(torch.bool)

        q_losses = []
        q_acc_terms = []
        for t in range(int(max_steps)):
            logits = modelA.logits_query(
                tables=tables,
                sigma=sigma,
                base_obs=base_obs,
                actions=actions_prefix,
                responses=responses_prefix,
                t=int(t),
                max_steps=int(max_steps),
            )

            allowed = torch.zeros((B, A), device=device, dtype=torch.bool)
            for b in range(int(B)):
                acts = [int(a.item()) for a in actions_prefix[b, :t]]
                resps = [int(r.item()) for r in responses_prefix[b, :t]]
                allow = oracle_allowed_actions(
                    tables=tables[b].detach().cpu(),
                    sigma=sigma[b].detach().cpu(),
                    base_obs=int(base_obs[b].item()),
                    actions_prefix=acts,
                    responses_prefix=resps,
                    remaining_steps=int(max_steps - t),
                    cfg=oracle_cfg,
                )
                for a in allow:
                    allowed[b, int(a)] = True

            q_losses.append(_multi_positive_ce(logits=logits, allowed=allowed))

            # Apply protocol legality mask before argmax: forbid view0, forbid repeats, force STOP after STOP.
            masked_logits = logits.clone()
            masked_logits[:, 0] = -1e9
            if int(t) > 0:
                used = actions_prefix[:, : int(t)].to(torch.long)
                valid = used.ge(0) & used.lt(int(V))
                used_views = used.clamp(0, int(V) - 1)
                m_used = torch.zeros_like(masked_logits, dtype=torch.bool)
                m_used.scatter_(1, used_views, valid)
                masked_logits = masked_logits.masked_fill(m_used, -1e9)
            masked_logits = torch.where(stopped[:, None], torch.full_like(masked_logits, -1e9), masked_logits)
            masked_logits[stopped, int(V)] = 0.0

            pred = torch.argmax(masked_logits, dim=-1)
            ok = allowed[torch.arange(B, device=device), pred]
            q_acc_terms.append(float(ok.float().mean().item()))

            teacher = torch.zeros((B,), device=device, dtype=torch.long)
            for b in range(int(B)):
                idxs = torch.nonzero(allowed[b], as_tuple=False).flatten()
                if int(idxs.numel()) == 0:
                    teacher[b] = int(V)
                else:
                    j = int(torch.randint(0, int(idxs.numel()), (1,), device=device).item())
                    teacher[b] = int(idxs[j].item())

            a_next = torch.where(use_teacher_traj, teacher, pred).to(torch.long)
            a_next = torch.where(stopped, torch.tensor(int(V), device=device, dtype=torch.long), a_next)
            actions_prefix[:, t] = a_next

            is_stop = a_next.eq(int(V))
            stopped = stopped | is_stop
            a_clamped = a_next.clamp(0, int(V) - 1)
            rr = tables[torch.arange(B, device=device), a_clamped, x.to(torch.long)]
            rr = torch.where(is_stop, torch.zeros_like(rr), rr)
            responses_prefix[:, t] = rr.to(torch.long)

        q_loss = torch.stack(q_losses, dim=0).mean()

        y_logits = modelA.predict_y(
            tables=tables,
            sigma=sigma,
            base_obs=base_obs,
            actions=actions_prefix,
            responses=responses_prefix,
            t=int(max_steps),
        )
        y_loss = F.nll_loss(y_logits, y.to(torch.long))

        # Rollout-aligned y loss: train on the same autonomous transcript distribution that evaluation uses.
        out_roll = modelA.rollout(tables=tables, sigma=sigma, x=x, base_obs=base_obs, max_steps=int(max_steps))
        y_loss_roll = F.nll_loss(out_roll["y_logits"], y.to(torch.long))

        # Closed-only readout loss (objective closure):
        # When the rollout transcript is objectively closed (ambiguity==1 under the oracle semantics),
        # force the model's final y readout to be correct.
        tables_cpu = tables.detach().cpu()
        sigma_cpu = sigma.detach().cpu()
        base_obs_cpu = base_obs.detach().cpu()
        actions_cpu = out_roll["actions"].detach().cpu()
        responses_cpu = out_roll["responses"].detach().cpu()
        closed_cpu = torch.zeros((B,), dtype=torch.bool)
        for bb in range(int(B)):
            acts = [int(a) for a in actions_cpu[bb].tolist()]
            resps = [int(r) for r in responses_cpu[bb].tolist()]
            cand = candidate_mask(
                tables=tables_cpu[bb],
                base_obs=int(base_obs_cpu[bb].item()),
                actions=acts,
                responses=resps,
            )
            amb = int(sigma_ambiguity(sigma=sigma_cpu[bb], cand_mask=cand))
            closed_cpu[bb] = bool(int(amb) == 1)
        closed_mask = closed_cpu.to(device=device)
        if bool(closed_mask.any().item()):
            y_loss_closed = F.nll_loss(out_roll["y_logits"][closed_mask], y.to(torch.long)[closed_mask])
        else:
            y_loss_closed = torch.zeros((), device=device, dtype=torch.float32)

        # Optional candidate-consistency loss: concentrate internal belief on the *exact* candidate set
        # induced by the rollout transcript (objective closure vs internalized closure).
        candidate_nll = torch.zeros((), device=device, dtype=torch.float32)
        if float(w_cand) > 0.0:
            b_roll = modelA.belief(
                tables=tables,
                sigma=sigma,
                base_obs=base_obs,
                actions=out_roll["actions"],
                responses=out_roll["responses"],
                t=int(max_steps),
            )
            cand_mask_cpu = torch.zeros((B, N), dtype=torch.bool)
            for bb in range(int(B)):
                acts = [int(a) for a in actions_cpu[bb].tolist()]
                resps = [int(r) for r in responses_cpu[bb].tolist()]
                cand = candidate_mask(
                    tables=tables_cpu[bb],
                    base_obs=int(base_obs_cpu[bb].item()),
                    actions=acts,
                    responses=resps,
                )
                cand_mask_cpu[bb] = cand
            cand_mask = cand_mask_cpu.to(device=device)
            cand_mass = (b_roll * cand_mask.to(b_roll.dtype)).sum(dim=-1).to(torch.float32)
            candidate_nll = -torch.log(cand_mass.clamp_min(1e-9)).mean()

        bvis = modelB_vis(base_obs)
        bcue = modelB_cue(tables, sigma)
        bvis_loss = F.cross_entropy(bvis, y.to(torch.long))
        bcue_loss = F.cross_entropy(bcue, y.to(torch.long))

        loss = (
            y_loss
            + 0.5 * y_loss_roll
            + float(w_y_closed) * y_loss_closed
            + q_loss
            + float(w_cand) * candidate_nll
            + 0.1 * (bvis_loss + bcue_loss)
        )

        opt.zero_grad(set_to_none=True)
        loss.backward()
        opt.step()

        if step % (250 if profile == "solid" else 50) == 0 or step == steps:
            with torch.no_grad():
                y_acc = _acc_from_logits(y_logits, y)
                q_acc = float(sum(q_acc_terms) / max(1, len(q_acc_terms)))
                outA = out_roll
                A_acc_batch = _acc_from_logits(outA["y_logits"].detach(), y)
                diag = _rollout_closure_diagnostics(
                    tables=tables,
                    sigma=sigma,
                    base_obs=base_obs,
                    actions=outA["actions"],
                    responses=outA["responses"],
                )
                cons = _rollout_candidate_consistency(
                    tables=tables,
                    sigma=sigma,
                    base_obs=base_obs,
                    actions=outA["actions"],
                    responses=outA["responses"],
                    belief=modelA.belief(
                        tables=tables,
                        sigma=sigma,
                        base_obs=base_obs,
                        actions=outA["actions"],
                        responses=outA["responses"],
                        t=int(max_steps),
                    ),
                    y_logits=outA["y_logits"],
                    y=y,
                )
            print(
                f"step={step}/{steps} loss={float(loss.item()):.6f} "
                f"(y={float(y_loss.item()):.6f}, y_roll={float(y_loss_roll.item()):.6f}, "
                f"y_closed={float(y_loss_closed.item()):.6f}, q={float(q_loss.item()):.6f}, "
                f"cand_nll={float(candidate_nll.item()):.6f}, "
                f"Bvis={float(bvis_loss.item()):.6f}, Bcue={float(bcue_loss.item()):.6f}) "
                f"y_acc={y_acc:.4f} q_acc={q_acc:.4f} A_acc_batch={A_acc_batch:.4f} p_traj={float(p_traj):.3f} "
                f"closed_roll={diag['closed_rate_roll']:.3f} amb_final={diag['final_ambiguity_mean']:.3f} "
                f"stop_rate={diag['stop_rate']:.3f} stop_closed={diag['stop_when_closed_rate']:.3f} "
                f"mean_stop_t={diag['mean_stop_t']:.3f} "
                f"mass_cand={cons['belief_mass_on_candidate']:.3f} "
                f"mass_cand_closed={cons['belief_mass_on_candidate_given_closed']:.3f} "
                f"A_closed={cons['A_acc_given_closed']:.3f}"
            )

    eval_cfg = EvalCfg(n_eval=256 if profile == "smoke" else 1024, batch_size=64)
    iid = _eval_split(
        modelA=modelA,
        modelB_vis=modelB_vis,
        modelB_cue=modelB_cue,
        device=device,
        n_states=n_states,
        n_views=n_views,
        y_classes=y_classes,
        obs_vocab=obs_vocab,
        max_steps=max_steps,
        ood=False,
        seed=int(args.seed) + 101,
        cfg=eval_cfg,
    )
    ood = _eval_split(
        modelA=modelA,
        modelB_vis=modelB_vis,
        modelB_cue=modelB_cue,
        device=device,
        n_states=n_states,
        n_views=n_views,
        y_classes=y_classes,
        obs_vocab=obs_vocab,
        max_steps=max_steps,
        ood=True,
        seed=int(args.seed) + 131,
        cfg=eval_cfg,
    )

    rec = {
        "kind": "aslmt_v19_algebra_universal_actionz_v4_9",
        "seed": int(args.seed),
        "n_states": int(n_states),
        "n_views": int(n_views),
        "y_classes": int(y_classes),
        "obs_vocab": int(obs_vocab),
        "max_steps": int(max_steps),
        "profile": str(profile),
        "tf_decay_frac": float(tf_decay_frac),
        "w_y_closed": float(w_y_closed),
        "w_cand": float(w_cand),
        "metrics": {"iid": iid, "ood": ood},
    }

    master = Path(args.master_jsonl).expanduser().resolve()
    master.parent.mkdir(parents=True, exist_ok=True)
    with open(master, "a", encoding="utf-8") as f:
        f.write(json.dumps(rec) + "\n")


if __name__ == "__main__":
    main()
