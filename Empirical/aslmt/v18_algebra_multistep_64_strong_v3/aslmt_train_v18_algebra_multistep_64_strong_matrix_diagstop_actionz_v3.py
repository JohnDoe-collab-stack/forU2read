import argparse
import json
import random
from dataclasses import dataclass
from pathlib import Path

import torch
import torch.nn.functional as F
from torch.utils.data import DataLoader

from aslmt_env_v18_algebra_multistep_64_strong_v3 import V18AlgebraMultistepDataset64_Strong
from aslmt_model_v18_algebra_multistep_64_strong_actionz_v3 import V18AlgebraMultistepModelA_ActionZ_Strong
from aslmt_model_v18_algebra_multistep_64_strong_common import (
    AlgebraModelCfg,
    V18AlgebraCueOnlyBaseline,
    V18AlgebraVisibleOnlyBaseline,
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


@dataclass(frozen=True)
class EvalCfg:
    n_eval: int = 512
    batch_size: int = 64


def _eval_split(
    *,
    modelA: V18AlgebraMultistepModelA_ActionZ_Strong,
    modelB_vis: V18AlgebraVisibleOnlyBaseline,
    modelB_cue: V18AlgebraCueOnlyBaseline,
    device: torch.device,
    n_states: int,
    n_views: int,
    y_classes: int,
    steps: int,
    obs_vocab: int,
    ood: bool,
    seed: int,
    cfg: EvalCfg,
) -> dict:
    ds = V18AlgebraMultistepDataset64_Strong(
        size=int(cfg.n_eval),
        n_states=int(n_states),
        n_views=int(n_views),
        y_classes=int(y_classes),
        steps=int(steps),
        obs_vocab=int(obs_vocab),
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

    with torch.no_grad():
        for batch in dl:
            tables = batch["tables"].to(device)
            sigma = batch["sigma"].to(device)
            x = batch["x"].to(device)
            y = batch["y"].to(device)
            base_obs = batch["base_obs"].to(device)

            outA = modelA.rollout(tables=tables, sigma=sigma, x=x, base_obs=base_obs, steps=int(steps))
            A_acc.append(_acc_from_logits(outA["y_logits"], y))

            outBv = modelB_vis(base_obs)
            Bvis_acc.append(_acc_from_logits(outBv, y))

            outBc = modelB_cue(tables, sigma)
            Bcue_acc.append(_acc_from_logits(outBc, y))

            outAbl = modelA.rollout(tables=tables, sigma=sigma, x=x, base_obs=base_obs, steps=int(steps), z_ablate=True)
            Abl_acc.append(_acc_from_logits(outAbl["y_logits"], y))

            perm = torch.arange(tables.shape[0], device=device, dtype=torch.long).flip(0)
            outSwap = modelA.rollout(tables=tables, sigma=sigma, x=x, base_obs=base_obs, steps=int(steps), z_swap_perm=perm)
            Swap_acc.append(_acc_from_logits(outSwap["y_logits"], y))

            a0 = outA["actions"][:, 0]
            a0_sw = outSwap["actions"][:, 0]
            swap_action_follow.append(float((a0_sw == a0[perm]).float().mean().item()))

    def _mean(xs: list[float]) -> float:
        return float(sum(xs) / max(1, len(xs)))

    return {
        "A_acc": _mean(A_acc),
        "B_vis_acc": _mean(Bvis_acc),
        "B_cue_acc": _mean(Bcue_acc),
        "A_abl_acc": _mean(Abl_acc),
        "A_swap_acc": _mean(Swap_acc),
        "swap_action_follow_rate": _mean(swap_action_follow),
    }


def main() -> None:
    p = argparse.ArgumentParser(
        description="ASLMT v18 algebra multistep strong matrix trainer (action-as-z diagstop)."
    )
    p.add_argument("--profile", type=str, default="solid", choices=["smoke", "solid"])
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--steps", type=int, default=4000)
    p.add_argument("--batch-size", type=int, default=64)
    p.add_argument("--lr", type=float, default=3e-4)
    p.add_argument("--n-states", type=int, required=True)
    p.add_argument("--n-views", type=int, default=8)
    p.add_argument("--y-classes", type=int, default=2)
    p.add_argument("--q-steps", type=int, default=2)
    p.add_argument("--obs-vocab", type=int, default=16)
    p.add_argument("--tf-decay-frac", type=float, default=0.8)
    p.add_argument("--master-jsonl", type=str, required=True)
    args = p.parse_args()

    profile = str(args.profile)
    seed = int(args.seed)
    _seed_everything(seed)

    device = torch.device(str(args.device))
    steps = int(args.steps)
    batch_size = int(args.batch_size)

    n_states = int(args.n_states)
    n_views = int(args.n_views)
    y_classes = int(args.y_classes)
    q_steps = int(args.q_steps)
    obs_vocab = int(args.obs_vocab)

    if profile == "smoke":
        if steps == 4000:
            steps = 300
        if batch_size == 64:
            batch_size = 32

    tf_decay_frac = float(args.tf_decay_frac)
    tf_decay_frac = min(1.0, max(0.1, tf_decay_frac))
    tf_decay_steps = max(1, int(tf_decay_frac * steps))

    cfgA = AlgebraModelCfg(n_views=n_views, obs_vocab=obs_vocab, y_classes=y_classes, z_classes=n_views, steps=q_steps)
    modelA = V18AlgebraMultistepModelA_ActionZ_Strong(cfgA).to(device)
    modelB_vis = V18AlgebraVisibleOnlyBaseline(obs_vocab=obs_vocab, y_classes=y_classes).to(device)
    modelB_cue = V18AlgebraCueOnlyBaseline(obs_vocab=obs_vocab, y_classes=y_classes).to(device)

    opt = torch.optim.AdamW(
        list(modelA.parameters()) + list(modelB_vis.parameters()) + list(modelB_cue.parameters()), lr=float(args.lr)
    )

    ds_iid = V18AlgebraMultistepDataset64_Strong(
        size=max(1024, steps * batch_size),
        n_states=n_states,
        n_views=n_views,
        y_classes=y_classes,
        steps=q_steps,
        obs_vocab=obs_vocab,
        ood=False,
        seed=seed + 17,
    )
    ds_ood = V18AlgebraMultistepDataset64_Strong(
        size=max(1024, steps * batch_size),
        n_states=n_states,
        n_views=n_views,
        y_classes=y_classes,
        steps=q_steps,
        obs_vocab=obs_vocab,
        ood=True,
        seed=seed + 23,
    )

    dl_iid = DataLoader(ds_iid, batch_size=batch_size, shuffle=True, num_workers=0)
    dl_ood = DataLoader(ds_ood, batch_size=batch_size, shuffle=True, num_workers=0)
    it_iid = iter(dl_iid)
    it_ood = iter(dl_ood)

    for step in range(1, steps + 1):
        use_ood = bool(step % 2 == 0)
        try:
            batch = next(it_ood if use_ood else it_iid)
        except StopIteration:
            it_iid = iter(dl_iid)
            it_ood = iter(dl_ood)
            batch = next(it_ood if use_ood else it_iid)

        tables = batch["tables"].to(device)
        sigma = batch["sigma"].to(device)
        x = batch["x"].to(device)
        y = batch["y"].to(device)
        base_obs = batch["base_obs"].to(device)
        opt_actions = batch["opt_actions"].to(device)
        bit_idxs = batch["bit_idxs"].to(device)

        B = int(tables.shape[0])
        p_tf = 1.0 - min(1.0, float(step) / float(tf_decay_steps))

        actions_prefix = torch.zeros((B, q_steps), device=device, dtype=torch.long)
        responses_prefix = torch.zeros((B, q_steps), device=device, dtype=torch.long)

        q_loss_terms = []
        rollout_q_acc_terms = []

        for t in range(q_steps):
            logits_q = modelA.logits_query(
                tables=tables,
                sigma=sigma,
                base_obs=base_obs,
                actions=actions_prefix,
                responses=responses_prefix,
                t=t,
            ).clone()

            if logits_q.shape[-1] >= 1:
                logits_q[:, 0] = -1e9
            if int(t) > 0:
                used = actions_prefix[:, : int(t)].to(torch.long).clamp(0, logits_q.shape[-1] - 1)
                mask = torch.zeros_like(logits_q, dtype=torch.bool)
                mask.scatter_(1, used, True)
                logits_q = logits_q.masked_fill(mask, -1e9)

            # Strong supervision: the first query target is set-valued {bit0, bit1} (a symmetry/tie).
            bit0 = bit_idxs[:, 0].to(torch.long)
            bit1 = bit_idxs[:, 1].to(torch.long)

            logp = F.log_softmax(logits_q, dim=-1)
            pred_a = torch.argmax(logits_q, dim=-1).to(torch.long)

            allowed = torch.stack([bit0, bit1], dim=1)
            allowed_mask = torch.zeros_like(logits_q, dtype=torch.bool)
            allowed_mask.scatter_(1, allowed.clamp(0, logits_q.shape[-1] - 1), True)

            if int(t) == 0:
                # Multi-positive CE: -log(sum_{a in allowed} p(a)).
                logp_allowed = torch.logsumexp(logp.masked_fill(~allowed_mask, -1e9), dim=-1)
                q_loss_terms.append((-logp_allowed).mean())

                with torch.no_grad():
                    ok = (pred_a == bit0) | (pred_a == bit1)
                    rollout_q_acc_terms.append(float(ok.float().mean().item()))

                    # Teacher action: sample uniformly among allowed actions.
                    pick_first = (torch.rand((B,), device=device) < 0.5).to(torch.bool)
                    teacher_a = torch.where(pick_first, bit0, bit1).to(torch.long)

                    use_teacher = (torch.rand((B,), device=device) < float(p_tf)).to(torch.bool)
                    a_next = torch.where(use_teacher, teacher_a, pred_a).to(torch.long)
                    actions_prefix[:, t] = a_next

                    rr = tables[torch.arange(B, device=device), a_next, x.to(torch.long)]
                    responses_prefix[:, t] = rr.to(torch.long)
            else:
                # At t=1, if a0 is a bit-view then the unique target is the other bit-view.
                # Otherwise the best remaining label is set-valued again.
                a0 = actions_prefix[:, 0].to(torch.long)
                a0_is_bit = (a0 == bit0) | (a0 == bit1)
                tgt_unique = torch.where(a0 == bit0, bit1, bit0).to(torch.long)

                logp_allowed = torch.logsumexp(logp.masked_fill(~allowed_mask, -1e9), dim=-1)
                loss_set_per = (-logp_allowed)  # (B,)
                loss_unique_per = (-logp.gather(1, tgt_unique[:, None]).squeeze(1))  # (B,)
                q_loss_terms.append(torch.where(a0_is_bit, loss_unique_per, loss_set_per).mean())

                with torch.no_grad():
                    ok_unique = (pred_a == tgt_unique)
                    ok_set = (pred_a == bit0) | (pred_a == bit1)
                    ok = torch.where(a0_is_bit, ok_unique, ok_set)
                    rollout_q_acc_terms.append(float(ok.float().mean().item()))

                    pick_first = (torch.rand((B,), device=device) < 0.5).to(torch.bool)
                    teacher_set = torch.where(pick_first, bit0, bit1).to(torch.long)
                    teacher_unique = tgt_unique
                    teacher_a = torch.where(a0_is_bit, teacher_unique, teacher_set).to(torch.long)

                    use_teacher = (torch.rand((B,), device=device) < float(p_tf)).to(torch.bool)
                    a_next = torch.where(use_teacher, teacher_a, pred_a).to(torch.long)
                    actions_prefix[:, t] = a_next

                    rr = tables[torch.arange(B, device=device), a_next, x.to(torch.long)]
                    responses_prefix[:, t] = rr.to(torch.long)

        y_logits = modelA.predict_y(
            tables=tables,
            sigma=sigma,
            base_obs=base_obs,
            actions=actions_prefix,
            responses=responses_prefix,
            t=q_steps,
        )
        y_loss = F.cross_entropy(y_logits, y.to(torch.long))

        bvis = modelB_vis(base_obs)
        bcue = modelB_cue(tables, sigma)
        bvis_loss = F.cross_entropy(bvis, y.to(torch.long))
        bcue_loss = F.cross_entropy(bcue, y.to(torch.long))

        q_loss = torch.stack(q_loss_terms, dim=0).mean()
        loss = y_loss + q_loss + 0.1 * (bvis_loss + bcue_loss)

        opt.zero_grad(set_to_none=True)
        loss.backward()
        opt.step()

        if step % (250 if profile == "solid" else 50) == 0 or step == steps:
            with torch.no_grad():
                y_acc = _acc_from_logits(y_logits, y)
                q_acc = float(sum(rollout_q_acc_terms) / max(1, len(rollout_q_acc_terms)))
                outA = modelA.rollout(tables=tables, sigma=sigma, x=x, base_obs=base_obs, steps=int(q_steps))
                A_acc_batch = _acc_from_logits(outA["y_logits"], y)
            print(
                f"step={step}/{steps} loss={float(loss.item()):.6f} "
                f"(y={float(y_loss.item()):.6f}, q={float(q_loss.item()):.6f}, "
                f"Bvis={float(bvis_loss.item()):.6f}, Bcue={float(bcue_loss.item()):.6f}) "
                f"y_acc={y_acc:.4f} q_acc={q_acc:.4f} A_acc_batch={A_acc_batch:.4f} p_tf={float(p_tf):.3f}"
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
        steps=q_steps,
        obs_vocab=obs_vocab,
        ood=False,
        seed=seed + 101,
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
        steps=q_steps,
        obs_vocab=obs_vocab,
        ood=True,
        seed=seed + 131,
        cfg=eval_cfg,
    )

    rec = {
        "kind": "aslmt_v18_algebra_multistep_64_strong_actionz_v3",
        "seed": int(seed),
        "n_states": int(n_states),
        "n_views": int(n_views),
        "y_classes": int(y_classes),
        "q_steps": int(q_steps),
        "obs_vocab": int(obs_vocab),
        "z_classes": int(n_views),
        "profile": str(profile),
        "tf_decay_frac": float(tf_decay_frac),
        "metrics": {"iid": iid, "ood": ood},
    }

    master = Path(args.master_jsonl).expanduser().resolve()
    master.parent.mkdir(parents=True, exist_ok=True)
    with open(master, "a", encoding="utf-8") as f:
        f.write(json.dumps(rec) + "\n")


if __name__ == "__main__":
    main()
