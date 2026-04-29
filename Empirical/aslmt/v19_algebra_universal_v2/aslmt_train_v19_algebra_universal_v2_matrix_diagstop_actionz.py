import argparse
import json
import random
from dataclasses import dataclass
from pathlib import Path

import torch
import torch.nn.functional as F
from torch.utils.data import DataLoader

from aslmt_env_v19_algebra_universal_v2 import V19AlgebraUniversalDataset
from aslmt_model_v19_algebra_universal_v2_actionz import (
    V19AlgebraCueOnlyBaseline,
    V19AlgebraUniversalModelA_ActionZ,
    V19AlgebraVisibleOnlyBaseline,
)
from aslmt_oracle_v19_algebra_universal_v2_common import HorizonOracleCfg, oracle_allowed_actions


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

    with torch.no_grad():
        for batch in dl:
            tables = batch["tables"].to(device)
            sigma = batch["sigma"].to(device)
            x = batch["x"].to(device)
            y = batch["y"].to(device)
            base_obs = batch["base_obs"].to(device)

            outA = modelA.rollout(tables=tables, sigma=sigma, x=x, base_obs=base_obs, max_steps=int(max_steps))
            A_acc.append(_acc_from_logits(outA["y_logits"], y))

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

    return {
        "A_acc": _mean(A_acc),
        "B_vis_acc": _mean(Bvis_acc),
        "B_cue_acc": _mean(Bcue_acc),
        "A_abl_acc": _mean(Abl_acc),
        "A_swap_acc": _mean(Swap_acc),
        "swap_action_follow_rate": _mean(swap_action_follow),
    }


def main() -> None:
    p = argparse.ArgumentParser(description="ASLMT v19 algebra universal v2 trainer (horizon oracle, action-as-z).")
    p.add_argument("--profile", type=str, default="solid", choices=["smoke", "solid"])
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--steps", type=int, default=4000)
    p.add_argument("--batch-size", type=int, default=64)
    p.add_argument("--lr", type=float, default=3e-4)
    p.add_argument("--n-states", type=int, required=True)
    p.add_argument("--n-views", type=int, default=8)
    p.add_argument("--y-classes", type=int, default=2)
    p.add_argument("--obs-vocab", type=int, default=16)
    p.add_argument("--max-steps", type=int, default=3)
    p.add_argument("--tf-decay-frac", type=float, default=0.8)
    p.add_argument("--master-jsonl", type=str, required=True)
    args = p.parse_args()

    profile = str(args.profile)
    steps = int(args.steps)
    batch_size = int(args.batch_size)
    if profile == "smoke":
        if steps == 4000:
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

    modelA = V19AlgebraUniversalModelA_ActionZ(n_views=int(n_views), y_classes=int(y_classes), obs_vocab=int(obs_vocab)).to(device)
    modelB_vis = V19AlgebraVisibleOnlyBaseline(obs_vocab=int(obs_vocab), y_classes=int(y_classes)).to(device)
    modelB_cue = V19AlgebraCueOnlyBaseline(n_views=int(n_views), n_states=int(n_states), obs_vocab=int(obs_vocab), y_classes=int(y_classes)).to(device)

    opt = torch.optim.AdamW(list(modelA.parameters()) + list(modelB_vis.parameters()) + list(modelB_cue.parameters()), lr=float(args.lr))

    ds = V19AlgebraUniversalDataset(
        size=steps * batch_size,
        n_states=int(n_states),
        n_views=int(n_views),
        y_classes=int(y_classes),
        obs_vocab=int(obs_vocab),
        max_steps=int(max_steps),
        ood=False,
        seed=int(args.seed),
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

        p_tf = max(0.0, 1.0 - float(step) / max(1.0, float(steps) * float(tf_decay_frac)))

        q_losses = []
        q_acc_terms = []
        for t in range(int(max_steps)):
            logits = modelA.logits_query(
                tables=tables, sigma=sigma, base_obs=base_obs, actions=actions_prefix, responses=responses_prefix, t=int(t), max_steps=int(max_steps)
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

            pred = torch.argmax(logits, dim=-1)
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

            use_teacher = (torch.rand((B,), device=device) < float(p_tf)).to(torch.bool)
            a_next = torch.where(use_teacher, teacher, pred).to(torch.long)
            actions_prefix[:, t] = a_next

            is_stop = a_next.eq(int(V))
            a_clamped = a_next.clamp(0, int(V) - 1)
            rr = tables[torch.arange(B, device=device), a_clamped, x.to(torch.long)]
            rr = torch.where(is_stop, torch.zeros_like(rr), rr)
            responses_prefix[:, t] = rr.to(torch.long)

        q_loss = torch.stack(q_losses, dim=0).mean()

        y_logits = modelA.predict_y(tables=tables, sigma=sigma, base_obs=base_obs, actions=actions_prefix, responses=responses_prefix, t=int(max_steps))
        y_loss = F.nll_loss(y_logits, y.to(torch.long))

        bvis = modelB_vis(base_obs)
        bcue = modelB_cue(tables, sigma)
        bvis_loss = F.cross_entropy(bvis, y.to(torch.long))
        bcue_loss = F.cross_entropy(bcue, y.to(torch.long))

        loss = y_loss + q_loss + 0.1 * (bvis_loss + bcue_loss)

        opt.zero_grad(set_to_none=True)
        loss.backward()
        opt.step()

        if step % (250 if profile == "solid" else 50) == 0 or step == steps:
            with torch.no_grad():
                y_acc = _acc_from_logits(y_logits, y)
                q_acc = float(sum(q_acc_terms) / max(1, len(q_acc_terms)))
                outA = modelA.rollout(tables=tables, sigma=sigma, x=x, base_obs=base_obs, max_steps=int(max_steps))
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
        "kind": "aslmt_v19_algebra_universal_actionz_v2",
        "seed": int(args.seed),
        "n_states": int(n_states),
        "n_views": int(n_views),
        "y_classes": int(y_classes),
        "obs_vocab": int(obs_vocab),
        "max_steps": int(max_steps),
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

