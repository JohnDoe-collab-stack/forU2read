import argparse
import json
import random
from dataclasses import dataclass
from pathlib import Path

import torch
import torch.nn.functional as F
from torch.utils.data import DataLoader

from aslmt_env_v18_algebra_total import V18AlgebraTotalDataset
from aslmt_model_v18_algebra_total import V18AlgebraTotalModelA, V18VisibleOnlyBaseline


def _seed_everything(seed: int) -> None:
    seed = int(seed)
    random.seed(seed)
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)


def _env_responses(
    *,
    h: torch.Tensor,
    k_bits: torch.Tensor,
    actions: torch.Tensor,
    ood_shift: torch.Tensor,
    m_actions: int,
) -> torch.Tensor:
    """
    Deterministic multi-interface response:

    For each bit j in k_bits, there is a designated action:
      a_j = (h + j + ood_shift) % m_actions

    The policy chooses an action per bit: actions.shape == (B,k_dim).

    Response vector r has size k_dim:
      r[j] = k_bits[j] when actions[j]==a_j else 0.
    """
    h = h.to(torch.long)
    actions = actions.to(torch.long)
    ood_shift = ood_shift.to(torch.long)

    B, k_dim = k_bits.shape
    if actions.shape != (B, k_dim):
        raise ValueError(f"actions must have shape (B,k_dim)={(B,k_dim)}, got {tuple(actions.shape)}")
    out = torch.zeros((B, k_dim), device=k_bits.device, dtype=torch.float32)
    for j in range(int(k_dim)):
        aj = (h + int(j) + ood_shift) % int(m_actions)
        correct = (actions[:, j] == aj).to(torch.float32)
        out[:, j] = correct * k_bits[:, j].to(torch.float32)
    return out


def _target_y(*, h: torch.Tensor, k_bits: torch.Tensor) -> torch.Tensor:
    """
    Target depends on (h,k): y = parity(k_bits[0:use_dim]) XOR (h % 2).

    We set use_dim=2 by default to keep the task learnable while still requiring
    a genuinely multi-interface query (two components).
    """
    h2 = (h.to(torch.long) % 2).to(torch.long)
    use_dim = int(min(2, int(k_bits.shape[1])))
    parity = (k_bits[:, :use_dim].to(torch.long).sum(dim=1) % 2).to(torch.long)
    return (parity ^ h2).to(torch.long)


@dataclass(frozen=True)
class Metrics:
    A_acc: float
    B_acc: float
    z_acc: float
    q_acc: float
    action_rate: float


def _eval_once(
    *,
    modelA: V18AlgebraTotalModelA,
    modelB: V18VisibleOnlyBaseline,
    device: torch.device,
    n_classes: int,
    k_dim: int,
    m_actions: int,
    seed: int,
    kind: str,
    batch_size: int = 256,
) -> Metrics:
    ds = V18AlgebraTotalDataset(size=2048, n_classes=int(n_classes), k_dim=int(k_dim), m_actions=int(m_actions), seed=int(seed), ood_kind=str(kind))
    dl = DataLoader(ds, batch_size=int(batch_size), shuffle=False, collate_fn=lambda b: V18AlgebraTotalDataset.collate(b, k_dim=int(k_dim)))

    A_ok = 0
    B_ok = 0
    z_ok = 0
    q_ok = 0
    tot = 0
    act_sum = 0

    modelA.eval()
    modelB.eval()
    with torch.no_grad():
        for batch in dl:
            h = batch["h"].to(device)
            k_bits = batch["k_bits"].to(device)
            ood_shift = batch["ood_shift"].to(device)

            # Policy query.
            z_logits = modelA.z_logits(h)
            z_ok += int((torch.argmax(z_logits, dim=-1) == h.to(torch.long)).sum().item())

            logits_q = modelA.logits_query(h)  # (B,k_dim,m_actions)
            a = torch.argmax(logits_q, dim=-1)  # (B,k_dim)

            # Query correctness across all bits.
            for j in range(int(k_dim)):
                aj = (h.to(torch.long) + int(j) + ood_shift.to(torch.long)) % int(m_actions)
                q_ok += int((a[:, j] == aj).sum().item())

            # Responses and prediction.
            r = _env_responses(h=h, k_bits=k_bits, actions=a, ood_shift=ood_shift, m_actions=int(m_actions))
            logits_yA = modelA.forward_with_responses(h, r)
            y = _target_y(h=h, k_bits=k_bits)
            A_ok += int((torch.argmax(logits_yA, dim=-1) == y).sum().item())

            logits_yB = modelB(h)
            B_ok += int((torch.argmax(logits_yB, dim=-1) == y).sum().item())

            tot += int(h.shape[0])
            act_sum += float(a.float().mean().item())

    return Metrics(
        A_acc=float(A_ok / max(1, tot)),
        B_acc=float(B_ok / max(1, tot)),
        z_acc=float(z_ok / max(1, tot)),
        q_acc=float(q_ok / max(1, tot * int(k_dim))),
        action_rate=float(act_sum / max(1, len(dl))),
    )


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--profile", type=str, default="solid", choices=["smoke", "solid"])
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--steps", type=int, default=4000)
    p.add_argument("--batch-size", type=int, default=256)
    p.add_argument("--lr", type=float, default=3e-3)
    p.add_argument("--n-classes", type=int, required=True)
    p.add_argument("--z-classes", type=int, required=True)
    p.add_argument("--m-actions", type=int, default=4)
    p.add_argument("--k-dim", type=int, default=2)
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--out-jsonl", type=str, default="")
    args = p.parse_args()

    profile = str(args.profile)
    if profile == "smoke":
        if int(args.steps) == 4000:
            args.steps = 1500

    _seed_everything(int(args.seed))

    device = torch.device(str(args.device))
    modelA = V18AlgebraTotalModelA(
        n_classes=int(args.n_classes),
        z_classes=int(args.z_classes),
        m_actions=int(args.m_actions),
        k_dim=int(args.k_dim),
    ).to(device)
    modelB = V18VisibleOnlyBaseline(n_classes=int(args.n_classes)).to(device)

    optA = torch.optim.Adam(modelA.parameters(), lr=float(args.lr))
    optB = torch.optim.Adam(modelB.parameters(), lr=float(args.lr))

    ds_iid = V18AlgebraTotalDataset(size=8192, n_classes=int(args.n_classes), k_dim=int(args.k_dim), m_actions=int(args.m_actions), seed=int(args.seed), ood_kind="iid")
    dl = DataLoader(ds_iid, batch_size=int(args.batch_size), shuffle=True, drop_last=True, collate_fn=lambda b: V18AlgebraTotalDataset.collate(b, k_dim=int(args.k_dim)))

    it = iter(dl)
    for step in range(1, int(args.steps) + 1):
        try:
            batch = next(it)
        except StopIteration:
            it = iter(dl)
            batch = next(it)

        h = batch["h"].to(device)
        k_bits = batch["k_bits"].to(device)
        ood_shift = batch["ood_shift"].to(device)

        z_logits = modelA.z_logits(h)
        loss_z = F.cross_entropy(z_logits, h.to(torch.long))

        # Train query head to select canonical action for bit0.
        logits_q = modelA.logits_query(h)  # (B,k_dim,m_actions)
        losses_q = []
        a_choices = []
        for j in range(int(args.k_dim)):
            aj = (h.to(torch.long) + int(j) + ood_shift.to(torch.long)) % int(args.m_actions)
            losses_q.append(F.cross_entropy(logits_q[:, j, :], aj))
            a_choices.append(torch.argmax(logits_q[:, j, :], dim=-1))
        loss_q = torch.stack(losses_q).mean()
        a = torch.stack(a_choices, dim=1)  # (B,k_dim)
        r = _env_responses(h=h, k_bits=k_bits, actions=a, ood_shift=ood_shift, m_actions=int(args.m_actions))
        y = _target_y(h=h, k_bits=k_bits)
        logits_yA = modelA.forward_with_responses(h, r)
        loss_yA = F.cross_entropy(logits_yA, y)

        optA.zero_grad(set_to_none=True)
        (loss_yA + loss_q + loss_z).backward()
        optA.step()

        logits_yB = modelB(h)
        loss_yB = F.cross_entropy(logits_yB, y)
        optB.zero_grad(set_to_none=True)
        loss_yB.backward()
        optB.step()

        if step % 250 == 0 or step == int(args.steps):
            metrics_iid = _eval_once(
                modelA=modelA,
                modelB=modelB,
                device=device,
                n_classes=int(args.n_classes),
                k_dim=int(args.k_dim),
                m_actions=int(args.m_actions),
                seed=int(args.seed) + 1000,
                kind="iid",
            )
            metrics_ood = _eval_once(
                modelA=modelA,
                modelB=modelB,
                device=device,
                n_classes=int(args.n_classes),
                k_dim=int(args.k_dim),
                m_actions=int(args.m_actions),
                seed=int(args.seed) + 2000,
                kind="ood",
            )

            msg = {
                "kind": "aslmt_v18_algebra_total",
                "seed": int(args.seed),
                "n_classes": int(args.n_classes),
                "z_classes": int(args.z_classes),
                "m_actions": int(args.m_actions),
                "k_dim": int(args.k_dim),
                "step": int(step),
                "metrics": {
                    "iid": metrics_iid.__dict__,
                    "ood": metrics_ood.__dict__,
                },
            }
            print(json.dumps(msg))

    if str(args.out_jsonl):
        Path(args.out_jsonl).parent.mkdir(parents=True, exist_ok=True)
        final = {
            "kind": "aslmt_v18_algebra_total",
            "seed": int(args.seed),
            "n_classes": int(args.n_classes),
            "z_classes": int(args.z_classes),
            "m_actions": int(args.m_actions),
            "k_dim": int(args.k_dim),
            "metrics": {
                "iid": _eval_once(
                    modelA=modelA,
                    modelB=modelB,
                    device=device,
                    n_classes=int(args.n_classes),
                    k_dim=int(args.k_dim),
                    m_actions=int(args.m_actions),
                    seed=int(args.seed) + 3000,
                    kind="iid",
                ).__dict__,
                "ood": _eval_once(
                    modelA=modelA,
                    modelB=modelB,
                    device=device,
                    n_classes=int(args.n_classes),
                    k_dim=int(args.k_dim),
                    m_actions=int(args.m_actions),
                    seed=int(args.seed) + 4000,
                    kind="ood",
                ).__dict__,
            },
        }
        with open(str(args.out_jsonl), "a", encoding="utf-8") as f:
            f.write(json.dumps(final) + "\n")


if __name__ == "__main__":
    main()
