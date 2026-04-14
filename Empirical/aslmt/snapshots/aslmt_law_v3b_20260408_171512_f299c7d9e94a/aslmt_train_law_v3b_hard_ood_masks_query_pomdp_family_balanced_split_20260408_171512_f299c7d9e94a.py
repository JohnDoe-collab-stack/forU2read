#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict
from pathlib import Path

import torch

from aslmt_env_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split import (
    LawV3QueryPOMDPConfig,
    LawV3Tokens,
    env_step_result_token,
    sample_batch,
)
from aslmt_model_law_v3b_memory import LawV3MemoryPolicyV1, LawV3VisibleOnlyPolicyV1


def _timestamp() -> str:
    return time.strftime("%Y-%m-%d %H:%M:%S")


def _rollout_memory_policy(
    *,
    model: LawV3MemoryPolicyV1,
    cfg: LawV3QueryPOMDPConfig,
    batch: dict,
    device: str,
    sample: bool,
    ablate_query_mem: bool = False,
    ablate_out_mem: bool = False,
) -> dict:
    H = batch["H"]
    i = batch["i"]
    lo_tok = batch["lo_tok"]
    view_seq = batch["view_seq"]  # [B, T]
    d1 = batch["d1"]
    d2 = batch["d2"]
    B = int(H.shape[0])

    mem = model.init_mem(B, device)

    # Integrate the full view token sequence (mask bits + parity tokens).
    for t in range(int(view_seq.shape[1])):
        mem = model.step_mem(mem, view_seq[:, t])

    # Delays between views and query decision.
    if int(d1.max().item()) > 0:
        for k in range(int(d1.max().item())):
            tok = torch.full((B,), LawV3Tokens.DELAY, device=device, dtype=torch.long)
            mask = d1.gt(k).float().unsqueeze(1)
            mem = mem + mask * (model.step_mem(mem, tok) - mem)

    # Critical anti-bypass: do NOT inject current lo-token into memory before query.
    _ = lo_tok

    mem_for_query = torch.zeros_like(mem) if ablate_query_mem else mem
    logits_q = model.logits_query(mem_for_query)
    if sample:
        a_hi = torch.distributions.Categorical(logits=logits_q).sample()
    else:
        a_hi = model.greedy_action(logits_q)
    logp_q, ent_q = model.dist_logprob_entropy(logits_q, a_hi)
    v_q = model.value(mem_for_query)

    correct, bit, res_tok = env_step_result_token(cfg=cfg, H=H, i=i, a_hi=a_hi)

    # Delays between query result and final output decision.
    if int(d2.max().item()) > 0:
        for k in range(int(d2.max().item())):
            tok = torch.full((B,), LawV3Tokens.DELAY, device=device, dtype=torch.long)
            mask = d2.gt(k).float().unsqueeze(1)
            mem = mem + mask * (model.step_mem(mem, tok) - mem)

    mem = model.step_mem(mem, res_tok.to(device))

    mem_for_out = torch.zeros_like(mem) if ablate_out_mem else mem
    logits_out = model.logits_out(mem_for_out)
    if sample:
        out = torch.distributions.Categorical(logits=logits_out).sample()
    else:
        out = model.greedy_action(logits_out)
    logp_out, ent_out = model.dist_logprob_entropy(logits_out, out)
    v_out = model.value(mem_for_out)

    reward = (correct & out.eq(bit)).float()

    return {"reward": reward, "logp_q": logp_q, "logp_out": logp_out, "ent_q": ent_q, "ent_out": ent_out, "v_q": v_q, "v_out": v_out, "mem_query": mem_for_query.detach(), "mem_out": mem_for_out.detach()}


def _rollout_visible_only(*, model: LawV3VisibleOnlyPolicyV1, cfg: LawV3QueryPOMDPConfig, batch: dict, device: str, sample: bool) -> dict:
    H = batch["H"]
    i = batch["i"]
    lo_tok = batch["lo_tok"]
    B = int(H.shape[0])

    logits_q = model.logits_query(lo_tok)
    if sample:
        a_hi = torch.distributions.Categorical(logits=logits_q).sample()
    else:
        a_hi = model.greedy_action(logits_q)
    logp_q, ent_q = model.dist_logprob_entropy(logits_q, a_hi)
    v_q = model.value(lo_tok)

    correct, bit, res_tok = env_step_result_token(cfg=cfg, H=H, i=i, a_hi=a_hi)

    logits_out = model.logits_out(res_tok.to(device))
    if sample:
        out = torch.distributions.Categorical(logits=logits_out).sample()
    else:
        out = model.greedy_action(logits_out)
    logp_out, ent_out = model.dist_logprob_entropy(logits_out, out)
    v_out = model.value(res_tok.to(device))

    reward = (correct & out.eq(bit)).float()
    return {"reward": reward, "logp_q": logp_q, "logp_out": logp_out, "ent_q": ent_q, "ent_out": ent_out, "v_q": v_q, "v_out": v_out}


@torch.no_grad()
def _eval_memory_policy(*, model: LawV3MemoryPolicyV1, cfg: LawV3QueryPOMDPConfig, device: str, batch_size: int, ood: bool, seed: int) -> float:
    batch = sample_batch(batch_size=batch_size, cfg=cfg, device=device, ood=ood, seed=seed)
    out = _rollout_memory_policy(model=model, cfg=cfg, batch=batch, device=device, sample=False)
    return float(out["reward"].mean().item())


@torch.no_grad()
def _eval_visible_only(*, model: LawV3VisibleOnlyPolicyV1, cfg: LawV3QueryPOMDPConfig, device: str, batch_size: int, ood: bool, seed: int) -> float:
    batch = sample_batch(batch_size=batch_size, cfg=cfg, device=device, ood=ood, seed=seed)
    out = _rollout_visible_only(model=model, cfg=cfg, batch=batch, device=device, sample=False)
    return float(out["reward"].mean().item())


@torch.no_grad()
def _audit_causal_memory(*, model: LawV3MemoryPolicyV1, cfg: LawV3QueryPOMDPConfig, device: str, batch_size: int, ood: bool, seed: int) -> dict:
    batch = sample_batch(batch_size=batch_size, cfg=cfg, device=device, ood=ood, seed=seed)
    base = _rollout_memory_policy(model=model, cfg=cfg, batch=batch, device=device, sample=False)
    base_succ = float(base["reward"].mean().item())

    abl = _rollout_memory_policy(model=model, cfg=cfg, batch=batch, device=device, sample=False, ablate_query_mem=True, ablate_out_mem=True)
    abl_succ = float(abl["reward"].mean().item())

    perm = torch.randperm(batch_size, device=device)
    mem_out_swapped = base["mem_out"][perm]

    logits_q = model.logits_query(base["mem_query"])
    a_hi = model.greedy_action(logits_q)

    correct, bit, _ = env_step_result_token(cfg=cfg, H=batch["H"], i=batch["i"], a_hi=a_hi)
    out_bad = model.greedy_action(model.logits_out(mem_out_swapped))
    succ_swap_vs_orig = float((correct & out_bad.eq(bit)).float().mean().item())

    H_p = batch["H"][perm]
    i_p = batch["i"][perm]
    correct_p, bit_p, _ = env_step_result_token(cfg=cfg, H=H_p, i=i_p, a_hi=a_hi[perm])
    out_good = model.greedy_action(model.logits_out(mem_out_swapped))
    succ_swap_vs_perm = float((correct_p & out_good.eq(bit_p)).float().mean().item())

    return {"base_success": base_succ, "ablate_success": abl_succ, "ablation_drop": base_succ - abl_succ, "swap_vs_orig": succ_swap_vs_orig, "swap_vs_perm": succ_swap_vs_perm}


def _make_cfg_by_name(name: str, profile: str) -> LawV3QueryPOMDPConfig:
    if name == "C0_16b_4i_2hi":
        if profile == "smoke":
            return LawV3QueryPOMDPConfig(n_bits=16, n_index_bits=4, n_hi_bits=2, n_lo_bits=2, n_views=6, iid_delay_max=1, ood_delay_min=2, ood_delay_max=4)
        return LawV3QueryPOMDPConfig(n_bits=16, n_index_bits=4, n_hi_bits=2, n_lo_bits=2, n_views=8, iid_delay_max=2, ood_delay_min=3, ood_delay_max=6)
    if name == "C1_64b_6i_3hi":
        if profile == "smoke":
            return LawV3QueryPOMDPConfig(n_bits=64, n_index_bits=6, n_hi_bits=3, n_lo_bits=3, n_views=8, iid_delay_max=1, ood_delay_min=2, ood_delay_max=5)
        return LawV3QueryPOMDPConfig(n_bits=64, n_index_bits=6, n_hi_bits=3, n_lo_bits=3, n_views=10, iid_delay_max=2, ood_delay_min=3, ood_delay_max=7)
    if name == "C2_128b_7i_4hi":
        if profile == "smoke":
            return LawV3QueryPOMDPConfig(n_bits=128, n_index_bits=7, n_hi_bits=4, n_lo_bits=3, n_views=10, iid_delay_max=1, ood_delay_min=2, ood_delay_max=6)
        return LawV3QueryPOMDPConfig(n_bits=128, n_index_bits=7, n_hi_bits=4, n_lo_bits=3, n_views=12, iid_delay_max=2, ood_delay_min=3, ood_delay_max=8)
    raise ValueError(f"Unknown cfg_name: {name}")


def _train_one(*, cfg_name: str, seed: int, profile: str, device: str, out_jsonl: Path, out_txt: Path, snapshot_tag: str) -> None:
    torch.manual_seed(int(seed))
    device = str(device)
    cfg = _make_cfg_by_name(cfg_name, profile)
    vocab_size = LawV3Tokens.vocab_size(cfg)

    if profile == "smoke":
        steps = 9000
        batch_size = 256
        eval_batch = 2048
        lr = 2e-3
        d_embed = 96
        d_mem = 192
        ent_coef = 0.01
        v_coef = 0.25
    elif profile == "solid":
        steps = 30_000
        batch_size = 512
        eval_batch = 4096
        lr = 1.5e-3
        d_embed = 128
        d_mem = 256
        ent_coef = 0.01
        v_coef = 0.25
    else:
        raise ValueError(f"Unknown profile: {profile}")

    modelA = LawV3MemoryPolicyV1(vocab_size=vocab_size, n_queries=cfg.n_queries, d_embed=d_embed, d_mem=d_mem).to(device)
    modelB = LawV3VisibleOnlyPolicyV1(vocab_size=vocab_size, n_queries=cfg.n_queries, d_embed=d_embed).to(device)

    optA = torch.optim.Adam(modelA.parameters(), lr=lr)
    optB = torch.optim.Adam(modelB.parameters(), lr=lr)

    def update_memory() -> dict:
        batch = sample_batch(batch_size=batch_size, cfg=cfg, device=device, ood=False, seed=None)
        out = _rollout_memory_policy(model=modelA, cfg=cfg, batch=batch, device=device, sample=True)
        reward = out["reward"]
        adv_q = (reward - out["v_q"].detach())
        adv_out = (reward - out["v_out"].detach())
        loss_pg = -(out["logp_q"] * adv_q + out["logp_out"] * adv_out).mean()
        loss_v = v_coef * ((out["v_out"] - reward) ** 2).mean()
        loss_ent = -ent_coef * (out["ent_q"].mean() + out["ent_out"].mean())
        loss = loss_pg + loss_v + loss_ent
        optA.zero_grad()
        loss.backward()
        optA.step()
        return {"reward": float(reward.mean().item()), "loss": float(loss.item())}

    def update_visible() -> dict:
        batch = sample_batch(batch_size=batch_size, cfg=cfg, device=device, ood=False, seed=None)
        out = _rollout_visible_only(model=modelB, cfg=cfg, batch=batch, device=device, sample=True)
        reward = out["reward"]
        adv_q = (reward - out["v_q"].detach())
        adv_out = (reward - out["v_out"].detach())
        loss_pg = -(out["logp_q"] * adv_q + out["logp_out"] * adv_out).mean()
        loss_v = v_coef * ((out["v_out"] - reward) ** 2).mean()
        loss_ent = -ent_coef * (out["ent_q"].mean() + out["ent_out"].mean())
        loss = loss_pg + loss_v + loss_ent
        optB.zero_grad()
        loss.backward()
        optB.step()
        return {"reward": float(reward.mean().item()), "loss": float(loss.item())}

    with open(out_txt, "w", encoding="utf-8") as f:
        f.write(f"timestamp: {_timestamp()}\n")
        f.write(f"snapshot_tag: {snapshot_tag}\n")
        f.write(f"seed: {seed}\n")
        f.write(f"profile: {profile}\n")
        f.write(f"cfg_name: {cfg_name}\n")
        f.write(f"cfg: {json.dumps(asdict(cfg), sort_keys=True)}\n")

    for step in range(1, steps + 1):
        a = update_memory()
        b = update_visible()
        if step == 1 or step % 1000 == 0 or step == steps:
            with open(out_txt, "a", encoding="utf-8") as f:
                f.write(f"step {step}/{steps} A.reward={a['reward']:.4f} A.loss={a['loss']:.4f} | B.reward={b['reward']:.4f} B.loss={b['loss']:.4f}\n")

    A_iid = _eval_memory_policy(model=modelA, cfg=cfg, device=device, batch_size=eval_batch, ood=False, seed=seed)
    B_iid = _eval_visible_only(model=modelB, cfg=cfg, device=device, batch_size=eval_batch, ood=False, seed=seed)
    A_ood = _eval_memory_policy(model=modelA, cfg=cfg, device=device, batch_size=eval_batch, ood=True, seed=seed)
    B_ood = _eval_visible_only(model=modelB, cfg=cfg, device=device, batch_size=eval_batch, ood=True, seed=seed)
    aud_iid = _audit_causal_memory(model=modelA, cfg=cfg, device=device, batch_size=eval_batch, ood=False, seed=seed)
    aud_ood = _audit_causal_memory(model=modelA, cfg=cfg, device=device, batch_size=eval_batch, ood=True, seed=seed)

    row = {"kind": "aslmt_law_v3b_hard_ood_masks_query_pomdp_family_balanced_split", "cfg_name": cfg_name, "cfg": asdict(cfg), "profile": profile, "seed": int(seed), "snapshot_tag": snapshot_tag, "iid": {"A_success": A_iid, "B_success": B_iid, "audit": aud_iid}, "ood": {"A_success": A_ood, "B_success": B_ood, "audit": aud_ood}}
    with open(out_jsonl, "a", encoding="utf-8") as f:
        f.write(json.dumps(row) + "\n")


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--snapshot-tag", type=str, required=True)
    p.add_argument("--seed", type=int, required=True)
    p.add_argument("--profile", type=str, default="smoke", choices=["smoke", "solid"])
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--out-jsonl", type=str, required=True)
    p.add_argument("--out-txt", type=str, required=True)
    p.add_argument("--cfg-name", type=str, required=True, choices=["C0_16b_4i_2hi", "C1_64b_6i_3hi", "C2_128b_7i_4hi"])
    args = p.parse_args()

    _train_one(cfg_name=str(args.cfg_name), seed=int(args.seed), profile=str(args.profile), device=str(args.device), out_jsonl=Path(args.out_jsonl), out_txt=Path(args.out_txt), snapshot_tag=str(args.snapshot_tag))


if __name__ == "__main__":
    main()
