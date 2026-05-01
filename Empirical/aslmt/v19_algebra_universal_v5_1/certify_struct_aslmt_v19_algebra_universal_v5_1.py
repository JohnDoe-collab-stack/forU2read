import argparse
import hashlib
import json
from datetime import datetime
from pathlib import Path
from typing import Any

import torch

from aslmt_env_v19_algebra_universal_v5_1 import AlgebraUniversalEpisodeCfg, sample_episode
from aslmt_oracle_v19_algebra_universal_v5_1_common import (
    HorizonOracleCfg,
    oracle_allowed_actions,
)
from aslmt_model_v19_algebra_universal_v5_1_actionz import V19AlgebraUniversalModelA_ActionZ


HERE = Path(__file__).resolve().parent


def _now_ts() -> str:
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def _sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    h.update(p.read_bytes())
    return h.hexdigest()


def _tensor_to_jsonable(x: torch.Tensor) -> Any:
    x = x.detach().cpu()
    if x.ndim == 0:
        return int(x.item())
    return x.to(torch.long).tolist()


def _first_stop_t(*, actions: list[int], stop_action: int, max_steps: int) -> int:
    for t in range(int(max_steps)):
        if int(actions[t]) == int(stop_action):
            return int(t)
    return int(max_steps)


def _candidate_mask_exact(
    *,
    tables: torch.Tensor,  # (V,N)
    base_obs: int,
    actions: list[int],
    responses: list[int],
    stop_action: int,
) -> torch.Tensor:
    tables = tables.detach().cpu().to(torch.long)
    V, _ = tables.shape
    if int(stop_action) != int(V):
        raise ValueError("stop_action must equal n_views == V")
    cand = tables[0].eq(int(base_obs))
    for a, r in zip(actions, responses):
        a = int(a)
        if int(a) == int(stop_action):
            continue
        cand = cand & tables[int(a)].eq(int(r))
    return cand


def _sigma_ambiguity_exact(*, sigma: torch.Tensor, cand_mask: torch.Tensor) -> int:
    sigma = sigma.detach().cpu().to(torch.long)
    idx = cand_mask.nonzero(as_tuple=False).flatten()
    if int(idx.numel()) == 0:
        return 0
    vals = torch.unique(sigma[idx])
    return int(vals.numel())


def _sigma_star_exact(*, sigma: torch.Tensor, cand_mask: torch.Tensor) -> int:
    sigma = sigma.detach().cpu().to(torch.long)
    idx = cand_mask.nonzero(as_tuple=False).flatten()
    if int(idx.numel()) == 0:
        raise ValueError("sigma_star undefined on empty candidate set")
    vals = torch.unique(sigma[idx])
    if int(vals.numel()) != 1:
        raise ValueError("sigma_star requires ambiguity==1")
    return int(vals[0].item())


def _run_oracle_policy(
    *,
    tables: torch.Tensor,  # (V,N)
    sigma: torch.Tensor,  # (N,)
    x: int,
    base_obs: int,
    max_steps: int,
) -> tuple[list[int], list[int]]:
    tables_cpu = tables.detach().cpu().to(torch.long)
    sigma_cpu = sigma.detach().cpu().to(torch.long)
    V, _ = tables_cpu.shape
    stop = int(V)

    cfg = HorizonOracleCfg(forbid_view0=True, allow_stop_only_if_closed=True)
    actions: list[int] = []
    responses: list[int] = []
    stopped = False
    for _t in range(int(max_steps)):
        if stopped:
            actions.append(int(stop))
            responses.append(0)
            continue

        cand = _candidate_mask_exact(
            tables=tables_cpu,
            base_obs=int(base_obs),
            actions=list(actions),
            responses=list(responses),
            stop_action=int(stop),
        )
        if int(_sigma_ambiguity_exact(sigma=sigma_cpu, cand_mask=cand)) == 1:
            stopped = True
            actions.append(int(stop))
            responses.append(0)
            continue

        allowed = oracle_allowed_actions(
            tables=tables_cpu,
            sigma=sigma_cpu,
            base_obs=int(base_obs),
            actions_prefix=list(actions),
            responses_prefix=list(responses),
            remaining_steps=int(max_steps - len(actions)),
            cfg=cfg,
        )
        allowed = [int(a) for a in allowed if int(a) != int(stop)]
        if not allowed:
            allowed = [a for a in range(1, int(V)) if a not in set(actions)]
        if not allowed:
            raise RuntimeError("oracle failure: no allowed action available")
        a = int(min(allowed))
        actions.append(int(a))
        responses.append(int(tables_cpu[int(a), int(x)].item()))

    return actions, responses


def _run_model_policy(
    *,
    modelA: V19AlgebraUniversalModelA_ActionZ,
    tables: torch.Tensor,  # (V,N)
    sigma: torch.Tensor,  # (N,)
    x: int,
    base_obs: int,
    max_steps: int,
    device: str,
) -> tuple[list[int], list[int], int]:
    modelA.eval()
    with torch.no_grad():
        out = modelA.rollout(
            tables=tables[None].to(device),
            sigma=sigma[None].to(device),
            x=torch.tensor([int(x)], device=device, dtype=torch.long),
            base_obs=torch.tensor([int(base_obs)], device=device, dtype=torch.long),
            max_steps=int(max_steps),
        )
        actions = out["actions"][0].detach().cpu().to(torch.long).tolist()
        responses = out["responses"][0].detach().cpu().to(torch.long).tolist()
        y_pred = int(torch.argmax(out["y_logits"][0].detach().cpu(), dim=-1).item())
    return [int(a) for a in actions], [int(r) for r in responses], int(y_pred)


def _write_jsonl(path: Path, recs: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        for rec in recs:
            f.write(json.dumps(rec, sort_keys=True) + "\n")


def main() -> None:
    p = argparse.ArgumentParser(description="Produce episode-level structural certificates for v19 universal v5.1.")
    p.add_argument("--out-jsonl", type=str, required=True)
    p.add_argument("--split", choices=["iid", "ood"], required=True)
    p.add_argument("--episodes", type=int, default=1024)
    p.add_argument("--seed-base", type=int, default=0)
    p.add_argument("--n-states", type=int, required=True)
    p.add_argument("--n-views", type=int, default=8)
    p.add_argument("--y-classes", type=int, default=2)
    p.add_argument("--obs-vocab", type=int, default=16)
    p.add_argument("--max-steps", type=int, default=3)
    p.add_argument("--policy", choices=["oracle", "model"], default="oracle")
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--model-state-dict", type=str, default="")
    args = p.parse_args()

    out_jsonl = Path(args.out_jsonl)
    split = str(args.split)
    ood = split == "ood"

    env_path = HERE / "aslmt_env_v19_algebra_universal_v5_1.py"
    verify_path = HERE / "verify_struct_aslmt_v19_algebra_universal_v5_1.py"
    certify_path = Path(__file__).resolve()

    run_meta = {
        "run_tag": f"aslmt_struct_cert_v5_1_{split}",
        "timestamp": _now_ts(),
        "sha256": {
            "certify_script": _sha256_file(certify_path),
            "verify_script": _sha256_file(verify_path) if verify_path.exists() else "",
            "env_script": _sha256_file(env_path) if env_path.exists() else "",
            "model_weights": "",
        },
        "config": {
            "N": int(args.n_states),
            "V": int(args.n_views),
            "T": int(args.max_steps),
            "obs_vocab": int(args.obs_vocab),
            "y_classes": int(args.y_classes),
            "split": split,
            "seed_base": int(args.seed_base),
            "episodes": int(args.episodes),
            "policy": str(args.policy),
        },
    }

    modelA: V19AlgebraUniversalModelA_ActionZ | None = None
    if str(args.policy) == "model":
        if not str(args.model_state_dict):
            raise SystemExit("--model-state-dict is required for --policy model")
        run_meta["sha256"]["model_weights"] = _sha256_file(Path(args.model_state_dict))
        modelA = V19AlgebraUniversalModelA_ActionZ(
            n_views=int(args.n_views),
            n_states=int(args.n_states),
            y_classes=int(args.y_classes),
            obs_vocab=int(args.obs_vocab),
        ).to(str(args.device))
        sd = torch.load(str(args.model_state_dict), map_location=str(args.device))
        modelA.load_state_dict(sd)

    ep_cfg = AlgebraUniversalEpisodeCfg(
        n_states=int(args.n_states),
        n_views=int(args.n_views),
        y_classes=int(args.y_classes),
        obs_vocab=int(args.obs_vocab),
        max_steps=int(args.max_steps),
    )
    recs: list[dict] = []
    for i in range(int(args.episodes)):
        ep = sample_episode(idx=int(i), cfg=ep_cfg, ood=bool(ood), seed_base=int(args.seed_base))
        tables = ep["tables"]
        sigma = ep["sigma"]
        x = int(ep["x"].item())
        base_obs = int(ep["base_obs"].item())
        stop_action = int(ep["stop_action"].item())
        max_steps = int(ep["max_steps"].item())

        if str(args.policy) == "oracle":
            actions, responses = _run_oracle_policy(
                tables=tables, sigma=sigma, x=int(x), base_obs=int(base_obs), max_steps=int(max_steps)
            )
            t_stop = _first_stop_t(actions=actions, stop_action=int(stop_action), max_steps=int(max_steps))
            cand = _candidate_mask_exact(
                tables=tables,
                base_obs=int(base_obs),
                actions=actions[:t_stop],
                responses=responses[:t_stop],
                stop_action=int(stop_action),
            )
            # Oracle baseline: output the *exact* unique-branch readout, if closed.
            # This is a structural sanity check for the verifier/test harness.
            y_pred = int(_sigma_star_exact(sigma=sigma, cand_mask=cand))
        else:
            assert modelA is not None
            actions, responses, y_pred = _run_model_policy(
                modelA=modelA,
                tables=tables,
                sigma=sigma,
                x=int(x),
                base_obs=int(base_obs),
                max_steps=int(max_steps),
                device=str(args.device),
            )

        recs.append(
            {
                "run_meta": run_meta,
                "episode_id": int(i),
                "episode": {
                    "tables": _tensor_to_jsonable(tables),
                    "sigma": _tensor_to_jsonable(sigma),
                    "x": int(x),
                    "base_obs": int(base_obs),
                    "max_steps": int(max_steps),
                    "stop_action": int(stop_action),
                },
                "agent": {
                    "actions": [int(a) for a in actions],
                    "responses": [int(r) for r in responses],
                    "y_pred": int(y_pred),
                },
            }
        )

    _write_jsonl(out_jsonl, recs)
    print(f"WROTE {str(out_jsonl)} lines={len(recs)}")


if __name__ == "__main__":
    main()

