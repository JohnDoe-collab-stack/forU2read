import argparse
import hashlib
import json
from datetime import datetime
from pathlib import Path
from typing import Any

import torch

from aslmt_env_v19_algebra_universal_v5_1 import AlgebraUniversalEpisodeCfg, sample_episode
from aslmt_model_v19_algebra_universal_v5_1_actionz import V19AlgebraUniversalModelA_ActionZ
from aslmt_oracle_v19_algebra_universal_v5_1_common import (
    HorizonOracleCfg,
    oracle_allowed_actions,
)

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


def _choose_action_from_logits(
    *, logits: torch.Tensor, used: set[int], stop_action: int, forbid_view0: bool
) -> int:
    # logits shape: (V+1,)
    scores = logits.detach().cpu().to(torch.float32).clone()
    V1 = int(scores.numel())
    if int(stop_action) != int(V1 - 1):
        # stop_action is V, action space size is V+1
        pass
    # never choose STOP here (STOP is controlled by exact closure check)
    scores[int(stop_action)] = -1e9
    if bool(forbid_view0) and V1 >= 1:
        scores[0] = -1e9
    for a in used:
        if 0 <= int(a) < int(stop_action):
            scores[int(a)] = -1e9
    a = int(torch.argmax(scores, dim=-1).item())
    if int(a) < 0 or int(a) >= int(stop_action):
        # fallback: pick smallest available non-base view
        for j in range(1, int(stop_action)):
            if int(j) not in used:
                return int(j)
        return 1
    return int(a)


def _run_model_policy_exact(
    *,
    modelA: V19AlgebraUniversalModelA_ActionZ,
    tables: torch.Tensor,  # (V,N)
    sigma: torch.Tensor,  # (N,)
    x: int,
    base_obs: int,
    max_steps: int,
    device: str,
    forbid_view0: bool,
    forbid_repeats: bool,
) -> tuple[list[int], list[int], int]:
    """
    Policy = learned query selector, but STOP + readout are exact:

    - At each step t, compute exact closure on current transcript prefix.
      If closed: emit STOP for remaining steps.
    - Otherwise: pick a query action from model logits (with forbid_view0/repeats), observe true response.
    - If closed at or before the budget, y_pred is σ* on the closed prefix.
      Otherwise, y_pred is the model's final y prediction (verifier will fail P2 anyway).
    """
    modelA.eval()
    V, _ = tables.shape
    stop_action = int(V)

    actions: list[int] = []
    responses: list[int] = []
    used: set[int] = set()
    stopped = False
    stop_t: int | None = None

    with torch.no_grad():
        for t in range(int(max_steps)):
            if stopped:
                actions.append(int(stop_action))
                responses.append(0)
                continue

            cand = _candidate_mask_exact(
                tables=tables,
                base_obs=int(base_obs),
                actions=list(actions),
                responses=list(responses),
                stop_action=int(stop_action),
            )
            amb = int(_sigma_ambiguity_exact(sigma=sigma, cand_mask=cand))
            if amb == 1:
                stopped = True
                stop_t = int(t)
                actions.append(int(stop_action))
                responses.append(0)
                continue

            # model proposes next query action
            a_t = torch.tensor(actions + [int(stop_action)] * (int(max_steps) - len(actions)), device=device, dtype=torch.long)[
                None, :
            ]
            r_t = torch.tensor(responses + [0] * (int(max_steps) - len(responses)), device=device, dtype=torch.long)[None, :]
            logits = modelA.logits_query(
                tables=tables[None].to(device),
                sigma=sigma[None].to(device),
                base_obs=torch.tensor([int(base_obs)], device=device, dtype=torch.long),
                actions=a_t,
                responses=r_t,
                t=int(t),
                max_steps=int(max_steps),
            )[0]
            a = _choose_action_from_logits(
                logits=logits,
                used=(used if bool(forbid_repeats) else set()),
                stop_action=int(stop_action),
                forbid_view0=bool(forbid_view0),
            )
            actions.append(int(a))
            if bool(forbid_repeats) and 0 <= int(a) < int(stop_action):
                used.add(int(a))
            responses.append(int(tables[int(a), int(x)].item()))

        # determine stop_t for readout
        if stop_t is None:
            t_stop = _first_stop_t(actions=actions, stop_action=int(stop_action), max_steps=int(max_steps))
            cand = _candidate_mask_exact(
                tables=tables,
                base_obs=int(base_obs),
                actions=actions[:t_stop],
                responses=responses[:t_stop],
                stop_action=int(stop_action),
            )
            if int(_sigma_ambiguity_exact(sigma=sigma, cand_mask=cand)) == 1:
                stop_t = int(t_stop)

        if stop_t is not None:
            cand = _candidate_mask_exact(
                tables=tables,
                base_obs=int(base_obs),
                actions=actions[: int(stop_t)],
                responses=responses[: int(stop_t)],
                stop_action=int(stop_action),
            )
            y_pred = int(_sigma_star_exact(sigma=sigma, cand_mask=cand))
        else:
            out = modelA.predict_y(
                tables=tables[None].to(device),
                sigma=sigma[None].to(device),
                base_obs=torch.tensor([int(base_obs)], device=device, dtype=torch.long),
                actions=torch.tensor(actions, device=device, dtype=torch.long)[None, :],
                responses=torch.tensor(responses, device=device, dtype=torch.long)[None, :],
                t=int(max_steps),
            )[0]
            y_pred = int(torch.argmax(out.detach().cpu(), dim=-1).item())

    return [int(a) for a in actions], [int(r) for r in responses], int(y_pred)


def _run_oracle_policy_exact(
    *,
    tables: torch.Tensor,  # (V,N)
    sigma: torch.Tensor,  # (N,)
    x: int,
    base_obs: int,
    max_steps: int,
    forbid_view0: bool,
) -> tuple[list[int], list[int], int]:
    """
    Oracle certificate = exact environment interaction + exact closure/readout.

    This is only for verifier sanity checks and for demonstrating that the episodes
    are in fact closable within the declared budget; it is not a learned policy.
    """
    V, _ = tables.detach().cpu().shape
    stop_action = int(V)

    cfg = HorizonOracleCfg(
        forbid_view0=bool(forbid_view0),
        allow_stop_only_if_closed=True,
    )

    actions: list[int] = []
    responses: list[int] = []
    stop_t: int | None = None

    for t in range(int(max_steps)):
        cand = _candidate_mask_exact(
            tables=tables,
            base_obs=int(base_obs),
            actions=list(actions),
            responses=list(responses),
            stop_action=int(stop_action),
        )
        if int(_sigma_ambiguity_exact(sigma=sigma, cand_mask=cand)) == 1:
            stop_t = int(t)
            actions.append(int(stop_action))
            responses.append(0)
            for _ in range(int(t) + 1, int(max_steps)):
                actions.append(int(stop_action))
                responses.append(0)
            break

        allowed = oracle_allowed_actions(
            tables=tables,
            sigma=sigma,
            base_obs=int(base_obs),
            actions_prefix=list(actions),
            responses_prefix=list(responses),
            remaining_steps=int(max_steps) - int(t),
            cfg=cfg,
        )
        # Prefer a query (non-STOP) action; STOP is emitted only via the exact closure check above.
        a = next((int(a0) for a0 in allowed if int(a0) != int(stop_action)), int(allowed[0]))
        actions.append(int(a))
        responses.append(int(tables[int(a), int(x)].item()))

    if stop_t is None:
        t_stop = _first_stop_t(actions=actions, stop_action=int(stop_action), max_steps=int(max_steps))
        cand = _candidate_mask_exact(
            tables=tables,
            base_obs=int(base_obs),
            actions=actions[:t_stop],
            responses=responses[:t_stop],
            stop_action=int(stop_action),
        )
        if int(_sigma_ambiguity_exact(sigma=sigma, cand_mask=cand)) == 1:
            stop_t = int(t_stop)

    if stop_t is not None:
        cand = _candidate_mask_exact(
            tables=tables,
            base_obs=int(base_obs),
            actions=actions[: int(stop_t)],
            responses=responses[: int(stop_t)],
            stop_action=int(stop_action),
        )
        y_pred = int(_sigma_star_exact(sigma=sigma, cand_mask=cand))
    else:
        # Not expected in well-formed episodes, but keep a total function.
        y_pred = 0

    return [int(a) for a in actions], [int(r) for r in responses], int(y_pred)


def _write_jsonl(path: Path, recs: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        for rec in recs:
            f.write(json.dumps(rec, sort_keys=True) + "\n")


def main() -> None:
    p = argparse.ArgumentParser(
        description="Produce episode-level structural certificates for v19 universal v5.1 (exact STOP + exact readout)."
    )
    p.add_argument("--out-jsonl", type=str, required=True)
    p.add_argument("--split", choices=["iid", "ood"], required=True)
    p.add_argument("--episodes", type=int, default=1024)
    p.add_argument("--seed-base", type=int, default=0)
    p.add_argument("--n-states", type=int, required=True)
    p.add_argument("--n-views", type=int, default=8)
    p.add_argument("--y-classes", type=int, default=2)
    p.add_argument("--obs-vocab", type=int, default=16)
    p.add_argument("--max-steps", type=int, default=3)
    p.add_argument("--policy", choices=["oracle", "model_exact"], default="oracle")
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--model-state-dict", type=str, default="")
    p.add_argument("--forbid-view0", action="store_true")
    p.add_argument("--forbid-repeats", action="store_true")
    args = p.parse_args()

    out_jsonl = Path(args.out_jsonl)
    split = str(args.split)
    ood = split == "ood"

    verify_path = HERE / "verify_struct_aslmt_v19_algebra_universal_v5_1.py"

    run_meta = {
        "run_tag": f"aslmt_struct_cert_v5_1_exact_{split}",
        "timestamp": _now_ts(),
        "sha256": {
            "certify_script": _sha256_file(Path(__file__).resolve()),
            "verify_script": _sha256_file(verify_path) if verify_path.exists() else "",
            "env_script": _sha256_file(HERE / "aslmt_env_v19_algebra_universal_v5_1.py"),
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
            "forbid_view0": bool(args.forbid_view0),
            "forbid_repeats": bool(args.forbid_repeats),
        },
    }

    modelA: V19AlgebraUniversalModelA_ActionZ | None = None
    if str(args.policy) == "model_exact":
        if not str(args.model_state_dict):
            raise SystemExit("--model-state-dict is required for --policy model_exact")
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
            actions, responses, y_pred = _run_oracle_policy_exact(
                tables=tables,
                sigma=sigma,
                x=int(x),
                base_obs=int(base_obs),
                max_steps=int(max_steps),
                forbid_view0=bool(args.forbid_view0),
            )
        else:
            assert modelA is not None
            actions, responses, y_pred = _run_model_policy_exact(
                modelA=modelA,
                tables=tables,
                sigma=sigma,
                x=int(x),
                base_obs=int(base_obs),
                max_steps=int(max_steps),
                device=str(args.device),
                forbid_view0=bool(args.forbid_view0),
                forbid_repeats=bool(args.forbid_repeats),
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
