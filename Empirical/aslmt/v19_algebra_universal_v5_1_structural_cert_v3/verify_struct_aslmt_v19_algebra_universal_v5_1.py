import argparse
import json
from dataclasses import dataclass
from pathlib import Path

import torch


@dataclass(frozen=True)
class Violation:
    episode_id: int
    prop: str
    detail: str
    t_stop: int
    amb_trace: list[int]
    cand_sizes: list[int]
    actions: list[int]
    responses: list[int]


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


def _first_stop_t(*, actions: list[int], stop_action: int, max_steps: int) -> int:
    for t in range(int(max_steps)):
        if int(actions[t]) == int(stop_action):
            return int(t)
    return int(max_steps)


def _amb_trace(
    *,
    tables: torch.Tensor,
    sigma: torch.Tensor,
    base_obs: int,
    actions: list[int],
    responses: list[int],
    stop_action: int,
    max_steps: int,
) -> tuple[list[int], list[int]]:
    amb: list[int] = []
    sizes: list[int] = []
    actions_prefix: list[int] = []
    responses_prefix: list[int] = []

    cand0 = _candidate_mask_exact(
        tables=tables,
        base_obs=int(base_obs),
        actions=[],
        responses=[],
        stop_action=int(stop_action),
    )
    amb.append(int(_sigma_ambiguity_exact(sigma=sigma, cand_mask=cand0)))
    sizes.append(int(cand0.sum().item()))

    for t in range(int(max_steps)):
        a = int(actions[t])
        r = int(responses[t])
        if int(a) != int(stop_action):
            actions_prefix.append(int(a))
            responses_prefix.append(int(r))
        cand = _candidate_mask_exact(
            tables=tables,
            base_obs=int(base_obs),
            actions=actions_prefix,
            responses=responses_prefix,
            stop_action=int(stop_action),
        )
        amb.append(int(_sigma_ambiguity_exact(sigma=sigma, cand_mask=cand)))
        sizes.append(int(cand.sum().item()))
    return amb, sizes


def _check_P1_legality(
    *,
    actions: list[int],
    V: int,
    stop_action: int,
    forbid_view0: bool,
    forbid_repeats: bool,
) -> str | None:
    seen: set[int] = set()
    stopped = False
    for t, a in enumerate(actions):
        a = int(a)
        if stopped:
            if a != int(stop_action):
                return f"STOP persistence violated at t={t}"
            continue
        if a == int(stop_action):
            stopped = True
            continue
        if forbid_view0 and a == 0:
            return f"view0 forbidden but used at t={t}"
        if a < 0 or a >= int(V):
            return f"invalid view id a={a} at t={t} for V={V}"
        if forbid_repeats:
            if a in seen:
                return f"repeated view a={a}"
            seen.add(int(a))
    return None


def verify_certificates(
    *,
    cert_jsonl: Path,
    expect_lines: int | None,
    forbid_view0: bool,
    forbid_repeats: bool,
) -> tuple[dict, list[Violation]]:
    violations: list[Violation] = []
    n_lines = 0

    with open(cert_jsonl, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            n_lines += 1
            rec = json.loads(line)
            ep_id = int(rec["episode_id"])
            ep = rec["episode"]
            agent = rec["agent"]

            tables = torch.tensor(ep["tables"], dtype=torch.long)
            sigma = torch.tensor(ep["sigma"], dtype=torch.long)
            x = int(ep["x"])
            base_obs = int(ep["base_obs"])
            max_steps = int(ep["max_steps"])
            stop_action = int(ep["stop_action"])
            actions = [int(a) for a in agent["actions"]]
            responses = [int(r) for r in agent["responses"]]
            y_pred = int(agent["y_pred"])

            V, _ = tables.shape
            if int(V) != int(stop_action):
                violations.append(
                    Violation(
                        episode_id=ep_id,
                        prop="P0",
                        detail=f"stop_action mismatch: stop_action={stop_action} but V={V}",
                        t_stop=0,
                        amb_trace=[],
                        cand_sizes=[],
                        actions=actions,
                        responses=responses,
                    )
                )
                continue

            if len(actions) != int(max_steps) or len(responses) != int(max_steps):
                violations.append(
                    Violation(
                        episode_id=ep_id,
                        prop="P0",
                        detail=f"expected length T={max_steps} but got actions={len(actions)} responses={len(responses)}",
                        t_stop=0,
                        amb_trace=[],
                        cand_sizes=[],
                        actions=actions,
                        responses=responses,
                    )
                )
                continue

            err = _check_P1_legality(
                actions=actions,
                V=int(V),
                stop_action=int(stop_action),
                forbid_view0=bool(forbid_view0),
                forbid_repeats=bool(forbid_repeats),
            )
            amb, sizes = _amb_trace(
                tables=tables,
                sigma=sigma,
                base_obs=int(base_obs),
                actions=actions,
                responses=responses,
                stop_action=int(stop_action),
                max_steps=int(max_steps),
            )
            t_stop = _first_stop_t(actions=actions, stop_action=int(stop_action), max_steps=int(max_steps))

            if err is not None:
                violations.append(
                    Violation(
                        episode_id=ep_id,
                        prop="P1",
                        detail=str(err),
                        t_stop=int(t_stop),
                        amb_trace=amb,
                        cand_sizes=sizes,
                        actions=actions,
                        responses=responses,
                    )
                )
                continue

            # P1bis — response fidelity: when a_t != STOP, responses[t] must match tables[a_t, x].
            bad_resp = False
            for t in range(int(max_steps)):
                a = int(actions[t])
                if int(a) == int(stop_action):
                    continue
                expected_r = int(tables[int(a), int(x)].item())
                got_r = int(responses[t])
                if int(got_r) != int(expected_r):
                    violations.append(
                        Violation(
                            episode_id=ep_id,
                            prop="P1bis",
                            detail=f"response mismatch at t={t}: got {got_r} expected {expected_r}",
                            t_stop=int(t_stop),
                            amb_trace=amb,
                            cand_sizes=sizes,
                            actions=actions,
                            responses=responses,
                        )
                    )
                    bad_resp = True
                    break
            if bad_resp:
                continue

            if int(sizes[0]) == 0:
                violations.append(
                    Violation(
                        episode_id=ep_id,
                        prop="P5",
                        detail="empty candidate set at t=0",
                        t_stop=int(t_stop),
                        amb_trace=amb,
                        cand_sizes=sizes,
                        actions=actions,
                        responses=responses,
                    )
                )
                continue

            if int(sizes[t_stop]) == 0:
                violations.append(
                    Violation(
                        episode_id=ep_id,
                        prop="P5",
                        detail=f"empty candidate set at t_stop={t_stop}",
                        t_stop=int(t_stop),
                        amb_trace=amb,
                        cand_sizes=sizes,
                        actions=actions,
                        responses=responses,
                    )
                )
                continue

            for u, v in zip(amb, amb[1:]):
                if int(v) > int(u):
                    violations.append(
                        Violation(
                            episode_id=ep_id,
                            prop="P4",
                            detail=f"ambiguity increased: trace={amb}",
                            t_stop=int(t_stop),
                            amb_trace=amb,
                            cand_sizes=sizes,
                            actions=actions,
                            responses=responses,
                        )
                    )
                    break
            else:
                if int(amb[t_stop]) != 1:
                    violations.append(
                        Violation(
                            episode_id=ep_id,
                            prop="P2",
                            detail=f"Amb at t_stop is {amb[t_stop]} not 1",
                            t_stop=int(t_stop),
                            amb_trace=amb,
                            cand_sizes=sizes,
                            actions=actions,
                            responses=responses,
                        )
                    )
                    continue

                cand = _candidate_mask_exact(
                    tables=tables,
                    base_obs=int(base_obs),
                    actions=actions[:t_stop],
                    responses=responses[:t_stop],
                    stop_action=int(stop_action),
                )
                y_star = _sigma_star_exact(sigma=sigma, cand_mask=cand)
                if int(y_pred) != int(y_star):
                    violations.append(
                        Violation(
                            episode_id=ep_id,
                            prop="P3",
                            detail=f"y_pred={y_pred} but sigma*={y_star}",
                            t_stop=int(t_stop),
                            amb_trace=amb,
                            cand_sizes=sizes,
                            actions=actions,
                            responses=responses,
                        )
                    )

    if expect_lines is not None and int(n_lines) != int(expect_lines):
        violations.append(
            Violation(
                episode_id=-1,
                prop="COVERAGE",
                detail=f"expected {expect_lines} lines but got {n_lines}",
                t_stop=0,
                amb_trace=[],
                cand_sizes=[],
                actions=[],
                responses=[],
            )
        )

    report = {
        "cert_jsonl": str(cert_jsonl),
        "lines": int(n_lines),
        "ok": len(violations) == 0,
        "violations": len(violations),
        "props_count": {
            "P1": sum(1 for v in violations if v.prop == "P1"),
            "P1bis": sum(1 for v in violations if v.prop == "P1bis"),
            "P2": sum(1 for v in violations if v.prop == "P2"),
            "P3": sum(1 for v in violations if v.prop == "P3"),
            "P4": sum(1 for v in violations if v.prop == "P4"),
            "P5": sum(1 for v in violations if v.prop == "P5"),
            "COVERAGE": sum(1 for v in violations if v.prop == "COVERAGE"),
            "P0": sum(1 for v in violations if v.prop == "P0"),
        },
    }
    return report, violations


def _violations_to_jsonable(violations: list[Violation]) -> list[dict]:
    return [
        {
            "episode_id": int(v.episode_id),
            "prop": str(v.prop),
            "detail": str(v.detail),
            "t_stop": int(v.t_stop),
            "amb_trace": [int(x) for x in v.amb_trace],
            "cand_sizes": [int(x) for x in v.cand_sizes],
            "actions": [int(x) for x in v.actions],
            "responses": [int(x) for x in v.responses],
        }
        for v in violations
    ]


def _write_violations_jsonl(path: Path, violations: list[Violation]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        for v in _violations_to_jsonable(violations):
            f.write(json.dumps(v, sort_keys=True) + "\n")


def main() -> None:
    p = argparse.ArgumentParser(description="Structural verifier for v19 universal v5.1 certificates.")
    p.add_argument("--cert-jsonl", type=str, required=True)
    p.add_argument("--expect-lines", type=int, default=0)
    p.add_argument("--forbid-view0", action="store_true")
    p.add_argument("--forbid-repeats", action="store_true")
    p.add_argument("--out-report-json", type=str, default="")
    p.add_argument("--out-report-txt", type=str, default="")
    p.add_argument(
        "--out-violations-jsonl",
        type=str,
        default="",
        help="Optional: write one JSON record per violation (exhaustive).",
    )
    args = p.parse_args()

    report, violations = verify_certificates(
        cert_jsonl=Path(args.cert_jsonl),
        expect_lines=(int(args.expect_lines) if int(args.expect_lines) > 0 else None),
        forbid_view0=bool(args.forbid_view0),
        forbid_repeats=bool(args.forbid_repeats),
    )

    # Always prepare an exhaustive, machine-readable list (optionally written to disk).
    violations_list = _violations_to_jsonable(violations)

    if str(args.out_report_json):
        report_full = dict(report)
        report_full["violations_list"] = violations_list
        Path(args.out_report_json).write_text(
            json.dumps(report_full, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    if str(args.out_report_txt):
        lines = [
            f"ok={report['ok']}",
            f"lines={report['lines']}",
            f"violations={report['violations']}",
            f"props_count={json.dumps(report['props_count'], sort_keys=True)}",
        ]
        if violations:
            v0 = violations[0]
            lines.append(f"first_violation={v0.prop} ep={v0.episode_id} detail={v0.detail}")
            lines.append(f"t_stop={v0.t_stop} amb_trace={v0.amb_trace} cand_sizes={v0.cand_sizes}")
        Path(args.out_report_txt).write_text("\n".join(lines) + "\n", encoding="utf-8")

    if str(args.out_violations_jsonl):
        _write_violations_jsonl(Path(args.out_violations_jsonl), violations)

    # Print a compact summary to stdout (avoid dumping large violation arrays).
    print(json.dumps(report, indent=2, sort_keys=True))
    if not report["ok"]:
        raise SystemExit(2)


if __name__ == "__main__":
    main()
