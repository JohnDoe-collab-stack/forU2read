import argparse
import json
from dataclasses import dataclass
from pathlib import Path

import torch

from render_aslmt_v20_algebra_v3b_paired_ctx_nscalable_spaced2_64 import Ctx, render


@dataclass(frozen=True)
class Violation:
    episode_id: int
    prop: str
    detail: str
    ctx_i: int
    payload: dict


def _read_jsonl(path: Path) -> list[dict]:
    out: list[dict] = []
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            out.append(json.loads(line))
    return out


def _ctx_from_json(d: dict) -> Ctx:
    return Ctx(
        cx=int(d["cx"]),
        cy=int(d["cy"]),
        t=int(d["t"]),
        occ_half=int(d["occ_half"]),
        img_size=int(d["img_size"]),
        ood=bool(d["ood"]),
        seed=int(d["seed"]),
    )


def verify_certificates(*, cert_jsonl: Path, expect_lines: int | None = None) -> tuple[dict, list[Violation]]:
    recs = _read_jsonl(cert_jsonl)
    violations: list[Violation] = []

    if expect_lines is not None and int(len(recs)) != int(expect_lines):
        violations.append(
            Violation(episode_id=-1, prop="P0", detail=f"expected {int(expect_lines)} lines, got {int(len(recs))}", ctx_i=-1, payload={})
        )

    props_count: dict[str, int] = {}
    total_vios = 0

    for r in recs:
        ep_id = int(r.get("episode_id", -1))
        run_meta = r.get("run_meta", {})
        cfg = run_meta.get("config", {}) if isinstance(run_meta, dict) else {}
        n_classes = int(cfg.get("n_classes", 0)) if isinstance(cfg, dict) else 0
        if n_classes <= 0:
            violations.append(Violation(episode_id=ep_id, prop="P0", detail="missing n_classes in run_meta.config", ctx_i=-1, payload={}))
            continue

        ep = r.get("episode", {})
        ctxs_json = ep.get("ctxs", [])
        if not isinstance(ctxs_json, list):
            violations.append(Violation(episode_id=ep_id, prop="P0", detail="episode.ctxs missing/not list", ctx_i=-1, payload={}))
            continue

        # Re-run the two marginal no-go checks for each ctx, independent of the certificate content.
        for ctx_i, cjson in enumerate(ctxs_json):
            if not isinstance(cjson, dict):
                violations.append(Violation(episode_id=ep_id, prop="P0", detail="malformed ctx entry (not dict)", ctx_i=int(ctx_i), payload={}))
                total_vios += 1
                props_count["P0"] = int(props_count.get("P0", 0)) + 1
                continue
            ctx = _ctx_from_json(cjson)

            k_fixed = int(ctx.seed & 1)
            h0 = int(ctx.seed % int(n_classes))
            h1 = int((h0 + 1) % int(n_classes))
            ex0 = render(ctx, h=int(h0), k=int(k_fixed), n_classes=int(n_classes))
            ex1 = render(ctx, h=int(h1), k=int(k_fixed), n_classes=int(n_classes))
            if not (torch.allclose(ex0["image"], ex1["image"]) and (not torch.allclose(ex0["hidden_target"], ex1["hidden_target"]))):
                violations.append(
                    Violation(
                        episode_id=int(ep_id),
                        prop="marginal_image_nogo_failed",
                        detail="expected same image but different hidden_target when varying h under fixed k",
                        ctx_i=int(ctx_i),
                        payload={"ctx": cjson, "h0": int(h0), "h1": int(h1), "k_fixed": int(k_fixed)},
                    )
                )
                props_count["marginal_image_nogo_failed"] = int(props_count.get("marginal_image_nogo_failed", 0)) + 1
                total_vios += 1

            h_fixed = int((ctx.seed * 3 + 1) % int(n_classes))
            cu0 = render(ctx, h=int(h_fixed), k=0, n_classes=int(n_classes))
            cu1 = render(ctx, h=int(h_fixed), k=1, n_classes=int(n_classes))
            if not (torch.allclose(cu0["cue_image"], cu1["cue_image"]) and (not torch.allclose(cu0["hidden_target"], cu1["hidden_target"]))):
                violations.append(
                    Violation(
                        episode_id=int(ep_id),
                        prop="marginal_cue_nogo_failed",
                        detail="expected same cue but different hidden_target when varying k under fixed h",
                        ctx_i=int(ctx_i),
                        payload={"ctx": cjson, "h_fixed": int(h_fixed)},
                    )
                )
                props_count["marginal_cue_nogo_failed"] = int(props_count.get("marginal_cue_nogo_failed", 0)) + 1
                total_vios += 1

        # Also accept and count any explicit violations stored in the certificate.
        res = r.get("result", {})
        vios = (res.get("violations", []) if isinstance(res, dict) else [])
        if isinstance(vios, list) and len(vios) > 0:
            for v in vios:
                prop = str(v.get("prop", ""))
                violations.append(Violation(episode_id=int(ep_id), prop=prop, detail=str(v.get("detail", "")), ctx_i=int(v.get("ctx_i", -1)), payload=v.get("payload", {})))
                props_count[prop] = int(props_count.get(prop, 0)) + 1
                total_vios += 1

    ok = (total_vios == 0) and all(v.prop != "P0" for v in violations)
    if any(v.prop == "P0" for v in violations):
        ok = False

    report = {
        "ok": bool(ok),
        "lines": int(len(recs)),
        "violations": int(total_vios),
        "props_count": {k: int(v) for (k, v) in sorted(props_count.items())},
    }
    return report, violations


def _violations_to_jsonable(violations: list[Violation]) -> list[dict]:
    out: list[dict] = []
    for v in violations:
        out.append(
            {
                "episode_id": int(v.episode_id),
                "prop": str(v.prop),
                "detail": str(v.detail),
                "ctx_i": int(v.ctx_i),
                "payload": (v.payload if isinstance(v.payload, dict) else {}),
            }
        )
    return out


def _write_violations_jsonl(path: Path, violations: list[Violation]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        for v in _violations_to_jsonable(violations):
            f.write(json.dumps(v, sort_keys=True) + "\n")


def main() -> None:
    p = argparse.ArgumentParser(description="Verifier for v20 algebra v3b marginal no-go certificates.")
    p.add_argument("--cert-jsonl", type=str, required=True)
    p.add_argument("--expect-lines", type=int, default=0)
    p.add_argument("--out-report-json", type=str, default="")
    p.add_argument("--out-report-txt", type=str, default="")
    p.add_argument("--out-violations-jsonl", type=str, default="")
    args = p.parse_args()

    report, violations = verify_certificates(
        cert_jsonl=Path(args.cert_jsonl),
        expect_lines=(int(args.expect_lines) if int(args.expect_lines) > 0 else None),
    )

    violations_list = _violations_to_jsonable(violations)
    if str(args.out_report_json):
        report_full = dict(report)
        report_full["violations_list"] = violations_list
        Path(args.out_report_json).write_text(json.dumps(report_full, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if str(args.out_report_txt):
        Path(args.out_report_txt).write_text(
            "\n".join(
                [
                    f"ok={report['ok']}",
                    f"lines={report['lines']}",
                    f"violations={report['violations']}",
                    f"props_count={json.dumps(report['props_count'], sort_keys=True)}",
                ]
            )
            + "\n",
            encoding="utf-8",
        )
    if str(args.out_violations_jsonl):
        _write_violations_jsonl(Path(args.out_violations_jsonl), violations)
    if not bool(report["ok"]):
        raise SystemExit(1)


if __name__ == "__main__":
    main()

