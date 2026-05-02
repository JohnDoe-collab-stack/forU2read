import argparse
import json
from dataclasses import dataclass
from pathlib import Path

import torch

from aslmt_model_v20_algebra_v3b_query_zread import V20AlgebraV3bQueryModelA_ZRead
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


def _add_xy(x: torch.Tensor) -> torch.Tensor:
    B, C, H, W = x.shape
    if int(C) != 1:
        raise ValueError(f"_add_xy expects C==1, got shape={tuple(x.shape)}")
    ys = torch.linspace(-1.0, 1.0, steps=int(H), device=x.device, dtype=x.dtype)
    xs = torch.linspace(-1.0, 1.0, steps=int(W), device=x.device, dtype=x.dtype)
    yv = ys[:, None].expand(int(H), int(W))
    xv = xs[None, :].expand(int(H), int(W))
    xy = torch.stack([xv, yv], dim=0).unsqueeze(0).expand(int(B), 2, int(H), int(W))
    return torch.cat([x, xy], dim=1)


def _overlap_score(pred_logits: torch.Tensor, true_mask: torch.Tensor) -> torch.Tensor:
    return (torch.sigmoid(pred_logits) * true_mask).sum(dim=(1, 2, 3))


def _load_modelA_from_ckpt(*, ckpt_path: Path, device: str) -> V20AlgebraV3bQueryModelA_ZRead:
    ckpt = torch.load(str(ckpt_path), map_location=str(device))
    z_classes = int(ckpt.get("z_classes", 0))
    if z_classes <= 0:
        raise ValueError("invalid ckpt: missing z_classes")
    sd = ckpt.get("modelA_state_dict", None)
    if not isinstance(sd, dict):
        raise ValueError("invalid ckpt: missing modelA_state_dict")
    modelA = V20AlgebraV3bQueryModelA_ZRead(z_classes=z_classes).to(str(device))
    modelA.load_state_dict(sd)
    modelA.eval()
    return modelA


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


def _check_collision_forced_fail(
    *,
    modelA: V20AlgebraV3bQueryModelA_ZRead,
    device: torch.device,
    ctx: Ctx,
    h0: int,
    h1: int,
    z: int,
    k_fixed: int,
    n_classes: int,
) -> tuple[bool, dict]:
    ex0 = render(ctx, h=int(h0), k=int(k_fixed), n_classes=int(n_classes))
    ex1 = render(ctx, h=int(h1), k=int(k_fixed), n_classes=int(n_classes))
    cue0 = _add_xy(ex0["cue_image"].unsqueeze(0).to(device))
    cue1 = _add_xy(ex1["cue_image"].unsqueeze(0).to(device))
    img = _add_xy(ex0["image"].unsqueeze(0).to(device))
    t0 = ex0["hidden_target"].unsqueeze(0).to(device)
    t1 = ex1["hidden_target"].unsqueeze(0).to(device)

    with torch.no_grad():
        zl0 = modelA.z_logits(cue0)
        zl1 = modelA.z_logits(cue1)
    z0 = int(torch.argmax(zl0, dim=-1).item())
    z1 = int(torch.argmax(zl1, dim=-1).item())
    z_ok = (int(z0) == int(z1) == int(z))

    k = torch.tensor([int(k_fixed)], device=device, dtype=torch.long)
    with torch.no_grad():
        p0 = modelA.forward_with_res_bit(cue0, img, res_bit=k)
        p1 = modelA.forward_with_res_bit(cue1, img, res_bit=k)

    same_pred = bool(torch.allclose(p0, p1))
    s00 = float(_overlap_score(p0, t0).item())
    s01 = float(_overlap_score(p0, t1).item())
    s10 = float(_overlap_score(p1, t0).item())
    s11 = float(_overlap_score(p1, t1).item())
    side0_correct = bool(s00 > s01)
    side1_correct = bool(s11 > s10)
    forced_fail = bool(same_pred and not (side0_correct and side1_correct))

    payload = {
        "ctx": {
            "cx": int(ctx.cx),
            "cy": int(ctx.cy),
            "t": int(ctx.t),
            "occ_half": int(ctx.occ_half),
            "img_size": int(ctx.img_size),
            "ood": bool(ctx.ood),
            "seed": int(ctx.seed),
        },
        "collision": {"h0": int(h0), "h1": int(h1), "z": int(z), "k_fixed": int(k_fixed), "z0": int(z0), "z1": int(z1)},
        "check": {
            "z_ok": bool(z_ok),
            "same_pred": bool(same_pred),
            "forced_fail": bool(forced_fail),
            "scores": {"s00": s00, "s01": s01, "s10": s10, "s11": s11},
        },
    }
    ok = bool(z_ok and forced_fail)
    return ok, payload


def verify_certificates(
    *, cert_jsonl: Path, ckpt: Path, device: str, expect_lines: int | None = None
) -> tuple[dict, list[Violation]]:
    recs = _read_jsonl(cert_jsonl)
    violations: list[Violation] = []

    if expect_lines is not None and int(len(recs)) != int(expect_lines):
        violations.append(
            Violation(episode_id=-1, prop="P0", detail=f"expected {int(expect_lines)} lines, got {int(len(recs))}", ctx_i=-1, payload={})
        )

    modelA = _load_modelA_from_ckpt(ckpt_path=ckpt, device=str(device))
    dev = torch.device(str(device))

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

        res = r.get("result", {})
        vios = (res.get("violations", []) if isinstance(res, dict) else [])
        if not isinstance(vios, list):
            violations.append(Violation(episode_id=ep_id, prop="P0", detail="result.violations missing/not list", ctx_i=-1, payload={}))
            continue

        for v in vios:
            prop = str(v.get("prop", ""))
            if prop != "minproof_z_collision_forced_fail":
                violations.append(
                    Violation(episode_id=ep_id, prop="P0", detail=f"unknown prop in cert: {prop!r}", ctx_i=int(v.get("ctx_i", -1)), payload={})
                )
                total_vios += 1
                props_count["P0"] = int(props_count.get("P0", 0)) + 1
                continue

            ctx_i = int(v.get("ctx_i", -1))
            payload = v.get("payload", {})
            if not isinstance(payload, dict):
                violations.append(Violation(episode_id=ep_id, prop="P0", detail="malformed payload (not dict)", ctx_i=int(ctx_i), payload={}))
                total_vios += 1
                props_count["P0"] = int(props_count.get("P0", 0)) + 1
                continue

            ctx_json = payload.get("ctx", {})
            coll_json = payload.get("collision", {})
            if not isinstance(ctx_json, dict) or not isinstance(coll_json, dict):
                violations.append(Violation(episode_id=ep_id, prop="P0", detail="payload.ctx/collision missing/not dict", ctx_i=int(ctx_i), payload=payload))
                total_vios += 1
                props_count["P0"] = int(props_count.get("P0", 0)) + 1
                continue

            ctx = _ctx_from_json(ctx_json)
            ok, recomputed = _check_collision_forced_fail(
                modelA=modelA,
                device=dev,
                ctx=ctx,
                h0=int(coll_json.get("h0", -1)),
                h1=int(coll_json.get("h1", -1)),
                z=int(coll_json.get("z", -1)),
                k_fixed=int(coll_json.get("k_fixed", -1)),
                n_classes=int(n_classes),
            )
            if not ok:
                violations.append(
                    Violation(
                        episode_id=ep_id,
                        prop="minproof_bad_witness",
                        detail="certified witness did not re-verify as a collision+forced-fail",
                        ctx_i=int(ctx_i),
                        payload=recomputed,
                    )
                )
                props_count["minproof_bad_witness"] = int(props_count.get("minproof_bad_witness", 0)) + 1
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
    p = argparse.ArgumentParser(description="Verifier for v20 algebra v3b minproof certificates.")
    p.add_argument("--cert-jsonl", type=str, required=True)
    p.add_argument("--ckpt", type=str, required=True)
    p.add_argument("--device", type=str, default="cpu")
    p.add_argument("--expect-lines", type=int, default=0)
    p.add_argument("--out-report-json", type=str, default="")
    p.add_argument("--out-report-txt", type=str, default="")
    p.add_argument("--out-violations-jsonl", type=str, default="")
    args = p.parse_args()

    report, violations = verify_certificates(
        cert_jsonl=Path(args.cert_jsonl),
        ckpt=Path(args.ckpt).expanduser().resolve(),
        device=str(args.device),
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

