import argparse
import json
from dataclasses import dataclass
from pathlib import Path

import torch

from aslmt_model_v20_algebra_v3b_query_zread import (
    V20AlgebraV3bCueOnlyBaseline,
    V20AlgebraV3bImageOnlyBaseline,
    V20AlgebraV3bQueryModelA_ZRead,
)
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


def _policy_action_from_h(h: torch.Tensor) -> torch.Tensor:
    x = h.to(torch.long) & 0xFFFFFFFF
    x = x ^ ((x << 13) & 0xFFFFFFFF)
    x = x ^ (x >> 17)
    x = x ^ ((x << 5) & 0xFFFFFFFF)
    return (x & 1).to(torch.long)


def _env_res_bit(*, h: torch.Tensor, k: torch.Tensor, action: torch.Tensor) -> torch.Tensor:
    a = action.to(torch.long)
    kk = k.to(torch.long)
    h2 = _policy_action_from_h(h)
    correct = (a == h2).to(torch.long)
    return kk * correct


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


def _load_models_from_ckpt(
    *, ckpt_path: Path, device: str
) -> tuple[V20AlgebraV3bQueryModelA_ZRead, V20AlgebraV3bImageOnlyBaseline, V20AlgebraV3bCueOnlyBaseline]:
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

    sd_img = ckpt.get("modelB_img_state_dict", None)
    if not isinstance(sd_img, dict):
        raise ValueError("invalid v6 ckpt: missing trained modelB_img_state_dict")
    modelB_img = V20AlgebraV3bImageOnlyBaseline().to(str(device))
    modelB_img.load_state_dict(sd_img)
    modelB_img.eval()

    sd_cue = ckpt.get("modelB_cue_state_dict", None)
    if not isinstance(sd_cue, dict):
        raise ValueError("invalid v6 ckpt: missing trained modelB_cue_state_dict")
    modelB_cue = V20AlgebraV3bCueOnlyBaseline().to(str(device))
    modelB_cue.load_state_dict(sd_cue)
    modelB_cue.eval()

    return modelA, modelB_img, modelB_cue


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


def _check_one_ctx(
    *,
    modelA: V20AlgebraV3bQueryModelA_ZRead,
    modelB_img: V20AlgebraV3bImageOnlyBaseline,
    modelB_cue: V20AlgebraV3bCueOnlyBaseline,
    device: torch.device,
    ctx: Ctx,
    n_classes: int,
) -> list[tuple[str, str, dict]]:
    """
    Recompute the structural checks for a single context.
    Returns list of (prop, detail, payload).
    """
    n_classes = int(n_classes)
    h0 = int(ctx.seed % n_classes)
    h1 = int((h0 + 1) % n_classes)
    k_fixed = int(ctx.seed & 1)
    h_fixed = int((ctx.seed * 3 + 1) % n_classes)

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
        "image_gate": {"h0": int(h0), "h1": int(h1), "k": int(k_fixed)},
        "cue_gate": {"h": int(h_fixed), "k0": 0, "k1": 1},
    }

    fails: list[tuple[str, str, dict]] = []

    ex_im0 = render(ctx, h=int(h0), k=int(k_fixed), n_classes=n_classes)
    ex_im1 = render(ctx, h=int(h1), k=int(k_fixed), n_classes=n_classes)
    if not torch.allclose(ex_im0["image"], ex_im1["image"]):
        fails.append(("barrier_image", "image depends on h under fixed k", payload))

    ex_cu0 = render(ctx, h=int(h_fixed), k=0, n_classes=n_classes)
    ex_cu1 = render(ctx, h=int(h_fixed), k=1, n_classes=n_classes)
    if not torch.allclose(ex_cu0["cue_image"], ex_cu1["cue_image"]):
        fails.append(("barrier_cue", "cue depends on k under fixed h", payload))

    cue_im0 = _add_xy(ex_im0["cue_image"].unsqueeze(0).to(device))
    cue_im1 = _add_xy(ex_im1["cue_image"].unsqueeze(0).to(device))
    image_fixed = _add_xy(ex_im0["image"].unsqueeze(0).to(device))
    t_im0 = ex_im0["hidden_target"].unsqueeze(0).to(device)
    t_im1 = ex_im1["hidden_target"].unsqueeze(0).to(device)
    h_im0 = ex_im0["h"].unsqueeze(0).to(device)
    h_im1 = ex_im1["h"].unsqueeze(0).to(device)
    k_im0 = ex_im0["k"].unsqueeze(0).to(device)
    k_im1 = ex_im1["k"].unsqueeze(0).to(device)

    with torch.no_grad():
        act_im0 = modelA.chosen_action(cue_im0)
        act_im1 = modelA.chosen_action(cue_im1)
        res_im0 = _env_res_bit(h=h_im0, k=k_im0, action=act_im0)
        res_im1 = _env_res_bit(h=h_im1, k=k_im1, action=act_im1)
        pA_im0 = modelA.forward_with_res_bit(cue_im0, image_fixed, res_bit=res_im0)
        pA_im1 = modelA.forward_with_res_bit(cue_im1, image_fixed, res_bit=res_im1)

    A_im0_correct = bool(_overlap_score(pA_im0, t_im0) > _overlap_score(pA_im0, t_im1))
    A_im1_correct = bool(_overlap_score(pA_im1, t_im1) > _overlap_score(pA_im1, t_im0))
    if not (A_im0_correct and A_im1_correct):
        fails.append(("image_gate", "modelA failed image-gate pair discrimination", payload))

    cue_fixed = _add_xy(ex_cu0["cue_image"].unsqueeze(0).to(device))
    img0 = _add_xy(ex_cu0["image"].unsqueeze(0).to(device))
    img1 = _add_xy(ex_cu1["image"].unsqueeze(0).to(device))
    t_cu0 = ex_cu0["hidden_target"].unsqueeze(0).to(device)
    t_cu1 = ex_cu1["hidden_target"].unsqueeze(0).to(device)
    h0t = ex_cu0["h"].unsqueeze(0).to(device)
    k0t = ex_cu0["k"].unsqueeze(0).to(device)
    k1t = ex_cu1["k"].unsqueeze(0).to(device)
    with torch.no_grad():
        act0 = modelA.chosen_action(cue_fixed)
        res0 = _env_res_bit(h=h0t, k=k0t, action=act0)
        res1 = _env_res_bit(h=h0t, k=k1t, action=act0)
        pA0 = modelA.forward_with_res_bit(cue_fixed, img0, res_bit=res0)
        pA1 = modelA.forward_with_res_bit(cue_fixed, img1, res_bit=res1)
    A_cu0_correct = bool(_overlap_score(pA0, t_cu0) > _overlap_score(pA0, t_cu1))
    A_cu1_correct = bool(_overlap_score(pA1, t_cu1) > _overlap_score(pA1, t_cu0))
    if not (A_cu0_correct and A_cu1_correct):
        fails.append(("cue_gate", "modelA failed cue-gate pair discrimination", payload))

    with torch.no_grad():
        pB_im0 = modelB_img(image_fixed)
        pB_im1 = modelB_img(image_fixed)
    B_img_both = bool(_overlap_score(pB_im0, t_im0) > _overlap_score(pB_im0, t_im1)) and bool(
        _overlap_score(pB_im1, t_im1) > _overlap_score(pB_im1, t_im0)
    )
    if B_img_both:
        fails.append(("baseline_image", "image-only baseline succeeded (should be impossible)", payload))

    with torch.no_grad():
        pB0 = modelB_cue(cue_fixed)
        pB1 = modelB_cue(cue_fixed)
    B_cue_both = bool(_overlap_score(pB0, t_cu0) > _overlap_score(pB0, t_cu1)) and bool(
        _overlap_score(pB1, t_cu1) > _overlap_score(pB1, t_cu0)
    )
    if B_cue_both:
        fails.append(("baseline_cue", "cue-only baseline succeeded (should be impossible)", payload))

    with torch.no_grad():
        pA_im0_abl = modelA.ablated_forward_with_res_bit(cue_im0, image_fixed, res_bit=res_im0)
        pA_im1_abl = modelA.ablated_forward_with_res_bit(cue_im1, image_fixed, res_bit=res_im1)
    A_abl_both = bool(_overlap_score(pA_im0_abl, t_im0) > _overlap_score(pA_im0_abl, t_im1)) and bool(
        _overlap_score(pA_im1_abl, t_im1) > _overlap_score(pA_im1_abl, t_im0)
    )
    if A_abl_both:
        fails.append(("ablation_z", "z-ablated model still succeeded (should fail)", payload))

    cue_pair = torch.cat([cue_im0, cue_im1], dim=0)
    img_pair = torch.cat([image_fixed, image_fixed], dim=0)
    res_pair = torch.cat([res_im0, res_im1], dim=0)
    perm = torch.tensor([1, 0], device=device, dtype=torch.long)
    with torch.no_grad():
        pA_pair_swap = modelA.swap_forward_with_res_bit(cue_pair, img_pair, res_bit=res_pair, perm=perm)
    pA_im0_swap = pA_pair_swap[0:1]
    pA_im1_swap = pA_pair_swap[1:2]

    A_im0_swap_follow = bool(_overlap_score(pA_im0_swap, t_im1) > _overlap_score(pA_im0_swap, t_im0))
    A_im1_swap_follow = bool(_overlap_score(pA_im1_swap, t_im0) > _overlap_score(pA_im1_swap, t_im1))
    if not (A_im0_swap_follow and A_im1_swap_follow):
        fails.append(("swap_follow", "swap(z) did not follow as expected", payload))

    A_im0_swap_orig = bool(_overlap_score(pA_im0_swap, t_im0) > _overlap_score(pA_im0_swap, t_im1))
    A_im1_swap_orig = bool(_overlap_score(pA_im1_swap, t_im1) > _overlap_score(pA_im1_swap, t_im0))
    if A_im0_swap_orig and A_im1_swap_orig:
        fails.append(("swap_orig", "swap(z) still matched original targets (should not)", payload))

    return fails


def verify_certificates(
    *, cert_jsonl: Path, ckpt: Path, device: str, expect_lines: int | None = None
) -> tuple[dict, list[Violation]]:
    recs = _read_jsonl(cert_jsonl)
    violations: list[Violation] = []

    if expect_lines is not None and int(len(recs)) != int(expect_lines):
        violations.append(Violation(episode_id=-1, prop="P0", detail=f"expected {int(expect_lines)} lines, got {int(len(recs))}", ctx_i=-1, payload={}))

    modelA, modelB_img, modelB_cue = _load_models_from_ckpt(ckpt_path=ckpt, device=str(device))
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

        for ctx_i, cjson in enumerate(ctxs_json):
            if not isinstance(cjson, dict):
                violations.append(Violation(episode_id=ep_id, prop="P0", detail="malformed ctx entry (not dict)", ctx_i=int(ctx_i), payload={}))
                total_vios += 1
                continue
            ctx = _ctx_from_json(cjson)
            fails = _check_one_ctx(
                modelA=modelA, modelB_img=modelB_img, modelB_cue=modelB_cue, device=dev, ctx=ctx, n_classes=int(n_classes)
            )
            for prop, detail, payload in fails:
                violations.append(Violation(episode_id=int(ep_id), prop=str(prop), detail=str(detail), ctx_i=int(ctx_i), payload=payload))
                props_count[str(prop)] = int(props_count.get(str(prop), 0)) + 1
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
    p = argparse.ArgumentParser(description="Verifier for v20 algebra v3b proofpack (independent re-run; zero counterexamples).")
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
        Path(args.out_report_json).write_text(
            json.dumps(report_full, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
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
