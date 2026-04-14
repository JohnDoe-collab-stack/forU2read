import argparse
import hashlib
import json
import os
from dataclasses import asdict, dataclass
from datetime import datetime
from pathlib import Path
from typing import Any

import torch


@dataclass(frozen=True)
class Ctx:
    cx: int
    cy: int
    t: int
    occ_half: int
    img_size: int = 32
    ood: bool = False
    seed: int = 0


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _draw_rect(mask: torch.Tensor, x0: int, y0: int, x1: int, y1: int, img_size: int, value: float = 1.0) -> None:
    x0 = max(0, min(img_size, x0))
    x1 = max(0, min(img_size, x1))
    y0 = max(0, min(img_size, y0))
    y1 = max(0, min(img_size, y1))
    if x1 > x0 and y1 > y0:
        mask[y0:y1, x0:x1] = value


def _draw_hbar(mask: torch.Tensor, cy: int, x0: int, x1: int, thickness: int, img_size: int) -> None:
    _draw_rect(mask, x0, cy - thickness // 2, x1, cy + (thickness + 1) // 2, img_size)


def _draw_vbar(mask: torch.Tensor, cx: int, y0: int, y1: int, thickness: int, img_size: int) -> None:
    _draw_rect(mask, cx - thickness // 2, y0, cx + (thickness + 1) // 2, y1, img_size)


def render(ctx: Ctx, hidden_label: int) -> dict[str, torch.Tensor]:
    H = int(ctx.img_size)
    W = int(ctx.img_size)
    amodal_mask = torch.zeros((H, W), dtype=torch.float32)
    occlusion_mask = torch.zeros((H, W), dtype=torch.float32)

    cx = int(ctx.cx)
    cy = int(ctx.cy)
    t = int(ctx.t)
    occ_half = int(ctx.occ_half)

    # Occluder rectangle.
    ox0, ox1 = cx - occ_half, cx + occ_half
    oy0, oy1 = cy - occ_half, cy + occ_half
    _draw_rect(occlusion_mask, ox0, oy0, ox1, oy1, H, 1.0)

    # Visible scaffold outside the occluder: identical for both classes.
    _draw_vbar(amodal_mask, cx, 0, oy0, t, H)  # top stub
    _draw_vbar(amodal_mask, cx, oy1, H, t, H)  # bottom stub
    _draw_hbar(amodal_mask, cy, 0, ox0, t, H)  # left stub
    _draw_hbar(amodal_mask, cy, ox1, W, t, H)  # right stub

    hidden = torch.zeros_like(amodal_mask)
    inner_margin = 1 if not ctx.ood else 2
    ix0, ix1 = ox0 + inner_margin, ox1 - inner_margin
    iy0, iy1 = oy0 + inner_margin, oy1 - inner_margin

    if int(hidden_label) == 0:
        # PLUS completion (fully inside the occluder).
        _draw_vbar(hidden, cx, oy0, oy1, max(2, t), H)
        _draw_hbar(hidden, cy, ox0, ox1, max(2, t), H)
    else:
        # RING completion (fully inside the occluder).
        _draw_hbar(hidden, iy0 + t // 2, ix0, ix1, t, H)
        _draw_hbar(hidden, iy1 - t // 2, ix0, ix1, t, H)
        _draw_vbar(hidden, ix0 + t // 2, iy0, iy1, t, H)
        _draw_vbar(hidden, ix1 - t // 2, iy0, iy1, t, H)

    amodal_mask = torch.clamp(amodal_mask + hidden, 0.0, 1.0)
    visible_mask = amodal_mask * (1.0 - occlusion_mask)

    # Decision-time observable: scaffold outside occluder + occluder, independent of hidden_label.
    image = torch.clamp(visible_mask + occlusion_mask, 0.0, 1.0)

    # Cue reveals only the hidden completion pattern.
    cue_image = hidden.clone()

    # Hidden-only target (inside occluder region).
    hidden_target = hidden * occlusion_mask

    # Optional deterministic OOD nuisance: flips in cue only.
    if ctx.ood:
        g = torch.Generator()
        g.manual_seed(int(ctx.seed))
        # Deterministic number of flips, matching the v7 env range [10, 20].
        n_flips = int(torch.randint(low=10, high=21, size=(1,), generator=g).item())
        ys = torch.randint(low=0, high=H, size=(n_flips,), generator=g)
        xs = torch.randint(low=0, high=W, size=(n_flips,), generator=g)
        cue_image[ys, xs] = 1.0 - cue_image[ys, xs]

    return {
        "cue_image": cue_image.unsqueeze(0),
        "image": image.unsqueeze(0),
        "hidden_target": hidden_target.unsqueeze(0),
        "occlusion_mask": occlusion_mask.unsqueeze(0),
        "hidden_label": torch.tensor(int(hidden_label), dtype=torch.long),
    }


def _jsonable(x: Any) -> Any:
    if isinstance(x, (str, int, float, bool)) or x is None:
        return x
    if isinstance(x, dict):
        return {str(k): _jsonable(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [_jsonable(v) for v in x]
    return str(x)


def main() -> None:
    p = argparse.ArgumentParser(description="Render a deterministic paired (x,x') witness for ASLMT v7 at fixed ctx.")
    p.add_argument("--cx", type=int, default=16)
    p.add_argument("--cy", type=int, default=16)
    p.add_argument("--t", type=int, default=2)
    p.add_argument("--occ-half", type=int, default=6)
    p.add_argument("--img-size", type=int, default=32)
    p.add_argument("--ood", action="store_true")
    p.add_argument("--seed", type=int, default=0, help="Only used when --ood is set (deterministic cue flips).")
    p.add_argument("--out-dir", type=str, default="", help="If empty, auto-creates a timestamp+hash run dir under aslmt/runs.")
    args = p.parse_args()

    script_path = Path(__file__).resolve()
    script_sha = _sha256_file(script_path)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    suf = f"{ts}_{script_sha[:16]}"

    aslmt_dir = script_path.parents[1]  # .../private/aslmt
    default_runs_dir = aslmt_dir / "runs"
    out_dir = Path(args.out_dir).expanduser().resolve() if args.out_dir else (default_runs_dir / f"aslmt_v7_paired_ctx_{suf}")
    out_dir.mkdir(parents=True, exist_ok=False)

    ctx = Ctx(cx=args.cx, cy=args.cy, t=args.t, occ_half=args.occ_half, img_size=args.img_size, ood=bool(args.ood), seed=int(args.seed))
    r0 = render(ctx, hidden_label=0)
    r1 = render(ctx, hidden_label=1)

    image_equal = torch.equal(r0["image"], r1["image"])
    target_equal = torch.equal(r0["hidden_target"], r1["hidden_target"])

    tensors_path = out_dir / f"paired_ctx_tensors_{suf}.pt"
    manifest_path = out_dir / f"paired_ctx_manifest_{suf}.json"
    console_path = out_dir / f"paired_ctx_console_{suf}.txt"

    payload = {
        "ctx": asdict(ctx),
        "checks": {"image_equal": bool(image_equal), "hidden_target_equal": bool(target_equal)},
        "x": r0,
        "x_prime": r1,
    }
    torch.save(payload, tensors_path)

    manifest = {
        "kind": "aslmt_v7_paired_ctx",
        "timestamp": ts,
        "script": {"path": str(script_path), "sha256": script_sha},
        "cmd": " ".join([os.path.basename(__file__)] + [str(a) for a in os.sys.argv[1:]]),
        "ctx": asdict(ctx),
        "checks": {"image_equal": bool(image_equal), "hidden_target_equal": bool(target_equal)},
        "outputs": {"tensors_pt": str(tensors_path), "manifest_json": str(manifest_path), "console_txt": str(console_path)},
    }
    with open(manifest_path, "w", encoding="utf-8") as f:
        f.write(json.dumps(_jsonable(manifest), indent=2) + "\n")

    with open(console_path, "w", encoding="utf-8") as f:
        f.write(f"CMD: {manifest['cmd']}\n")
        f.write(f"SCRIPT_SHA256: {script_sha}\n")
        f.write(json.dumps(_jsonable(manifest["checks"])) + "\n")

    print(json.dumps(_jsonable(manifest), indent=2))


if __name__ == "__main__":
    main()

