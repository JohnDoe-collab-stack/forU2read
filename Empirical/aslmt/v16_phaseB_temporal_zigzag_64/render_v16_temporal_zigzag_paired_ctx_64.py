import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from datetime import datetime
from pathlib import Path
from typing import Any

import torch


POS_STRIDE: int = 2
DEFAULT_IMG_SIZE: int = 64


@dataclass(frozen=True)
class Ctx:
    horizon: int
    img_size: int = DEFAULT_IMG_SIZE
    ood: bool = False
    seed: int = 0


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _draw_point(mask: torch.Tensor, x: int, y: int, img_size: int, value: float = 1.0) -> None:
    if 0 <= int(x) < int(img_size) and 0 <= int(y) < int(img_size):
        mask[int(y), int(x)] = float(value)


def _h_to_start_x(*, h: int, n_classes: int, img_size: int, margin: int) -> int:
    n = int(n_classes)
    needed = int(POS_STRIDE) * int(n - 1) + 1
    if int(img_size) - 2 * int(margin) < int(needed):
        raise ValueError(
            f"img_size={int(img_size)} too small for n={int(n)} under stride={int(POS_STRIDE)} "
            f"(needed width={int(needed)}, available={int(img_size) - 2 * int(margin)})"
        )
    return int(margin + int(POS_STRIDE) * int(h % n))


def sample_ctx(*, idx: int, n_classes: int, ood: bool, img_size: int, seed_base: int) -> Ctx:
    """
    Phase B family T1 (temporal): contexts differ by `horizon`.

    IID uses short horizons; OOD uses longer horizons.
    """
    g = torch.Generator().manual_seed(int(seed_base) + int(idx))
    if bool(ood):
        horizon = int(torch.randint(low=9, high=17, size=(1,), generator=g).item())
    else:
        horizon = int(torch.randint(low=4, high=9, size=(1,), generator=g).item())
    return Ctx(horizon=horizon, img_size=int(img_size), ood=bool(ood), seed=int(seed_base) + int(idx))


def render(ctx: Ctx, *, h: int, k: int, n_classes: int) -> dict[str, torch.Tensor]:
    """
    Temporal family (no occluder):

    - `h` is visible only in `cue_image` as a start location.
    - `k` is visible only in `image` as a present mark (top stripe).
    - The hidden target is a zigzag trajectory of length `ctx.horizon` starting from `h`,
      with initial direction controlled by `k`.

    Barrier structure:
      - image barrier: vary `h` with fixed `k` => image equal, target differs
      - cue barrier: vary `k` with fixed `h` => cue equal, target differs
    """
    n = int(n_classes)
    assert n >= 2

    H = int(ctx.img_size)
    W = int(ctx.img_size)
    margin = 4

    cue = torch.zeros((H, W), dtype=torch.float32)
    image = torch.zeros((H, W), dtype=torch.float32)
    hidden_target = torch.zeros((H, W), dtype=torch.float32)
    occlusion_mask = torch.zeros((H, W), dtype=torch.float32)

    hh = int(h) % int(n)
    kk = int(k) % 2

    start_x = _h_to_start_x(h=hh, n_classes=n, img_size=W, margin=margin)
    start_y = int(H // 2)

    # Cue shows the start (h) as a small marker.
    _draw_point(cue, start_x, start_y, H, 1.0)
    _draw_point(cue, start_x, start_y + 1, H, 1.0)

    # Image shows k as a present mark stripe.
    if kk == 1:
        image[0:3, :] = 1.0

    # Add mild OOD-only background noise that does not encode h or k.
    if bool(ctx.ood):
        g = torch.Generator().manual_seed(int(ctx.seed) + 991)
        n_noise = int(torch.randint(low=0, high=9, size=(1,), generator=g).item())
        for i in range(n_noise):
            yy = int(torch.randint(low=3, high=H, size=(1,), generator=g).item())
            xx = int(torch.randint(low=0, high=W, size=(1,), generator=g).item())
            _draw_point(image, xx, yy, H, 0.25)

    # Zigzag walk in the hidden target.
    # Direction alternates every step; k chooses the initial direction.
    x = int(start_x)
    y = int(start_y)
    for i in range(int(ctx.horizon)):
        _draw_point(hidden_target, x, y, H, 1.0)
        horiz = bool((i + kk) % 2 == 0)
        if horiz:
            x = x + 1
        else:
            y = y + 1
        if x >= W - margin:
            x = int(margin)
        if y >= H - margin:
            y = int(margin)

    return {
        "cue_image": cue.unsqueeze(0),
        "image": image.unsqueeze(0),
        "hidden_target": hidden_target.unsqueeze(0),
        "occlusion_mask": occlusion_mask.unsqueeze(0),
        "h": torch.tensor(int(hh), dtype=torch.long),
        "k": torch.tensor(int(kk), dtype=torch.long),
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
    p = argparse.ArgumentParser(description="Render paired-ctx witnesses for ASLMT v16 temporal zigzag family (64x64).")
    p.add_argument("--n-classes", type=int, default=8)
    p.add_argument("--horizon", type=int, default=6)
    p.add_argument("--img-size", type=int, default=DEFAULT_IMG_SIZE)
    p.add_argument("--ood", action="store_true")
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--out-dir", type=str, default="")
    args = p.parse_args()

    script_path = Path(__file__).resolve()
    script_sha = _sha256_file(script_path)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    suf = f"{ts}_{script_sha[:16]}"

    aslmt_dir = script_path.parents[1]
    runs_dir = aslmt_dir / "runs"
    out_dir = Path(args.out_dir).expanduser().resolve() if args.out_dir else (runs_dir / f"aslmt_v16_temporal_zigzag_paired_ctx_{suf}")
    out_dir.mkdir(parents=True, exist_ok=False)

    ctx = Ctx(horizon=int(args.horizon), img_size=int(args.img_size), ood=bool(args.ood), seed=int(args.seed))
    n = int(args.n_classes)

    k_fixed = 0
    x_im0 = render(ctx, h=0, k=k_fixed, n_classes=n)
    x_im1 = render(ctx, h=1, k=k_fixed, n_classes=n)

    h_fixed = 0
    x_cu0 = render(ctx, h=h_fixed, k=0, n_classes=n)
    x_cu1 = render(ctx, h=h_fixed, k=1, n_classes=n)

    checks = {
        "image_barrier": {
            "image_equal": bool(torch.equal(x_im0["image"], x_im1["image"])),
            "target_equal": bool(torch.equal(x_im0["hidden_target"], x_im1["hidden_target"])),
        },
        "cue_barrier": {
            "cue_equal": bool(torch.equal(x_cu0["cue_image"], x_cu1["cue_image"])),
            "target_equal": bool(torch.equal(x_cu0["hidden_target"], x_cu1["hidden_target"])),
        },
        "params": {"stride": int(POS_STRIDE), "img_size": int(ctx.img_size), "horizon": int(ctx.horizon)},
    }

    payload = {
        "ctx": asdict(ctx),
        "n_classes": n,
        "checks": checks,
        "image_pair": {"x": x_im0, "x_prime": x_im1, "k_fixed": k_fixed},
        "cue_pair": {"x": x_cu0, "x_prime": x_cu1, "h_fixed": h_fixed},
    }
    tensors_path = out_dir / f"paired_ctx_tensors_{suf}.pt"
    torch.save(payload, tensors_path)

    manifest = {
        "kind": "aslmt_v16_temporal_zigzag_paired_ctx",
        "timestamp": ts,
        "script": {"path": str(script_path), "sha256": str(script_sha)},
        "out_dir": str(out_dir),
        "tensors_path": str(tensors_path),
        "payload_summary": _jsonable({"ctx": payload["ctx"], "n_classes": payload["n_classes"], "checks": payload["checks"]}),
    }
    (out_dir / f"paired_ctx_manifest_{suf}.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()

