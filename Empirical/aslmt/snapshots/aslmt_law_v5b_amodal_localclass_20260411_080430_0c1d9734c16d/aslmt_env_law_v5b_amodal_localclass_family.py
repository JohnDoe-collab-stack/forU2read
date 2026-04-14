#!/usr/bin/env python3
from __future__ import annotations

# v5b env: copy of v5 env, pinned here to avoid accidental drift.

from dataclasses import asdict, dataclass

import torch


@dataclass(frozen=True)
class LawV5bAmodalConfig:
    img_size: int = 32
    thickness_min: int = 2
    thickness_max: int = 4
    iid_n_occluders_min: int = 2
    iid_n_occluders_max: int = 6
    iid_occ_size_min: int = 3
    iid_occ_size_max: int = 6
    ood_center_radius: int = 10
    ood_noise_occluders: int = 2
    ood_noise_radius: int = 3


def cfg_by_name(cfg_name: str) -> LawV5bAmodalConfig:
    # Family is defined by OOD occluder severity.
    if cfg_name == "C0_hard":
        # Diagnostic / borderline: very large central occluder.
        return LawV5bAmodalConfig(ood_center_radius=14)
    if cfg_name == "C1_mid":
        # Reference gate.
        return LawV5bAmodalConfig(ood_center_radius=10)
    if cfg_name == "C2_soft":
        # Reference gate (harder than C1): make local visible-only completion fail more reliably.
        return LawV5bAmodalConfig(ood_center_radius=12)
    raise ValueError(f"Unknown cfg_name: {cfg_name}")


def cfg_names() -> list[str]:
    return ["C0_hard", "C1_mid", "C2_soft"]


def _draw_rect(mask_hw: torch.Tensor, *, cx: int, cy: int, w: int, h: int) -> None:
    # mask_hw is [H, W]
    H = int(mask_hw.shape[0])
    W = int(mask_hw.shape[1])
    y0 = max(0, int(cy - h))
    y1 = min(H, int(cy + h))
    x0 = max(0, int(cx - w))
    x1 = min(W, int(cx + w))
    mask_hw[y0:y1, x0:x1] = 1.0


def _randint(g: torch.Generator, low: int, high: int) -> int:
    # inclusive low, inclusive high
    if high < low:
        raise ValueError("bad randint bounds")
    return int(torch.randint(low=low, high=high + 1, size=(1,), generator=g).item())


def sample_batch(*, cfg: LawV5bAmodalConfig, batch_size: int, device: str, g: torch.Generator, ood: bool) -> dict[str, torch.Tensor]:
    H = int(cfg.img_size)
    W = int(cfg.img_size)
    # Important: build masks on CPU (fast Python indexing), then move to device.
    # Writing pixel-by-pixel directly into CUDA tensors is extremely slow.
    amodal_cpu = torch.zeros((batch_size, 1, H, W), device="cpu", dtype=torch.float32)
    occl_cpu = torch.zeros((batch_size, 1, H, W), device="cpu", dtype=torch.float32)

    for b in range(int(batch_size)):
        am = amodal_cpu[b, 0]
        oc = occl_cpu[b, 0]

        obj_type = _randint(g, 0, 2)  # 0=cross, 1=L, 2=parallel
        cx = _randint(g, 10, 22)
        cy = _randint(g, 10, 22)
        t = _randint(g, int(cfg.thickness_min), int(cfg.thickness_max))

        if obj_type == 0:
            _draw_rect(am, cx=cx, cy=cy, w=cfg.img_size, h=t)
            _draw_rect(am, cx=cx, cy=cy, w=t, h=cfg.img_size)
        elif obj_type == 2:
            d = _randint(g, 5, 8)
            _draw_rect(am, cx=cx - d, cy=cy, w=t, h=cfg.img_size)
            _draw_rect(am, cx=cx + d, cy=cy, w=t, h=cfg.img_size)
        else:
            _draw_rect(am, cx=cx // 2, cy=cy, w=cx // 2, h=t)
            _draw_rect(am, cx=cx, cy=cy // 2, w=t, h=cy // 2)

        if ood:
            _draw_rect(oc, cx=16, cy=16, w=int(cfg.ood_center_radius), h=int(cfg.ood_center_radius))
            for _ in range(int(cfg.ood_noise_occluders)):
                ox = _randint(g, 0, 31)
                oy = _randint(g, 0, 31)
                _draw_rect(oc, cx=ox, cy=oy, w=int(cfg.ood_noise_radius), h=int(cfg.ood_noise_radius))
        else:
            n_occ = _randint(g, int(cfg.iid_n_occluders_min), int(cfg.iid_n_occluders_max))
            for _ in range(int(n_occ)):
                ox = _randint(g, 0, 31)
                oy = _randint(g, 0, 31)
                occ_size = _randint(g, int(cfg.iid_occ_size_min), int(cfg.iid_occ_size_max))
                _draw_rect(oc, cx=ox, cy=oy, w=occ_size, h=occ_size)

    amodal = amodal_cpu.to(device)
    occl = occl_cpu.to(device)
    image = torch.clamp(amodal + occl, 0.0, 1.0)
    visible = amodal * (1.0 - occl)
    return {
        "image": image,
        "amodal_mask": amodal,
        "visible_mask": visible,
        "occlusion_mask": occl,
        "cfg": asdict(cfg),
        "ood": bool(ood),
    }

