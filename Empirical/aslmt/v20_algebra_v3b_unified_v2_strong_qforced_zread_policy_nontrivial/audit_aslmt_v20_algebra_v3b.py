import argparse
import json
import random
from dataclasses import dataclass

import torch

from render_aslmt_v20_algebra_v3b_paired_ctx_nscalable_spaced2_64 import Ctx, render


def _policy_action_from_h(h: torch.Tensor) -> torch.Tensor:
    """
    Non-trivial policy for selecting the correct interface, as a deterministic function of `h`.

    Output is in {0,1}.
    """
    x = h.to(torch.long) & 0xFFFFFFFF
    x = x ^ ((x << 13) & 0xFFFFFFFF)
    x = x ^ (x >> 17)
    x = x ^ ((x << 5) & 0xFFFFFFFF)
    return (x & 1).to(torch.long)


def _env_res_bit(*, h: torch.Tensor, k: torch.Tensor, action: torch.Tensor) -> torch.Tensor:
    """
    v3b-style action-conditioned response bit (qforced):
      correct action => res_bit == k
      wrong action   => res_bit carries no information about k (here: always 0)
    """
    a = action.to(torch.long)
    kk = k.to(torch.long)
    h2 = _policy_action_from_h(h)
    correct = (a == h2).to(torch.long)
    return kk * correct


@dataclass(frozen=True)
class AuditCfg:
    n_episodes: int
    n_classes: int
    img_size: int
    ood: bool
    seed: int


def _algebra_spec_k_after(*, action: int, res_bit: int, correct_action: int) -> list[int]:
    """
    Algebraic spectrum over k ∈ {0,1} after observing a (action) and r (res_bit),
    given the protocol law used by _env_res_bit.
    """
    a = int(action)
    r = int(res_bit)
    ca = int(correct_action)
    if a == ca:
        # r == k
        if r in (0, 1):
            return [int(r)]
        return []
    # wrong action => r is always 0 under this construction
    if r == 0:
        return [0, 1]
    return []


def run_audit(*, cfg: AuditCfg) -> dict:
    random.seed(int(cfg.seed))
    torch.manual_seed(int(cfg.seed))

    n = int(cfg.n_classes)
    img_size = int(cfg.img_size)

    nontrivial_seen = set()
    examples = []

    for i in range(int(cfg.n_episodes)):
        # sample a context compatible with the renderer constraints
        # keep parameters simple (the dataset itself samples more broadly)
        occ_half = 20
        cx = img_size // 2
        cy = img_size // 2
        t = 2
        ctx = Ctx(cx=cx, cy=cy, t=t, occ_half=occ_half, img_size=img_size, ood=bool(cfg.ood), seed=int(cfg.seed) + i)

        h = random.randint(0, n - 1)
        k0 = 0
        k1 = 1

        ex0 = render(ctx, h=h, k=k0, n_classes=n)
        ex1 = render(ctx, h=h, k=k1, n_classes=n)

        # Barriers (anti-triche):
        # - strong regime => decision-time image must not depend on k
        if not torch.equal(ex0["image"], ex1["image"]):
            raise AssertionError("image barrier violated: image depends on k")
        # - cue must not depend on k
        if not torch.equal(ex0["cue_image"], ex1["cue_image"]):
            raise AssertionError("cue barrier violated: cue depends on k")

        hh = torch.tensor([int(h)], dtype=torch.long)
        correct_action = int(_policy_action_from_h(hh).item())
        nontrivial_seen.add(correct_action)

        # Algebra: before query, spec over k is {0,1} (open)
        spec0 = [0, 1]
        rho0 = len(spec0) - 1

        # correct interface: closes
        for k in (0, 1):
            kk = torch.tensor([int(k)], dtype=torch.long)
            aa = torch.tensor([int(correct_action)], dtype=torch.long)
            r = int(_env_res_bit(h=hh, k=kk, action=aa).item())
            spec1 = _algebra_spec_k_after(action=int(correct_action), res_bit=int(r), correct_action=int(correct_action))
            if spec1 != [int(k)]:
                raise AssertionError("algebra closure violated under correct action")
            rho1 = len(spec1) - 1
            if not (rho1 == 0 and rho0 == 1):
                raise AssertionError("rho values unexpected for correct action")

        # wrong interface: remains open when r=0
        wrong_action = 1 - int(correct_action)
        for k in (0, 1):
            kk = torch.tensor([int(k)], dtype=torch.long)
            aa = torch.tensor([int(wrong_action)], dtype=torch.long)
            r = int(_env_res_bit(h=hh, k=kk, action=aa).item())
            if r != 0:
                raise AssertionError("wrong action must produce non-informative res_bit=0")
            spec1 = _algebra_spec_k_after(action=int(wrong_action), res_bit=int(r), correct_action=int(correct_action))
            if spec1 != [0, 1]:
                raise AssertionError("algebra openness violated under wrong action")
            rho1 = len(spec1) - 1
            if rho1 != rho0:
                raise AssertionError("rho should not contract under wrong action")

        if i < 3:
            examples.append(
                {
                    "h": int(h),
                    "policy(h)": int(correct_action),
                    "rho0": int(rho0),
                    "rho1_correct": 0,
                    "rho1_wrong": int(rho0),
                }
            )

    if nontrivial_seen != {0, 1}:
        raise AssertionError(f"policy nontriviality check failed: seen={sorted(nontrivial_seen)}")

    return {
        "ok": True,
        "n_episodes": int(cfg.n_episodes),
        "n_classes": int(cfg.n_classes),
        "ood": bool(cfg.ood),
        "examples": examples,
    }


def main() -> None:
    p = argparse.ArgumentParser(description="Independent algebra audit for v20 algebra v3b bundle.")
    p.add_argument("--episodes", type=int, default=50)
    p.add_argument("--n-classes", type=int, default=8)
    p.add_argument("--img-size", type=int, default=64)
    p.add_argument("--ood", action="store_true")
    p.add_argument("--seed", type=int, default=0)
    args = p.parse_args()

    out = run_audit(
        cfg=AuditCfg(
            n_episodes=int(args.episodes),
            n_classes=int(args.n_classes),
            img_size=int(args.img_size),
            ood=bool(args.ood),
            seed=int(args.seed),
        )
    )
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()

