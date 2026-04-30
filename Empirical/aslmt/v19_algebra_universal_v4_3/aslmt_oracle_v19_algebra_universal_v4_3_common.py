from __future__ import annotations

from dataclasses import dataclass

import torch


@dataclass(frozen=True)
class HorizonOracleCfg:
    forbid_view0: bool = True
    allow_stop_only_if_closed: bool = True


def candidate_mask(
    *,
    tables: torch.Tensor,  # (V,N)
    base_obs: int,
    actions: list[int],
    responses: list[int],
) -> torch.Tensor:
    """
    Candidate set induced by the observed transcript (base_obs + queried view/response pairs).

    Convention: STOP action is encoded as a == V and is ignored in refinement.
    """
    V, _ = tables.shape
    m = tables[0].eq(int(base_obs))
    if len(actions) != len(responses):
        raise ValueError("actions/responses length mismatch")
    for a, r in zip(actions, responses):
        a = int(a)
        if a == int(V):
            continue
        if a < 0 or a > int(V) - 1:
            raise ValueError(f"action out of range: {a} for n_views={V}")
        m = m & tables[a].eq(int(r))
    return m


def sigma_ambiguity(*, sigma: torch.Tensor, cand_mask: torch.Tensor) -> int:
    vals = sigma[cand_mask]
    if int(vals.numel()) == 0:
        return 0
    return int(torch.unique(vals).numel())


def _mask_to_bitmask(mask: torch.Tensor) -> int:
    idx = mask.nonzero(as_tuple=False).flatten().to(torch.long).tolist()
    bm = 0
    for i in idx:
        bm |= 1 << int(i)
    return int(bm)


def _bitmask_count(bm: int) -> int:
    return int(bm.bit_count())


def _bitmask_to_indices(bm: int) -> list[int]:
    out: list[int] = []
    i = 0
    while bm:
        if bm & 1:
            out.append(i)
        bm >>= 1
        i += 1
    return out


def _best_value(
    *,
    tables: torch.Tensor,  # (V,N) CPU
    sigma: torch.Tensor,  # (N,) CPU
    base_obs: int,
    cand_bm: int,
    used_views_mask: int,
    depth_left: int,
    cfg: HorizonOracleCfg,
    cache: dict[tuple[int, int, int], tuple[float, float, float]],
) -> tuple[float, float, float]:
    """
    Return a lexicographic value tuple:

      (expected_steps_to_closure, expected_final_ambiguity, expected_final_candidate_size)

    Under the protocol rules:
    - STOP is allowed iff the current candidate set is already closed (ambiguity==1), unless cfg says otherwise.
    - view 0 is forbidden if cfg.forbid_view0 is True.
    - views cannot repeat.
    """
    key = (int(depth_left), int(used_views_mask), int(cand_bm))
    if key in cache:
        return cache[key]

    idx0 = _bitmask_to_indices(int(cand_bm))
    if not idx0:
        cache[key] = (0.0, 0.0, 0.0)
        return cache[key]

    cand_mask = torch.zeros((sigma.numel(),), dtype=torch.bool)
    cand_mask[idx0] = True
    amb0 = sigma_ambiguity(sigma=sigma, cand_mask=cand_mask)
    sz0 = float(len(idx0))

    if bool(cfg.allow_stop_only_if_closed) and int(amb0) == 1:
        cache[key] = (0.0, 1.0, float(sz0))
        return cache[key]

    if int(depth_left) <= 0:
        # No budget remaining but not closed: infeasible under the intended construction.
        cache[key] = (1e6, float(amb0), float(sz0))
        return cache[key]

    V, _ = tables.shape
    V = int(V)

    best: tuple[float, float, float] | None = None
    for a in range(int(V)):
        if bool(cfg.forbid_view0) and int(a) == 0:
            continue
        if (int(used_views_mask) >> int(a)) & 1:
            continue

        labels = tables[int(a), idx0].to(torch.long)
        uniq = torch.unique(labels).tolist()
        total0 = float(len(idx0))

        exp_steps = 0.0
        exp_amb = 0.0
        exp_sz = 0.0
        for r in uniq:
            r = int(r)
            cand1 = cand_mask & tables[int(a)].eq(int(r))
            bm1 = _mask_to_bitmask(cand1)
            sz1 = _bitmask_count(int(bm1))
            if int(sz1) <= 0:
                continue
            p = float(sz1) / total0
            v1 = _best_value(
                tables=tables,
                sigma=sigma,
                base_obs=int(base_obs),
                cand_bm=int(bm1),
                used_views_mask=int(used_views_mask) | (1 << int(a)),
                depth_left=int(depth_left) - 1,
                cfg=cfg,
                cache=cache,
            )
            exp_steps += p * float(v1[0])
            exp_amb += p * float(v1[1])
            exp_sz += p * float(v1[2])

        # one step consumed now
        score = (1.0 + float(exp_steps), float(exp_amb), float(exp_sz))
        if best is None or score < best:
            best = score

    if best is None:
        cache[key] = (1e6, float(amb0), float(sz0))
        return cache[key]

    cache[key] = best
    return best


def oracle_action_values(
    *,
    tables: torch.Tensor,  # (V,N) (CPU or GPU)
    sigma: torch.Tensor,  # (N,)
    base_obs: int,
    actions_prefix: list[int],
    responses_prefix: list[int],
    remaining_steps: int,
    cfg: HorizonOracleCfg,
    include_stop: bool = True,
    ) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
    """
    Compute (value, exp_final_size) per action for the current transcript prefix.

    value is a 3-vector, but for training/logits we return:
      - exp_steps_to_closure
      - exp_final_ambiguity
      - exp_final_candidate_size

    Returned tensors are shaped:
      steps: (A,)
      amb  : (A,)
      sz   : (A,)

    where A = V + (include_stop ? 1 : 0), STOP id = V.
    """
    BIG = 1e6
    tables_cpu = tables.detach().cpu()
    sigma_cpu = sigma.detach().cpu()
    V, N = tables_cpu.shape
    V = int(V)
    A = int(V) + (1 if bool(include_stop) else 0)

    cand0 = candidate_mask(
        tables=tables_cpu,
        base_obs=int(base_obs),
        actions=list(actions_prefix),
        responses=list(responses_prefix),
    )
    cand_bm0 = _mask_to_bitmask(cand0)
    idx0 = _bitmask_to_indices(int(cand_bm0))
    used_mask = 0
    for a in actions_prefix:
        a = int(a)
        if 0 <= a < V:
            used_mask |= 1 << int(a)

    steps = torch.full((A,), float(BIG), dtype=torch.float32)
    amb = torch.full((A,), float(BIG), dtype=torch.float32)
    sz = torch.full((A,), float(BIG), dtype=torch.float32)

    if not idx0:
        # degenerate; leave as huge
        return steps, amb, sz

    cache: dict[tuple[int, int, int], tuple[float, float, float]] = {}

    # current ambiguity/size
    amb0 = float(sigma_ambiguity(sigma=sigma_cpu, cand_mask=cand0))
    sz0 = float(len(idx0))

    # STOP
    if bool(include_stop):
        stop = int(V)
        if (not bool(cfg.allow_stop_only_if_closed)) or int(amb0) == 1:
            steps[stop] = 0.0
            amb[stop] = float(amb0)
            sz[stop] = float(sz0)
        else:
            steps[stop] = float(BIG)
            amb[stop] = float(BIG)
            sz[stop] = float(BIG)

    # view actions
    for a in range(int(V)):
        if bool(cfg.forbid_view0) and int(a) == 0:
            continue
        if (int(used_mask) >> int(a)) & 1:
            continue

        labels = tables_cpu[int(a), idx0].to(torch.long)
        uniq = torch.unique(labels).tolist()
        total0 = float(len(idx0))

        exp_steps = 0.0
        exp_amb = 0.0
        exp_sz = 0.0
        for r in uniq:
            r = int(r)
            cand1 = cand0 & tables_cpu[int(a)].eq(int(r))
            bm1 = _mask_to_bitmask(cand1)
            sz1 = _bitmask_count(int(bm1))
            if int(sz1) <= 0:
                continue
            p = float(sz1) / total0
            v1 = _best_value(
                tables=tables_cpu,
                sigma=sigma_cpu,
                base_obs=int(base_obs),
                cand_bm=int(bm1),
                used_views_mask=int(used_mask) | (1 << int(a)),
                depth_left=int(remaining_steps) - 1,
                cfg=cfg,
                cache=cache,
            )
            exp_steps += p * float(v1[0])
            exp_amb += p * float(v1[1])
            exp_sz += p * float(v1[2])

        steps[a] = 1.0 + float(exp_steps)
        amb[a] = float(exp_amb)
        sz[a] = float(exp_sz)

    return steps, amb, sz


def oracle_allowed_actions(
    *,
    tables: torch.Tensor,  # (V,N)
    sigma: torch.Tensor,  # (N,)
    base_obs: int,
    actions_prefix: list[int],
    responses_prefix: list[int],
    remaining_steps: int,
    cfg: HorizonOracleCfg,
) -> list[int]:
    """
    Return the set of horizon-optimal actions:
      argmin_a (steps_to_closure, final_amb, final_size)

    STOP (id=V) is included iff closure already holds (ambiguity==1),
    and cfg.allow_stop_only_if_closed is True.
    """
    steps, amb, sz = oracle_action_values(
        tables=tables,
        sigma=sigma,
        base_obs=int(base_obs),
        actions_prefix=list(actions_prefix),
        responses_prefix=list(responses_prefix),
        remaining_steps=int(remaining_steps),
        cfg=cfg,
        include_stop=True,
    )
    V, _ = tables.detach().cpu().shape
    V = int(V)
    A = int(V) + 1

    best = None
    for a in range(A):
        t = float(steps[a].item())
        if t >= 1e5:
            continue
        s = (t, float(amb[a].item()), float(sz[a].item()), int(a))
        if best is None or s < best:
            best = s

    if best is None:
        return [int(V)]

    best_key = (float(best[0]), float(best[1]), float(best[2]))
    allowed: list[int] = []
    eps = 1e-7
    for a in range(A):
        t = float(steps[a].item())
        if t >= 1e5:
            continue
        k = (float(t), float(amb[a].item()), float(sz[a].item()))
        if (
            abs(float(k[0]) - float(best_key[0])) <= eps
            and abs(float(k[1]) - float(best_key[1])) <= eps
            and abs(float(k[2]) - float(best_key[2])) <= eps
        ):
            allowed.append(int(a))

    if not allowed:
        raise RuntimeError("oracle failure: no horizon-optimal action found")
    return sorted(set(int(a) for a in allowed))
