from __future__ import annotations

from dataclasses import dataclass

import torch
import random


class LawV3Tokens:
    # Fixed ids.
    DELAY = 0
    RES_MISS = 1
    RES_BIT0 = 2
    RES_BIT1 = 3

    # Visible token at query time (lo-class).
    LO_BASE = 20_000

    # Mask-bit tokens: MASKBIT_BASE + (j*2 + bit)
    MASKBIT_BASE = 40_000

    # Parity token: PARITY_BASE + parity_bit
    PARITY_BASE = 50_000

    @staticmethod
    def tok_maskbit(j: int, bit: int) -> int:
        return int(LawV3Tokens.MASKBIT_BASE + int(j) * 2 + int(bit))

    @staticmethod
    def tok_parity(bit: int) -> int:
        return int(LawV3Tokens.PARITY_BASE + int(bit))

    @staticmethod
    def vocab_size(cfg: "LawV3QueryPOMDPConfig") -> int:
        lo_max = LawV3Tokens.LO_BASE + (1 << int(cfg.n_lo_bits))
        mask_max = LawV3Tokens.MASKBIT_BASE + int(cfg.n_hi_bits) * 2
        parity_max = LawV3Tokens.PARITY_BASE + 2
        return int(max(lo_max, mask_max, parity_max) + 1)


@dataclass(frozen=True)
class LawV3QueryPOMDPConfig:
    n_bits: int = 64
    n_index_bits: int = 6
    n_hi_bits: int = 3
    n_lo_bits: int = 3

    # Number of views. Each view contributes (n_hi_bits mask tokens + 1 parity token).
    n_views: int = 6

    iid_delay_max: int = 1
    ood_delay_min: int = 2
    ood_delay_max: int = 5

    def __post_init__(self) -> None:
        if (1 << int(self.n_index_bits)) < int(self.n_bits):
            raise ValueError("n_index_bits too small for n_bits")
        if int(self.n_hi_bits) + int(self.n_lo_bits) != int(self.n_index_bits):
            raise ValueError("n_hi_bits + n_lo_bits must equal n_index_bits")
        if int(self.n_views) <= 0:
            raise ValueError("n_views must be positive")
        if int(self.n_hi_bits) <= 0:
            raise ValueError("n_hi_bits must be positive")

    @property
    def n_queries(self) -> int:
        return 1 << int(self.n_hi_bits)

    def hi_class(self, i: torch.Tensor) -> torch.Tensor:
        return (i >> int(self.n_lo_bits)) & ((1 << int(self.n_hi_bits)) - 1)

    def lo_class(self, i: torch.Tensor) -> torch.Tensor:
        return i & ((1 << int(self.n_lo_bits)) - 1)


def _make_lo_token(cfg: LawV3QueryPOMDPConfig, lo: torch.Tensor) -> torch.Tensor:
    return (lo + LawV3Tokens.LO_BASE).long()


def _parity(mask_int: torch.Tensor, hi: torch.Tensor) -> torch.Tensor:
    x = (mask_int & hi).long()
    parity = torch.zeros_like(x)
    while True:
        parity ^= (x & 1)
        x = x >> 1
        if int(x.max().item()) == 0:
            break
    return parity.long()


def _full_rank_sets(n_hi_bits: int) -> list[tuple[int, ...]]:
    """
    Enumerate all ordered n_hi_bits-tuples of distinct nonzero masks in {1..2^n_hi_bits-1}
    that form a full-rank matrix over GF(2).

    This is tiny for n_hi_bits <= 4 (our default family), and avoids per-sample rank checks.
    """
    if n_hi_bits > 8:
        # Keep the implementation intentionally small and safe.
        raise ValueError("n_hi_bits too large for law_v3 full-rank enumeration")

    masks = list(range(1, (1 << n_hi_bits)))

    def rank_of(rows: list[int]) -> int:
        rows = rows[:]
        r = 0
        for b in range(n_hi_bits):
            pivot = None
            for k in range(r, len(rows)):
                if (rows[k] >> b) & 1:
                    pivot = k
                    break
            if pivot is None:
                continue
            rows[r], rows[pivot] = rows[pivot], rows[r]
            for k in range(len(rows)):
                if k != r and ((rows[k] >> b) & 1):
                    rows[k] ^= rows[r]
            r += 1
        return r

    out: list[tuple[int, ...]] = []
    # Brute force ordered tuples; still fine at n_hi_bits <= 4.
    import itertools

    for rows in itertools.permutations(masks, n_hi_bits):
        if rank_of(list(rows)) == n_hi_bits:
            out.append(tuple(int(x) for x in rows))
    if not out:
        raise RuntimeError("No full-rank mask-sets found")
    return out


_CACHE_SETS: dict[int, list[tuple[int, ...]]] = {}


def _get_sets(n_hi_bits: int) -> list[tuple[int, ...]]:
    if n_hi_bits not in _CACHE_SETS:
        _CACHE_SETS[n_hi_bits] = _full_rank_sets(n_hi_bits)
    return _CACHE_SETS[n_hi_bits]


def _sample_masks_all(*, cfg: LawV3QueryPOMDPConfig, batch_size: int, ood: bool, g: torch.Generator | None) -> torch.Tensor:
    """
    Returns a full set of view masks as integers, shape [B, n_views].

    Hard-OOD guarantee:
    - IID and OOD draw from disjoint subsets (by index) of the same full-rank set list.
    - **All** views (not only the first n_hi_bits) are drawn from the corresponding subset.

    This ensures the OOD shift is not "partially shared" via extra views.
    """
    n_hi = int(cfg.n_hi_bits)
    n_views = int(cfg.n_views)

    sets = _get_sets(n_hi)
    n = len(sets)
    if n <= 1:
        raise RuntimeError("Need at least 2 full-rank sets for hard-OOD split")

    # Build a deterministic hard-OOD split that is not tied to the raw enumeration order.
    #
    # Special case n_hi_bits=2:
    # The full-rank pool is exactly the 6 permutations of (1,2,3). A contiguous split
    # can create biased marginals and make C0 sensitive to enumeration artifacts.
    # We instead use an explicitly balanced 3/3 split:
    #   IID = {(1,2), (2,3), (3,1)}
    #   OOD = {(1,3), (2,1), (3,2)}
    #
    # For n_hi_bits >= 3:
    # We seed-shuffle indices and alternate IID/OOD to balance marginals better than a contiguous cut.
    if n_hi == 2:
        want_iid = [(1, 2), (2, 3), (3, 1)]
        want_ood = [(1, 3), (2, 1), (3, 2)]
        pos = {tuple(t): k for k, t in enumerate(sets)}
        try:
            iid_idx = [int(pos[t]) for t in want_iid]
            ood_idx = [int(pos[t]) for t in want_ood]
        except KeyError as e:
            raise RuntimeError(f"Missing expected n_hi=2 tuple in full-rank pool: {e}")
    else:
        idxs = list(range(n))
        rng = random.Random(1337 + n_hi)
        rng.shuffle(idxs)
        iid_idx = idxs[0::2]
        ood_idx = idxs[1::2]
        if not iid_idx or not ood_idx:
            # Fallback: contiguous split if alternation degenerated (should not happen for our pools).
            mid = max(1, n // 2)
            iid_idx = list(range(0, mid))
            ood_idx = list(range(mid, n))

    # How many full-rank blocks do we need to cover n_views?
    n_blocks = (n_views + n_hi - 1) // n_hi
    if n_blocks <= 0:
        raise RuntimeError("Invalid n_blocks")

    pool = iid_idx if not ood else ood_idx
    pool_t = torch.tensor(pool, dtype=torch.long)
    # Draw n_blocks indices per sample from the proper pool.
    pick = torch.randint(low=0, high=len(pool), size=(batch_size, n_blocks), generator=g, dtype=torch.long)
    idx = pool_t[pick]

    # Materialize chosen blocks on CPU (small); then slice to n_views.
    chosen = [[sets[int(j)] for j in row] for row in idx.tolist()]  # [[(mask,...)*n_blocks]*B]
    blocks = torch.tensor(chosen, dtype=torch.long)  # [B, n_blocks, n_hi]
    masks = blocks.reshape(batch_size, n_blocks * n_hi)[:, :n_views]  # [B, n_views]
    return masks


def _encode_view_tokens(*, cfg: LawV3QueryPOMDPConfig, masks_all: torch.Tensor, hi: torch.Tensor) -> torch.Tensor:
    """
    Build view token sequence, shape [B, T], where each view contributes:
      - n_hi_bits tokens encoding each mask bit (0/1)
      - 1 token encoding the parity

    Each "view" is one mask-row integer (in [1, 2^n_hi_bits)), and `masks_all` is already sampled
    according to the hard-OOD rule (IID/OOD disjoint mask-set pools).
    """
    B = int(masks_all.shape[0])
    n_hi = int(cfg.n_hi_bits)

    # Encode mask bits as tokens.
    bit_tokens = []
    for j in range(n_hi):
        bit = ((masks_all >> j) & 1).long()  # [B, V]
        tok0 = torch.full_like(bit, LawV3Tokens.tok_maskbit(j, 0))
        tok1 = torch.full_like(bit, LawV3Tokens.tok_maskbit(j, 1))
        bit_tokens.append(torch.where(bit.eq(0), tok0, tok1))

    parity = _parity(masks_all, hi.unsqueeze(1).expand_as(masks_all))
    parity_tok = torch.where(
        parity.eq(0),
        torch.full_like(parity, LawV3Tokens.tok_parity(0)),
        torch.full_like(parity, LawV3Tokens.tok_parity(1)),
    )

    # Interleave: for each view v, emit maskbit tokens for j=0..n_hi-1, then parity token.
    V = int(masks_all.shape[1])
    T = V * (n_hi + 1)
    out = torch.empty((B, T), dtype=torch.long)
    t = 0
    for v in range(V):
        for j in range(n_hi):
            out[:, t] = bit_tokens[j][:, v]
            t += 1
        out[:, t] = parity_tok[:, v]
        t += 1
    return out


def sample_batch(*, batch_size: int, cfg: LawV3QueryPOMDPConfig, device: str, ood: bool, seed: int | None) -> dict:
    if seed is not None:
        g = torch.Generator(device="cpu")
        g.manual_seed(int(seed) + (10_000 if ood else 0))
    else:
        g = None

    H = torch.randint(low=0, high=2, size=(batch_size, int(cfg.n_bits)), generator=g, dtype=torch.long)
    i = torch.randint(low=0, high=int(cfg.n_bits), size=(batch_size,), generator=g, dtype=torch.long)
    hi = cfg.hi_class(i)
    lo = cfg.lo_class(i)

    lo_tok = _make_lo_token(cfg, lo).to(device)

    masks_all = _sample_masks_all(cfg=cfg, batch_size=batch_size, ood=ood, g=g)  # [B, n_views]
    view_seq = _encode_view_tokens(cfg=cfg, masks_all=masks_all, hi=hi)  # [B, T]

    view_seq = view_seq.to(device)
    H = H.to(device)
    i = i.to(device)

    if not ood:
        d1 = torch.randint(low=0, high=int(cfg.iid_delay_max) + 1, size=(batch_size,), generator=g, dtype=torch.long).to(device)
        d2 = torch.randint(low=0, high=int(cfg.iid_delay_max) + 1, size=(batch_size,), generator=g, dtype=torch.long).to(device)
    else:
        d1 = torch.randint(low=int(cfg.ood_delay_min), high=int(cfg.ood_delay_max) + 1, size=(batch_size,), generator=g, dtype=torch.long).to(device)
        d2 = torch.randint(low=int(cfg.ood_delay_min), high=int(cfg.ood_delay_max) + 1, size=(batch_size,), generator=g, dtype=torch.long).to(device)

    return {"H": H, "i": i, "lo_tok": lo_tok, "view_seq": view_seq, "d1": d1, "d2": d2}


def env_step_result_token(*, cfg: LawV3QueryPOMDPConfig, H: torch.Tensor, i: torch.Tensor, a_hi: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
    hi_true = cfg.hi_class(i)
    correct = a_hi.eq(hi_true)
    bit = H.gather(dim=1, index=i.unsqueeze(1)).squeeze(1)
    res_tok = torch.where(
        correct,
        torch.where(bit.eq(0), torch.full_like(bit, LawV3Tokens.RES_BIT0), torch.full_like(bit, LawV3Tokens.RES_BIT1)),
        torch.full_like(bit, LawV3Tokens.RES_MISS),
    ).long()
    return correct, bit.long(), res_tok
