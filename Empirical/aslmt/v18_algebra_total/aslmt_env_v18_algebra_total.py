import random

import torch
from torch.utils.data import Dataset


def _int_to_bits(x: torch.Tensor, *, k_dim: int) -> torch.Tensor:
    """
    Convert integer tensor x (shape (B,)) to bits tensor (shape (B,k_dim)) with LSB-first.
    """
    x = x.to(torch.long)
    bits = []
    for j in range(int(k_dim)):
        bits.append(((x >> j) & 1).to(torch.long))
    return torch.stack(bits, dim=1)


class V18AlgebraTotalDataset(Dataset):
    """
    Multi-interface closure toy, designed to exercise:

    base  : sees h only (visible-only barrier on k),
    query : action chooses which interface to read,
    response is informative only on a specific action per k component,
    target depends on (h,k) so closure needs query.
    """

    def __init__(
        self,
        *,
        size: int,
        n_classes: int,
        k_dim: int,
        m_actions: int,
        seed: int = 0,
        ood_kind: str = "iid",
    ):
        self.size = int(size)
        self.n_classes = int(n_classes)
        self.k_dim = int(k_dim)
        self.m_actions = int(m_actions)
        self.seed = int(seed)
        self.ood_kind = str(ood_kind)
        if self.ood_kind not in ("iid", "ood"):
            raise ValueError(f"unknown ood_kind={self.ood_kind!r} (expected iid|ood)")
        if self.n_classes < 2:
            raise ValueError("n_classes must be >= 2")
        if self.k_dim < 1:
            raise ValueError("k_dim must be >= 1")
        if self.m_actions < 2:
            raise ValueError("m_actions must be >= 2")

    def __len__(self) -> int:
        return self.size

    def __getitem__(self, idx: int) -> dict:
        g = random.Random(int(self.seed) + int(idx))

        h = int(g.randrange(0, int(self.n_classes)))
        if self.ood_kind == "iid":
            k_int = int(g.randrange(0, 2 ** int(self.k_dim)))
        else:
            # OOD variant: change the marginal distribution of k while preserving the same
            # action/response structure (contract-preserving).
            # We bias towards low popcount.
            k_int = int(g.randrange(0, 2 ** int(self.k_dim)))
            if int(g.randrange(0, 2)) == 0:
                k_int = k_int & 1  # keep only bit0 half the time

        ood_shift = 0

        return {
            "h": h,
            "k_int": k_int,
            "ood_shift": ood_shift,
        }

    @staticmethod
    def collate(batch: list[dict], *, k_dim: int) -> dict:
        hs = torch.tensor([int(b["h"]) for b in batch], dtype=torch.long)
        ks = torch.tensor([int(b["k_int"]) for b in batch], dtype=torch.long)
        shifts = torch.tensor([int(b["ood_shift"]) for b in batch], dtype=torch.long)
        k_bits = _int_to_bits(ks, k_dim=int(k_dim))
        return {"h": hs, "k_int": ks, "k_bits": k_bits, "ood_shift": shifts}
