from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Partition:
    """
    Partition over a finite carrier X = {0..n-1}, represented by a class id per element.

    Invariant: labels are normalized (0..k-1) in first-occurrence order.
    """

    n: int
    cls: tuple[int, ...]

    def __post_init__(self) -> None:
        if int(self.n) < 0:
            raise ValueError("n must be >= 0")
        if len(self.cls) != int(self.n):
            raise ValueError("cls length must equal n")
        for c in self.cls:
            if int(c) < 0:
                raise ValueError("class ids must be >= 0")

    @staticmethod
    def from_labels(labels: list[int]) -> "Partition":
        n = int(len(labels))
        mp: dict[int, int] = {}
        out: list[int] = []
        nxt = 0
        for x in labels:
            x = int(x)
            if x not in mp:
                mp[x] = nxt
                nxt += 1
            out.append(int(mp[x]))
        return Partition(n=n, cls=tuple(out))

    @staticmethod
    def from_map(*, n: int, f) -> "Partition":
        labels = [f(i) for i in range(int(n))]
        return Partition.from_labels([int(x) for x in labels])

    def meet(self, other: "Partition") -> "Partition":
        """
        Meet of partitions (finer): class id is the pair (self.cls[i], other.cls[i]).
        """
        if int(self.n) != int(other.n):
            raise ValueError("meet requires same carrier size")
        pairs = [(int(self.cls[i]), int(other.cls[i])) for i in range(int(self.n))]
        mp: dict[tuple[int, int], int] = {}
        out: list[int] = []
        nxt = 0
        for p in pairs:
            if p not in mp:
                mp[p] = nxt
                nxt += 1
            out.append(int(mp[p]))
        return Partition(n=int(self.n), cls=tuple(out))

    def leq(self, other: "Partition") -> bool:
        """
        Order: self ≤ other means self is finer (refines other):
        i ~_self j => i ~_other j
        """
        if int(self.n) != int(other.n):
            raise ValueError("leq requires same carrier size")
        # For each self-class, ensure other-class is constant.
        rep_other: dict[int, int] = {}
        for i in range(int(self.n)):
            a = int(self.cls[i])
            b = int(other.cls[i])
            if a in rep_other:
                if int(rep_other[a]) != b:
                    return False
            else:
                rep_other[a] = b
        return True


def delta_pairs(*, n: int) -> list[tuple[int, int]]:
    """
    Unordered distinctions ΔX as ordered pairs (i,j) with i<j.
    """
    out: list[tuple[int, int]] = []
    for i in range(int(n)):
        for j in range(i + 1, int(n)):
            out.append((i, j))
    return out


def confusions_of_partition(E: Partition) -> set[tuple[int, int]]:
    """
    C_E ⊆ ΔX: pairs {i,j} confounded by E, represented as (i,j) with i<j.
    """
    n = int(E.n)
    out: set[tuple[int, int]] = set()
    for i in range(n):
        ci = int(E.cls[i])
        for j in range(i + 1, n):
            if ci == int(E.cls[j]):
                out.add((i, j))
    return out


def required_distinctions(*, n: int, sigma) -> set[tuple[int, int]]:
    """
    R_σ ⊆ ΔX: pairs distinguished by sigma.
    """
    out: set[tuple[int, int]] = set()
    for i in range(int(n)):
        si = sigma(i)
        for j in range(i + 1, int(n)):
            if si != sigma(j):
                out.add((i, j))
    return out


def loss_set(*, R_sigma: set[tuple[int, int]], C_E: set[tuple[int, int]]) -> set[tuple[int, int]]:
    """
    L_σ(E) := R_σ ∩ C_E
    """
    return set(R_sigma.intersection(C_E))


def residual_loss(*, losses: list[set[tuple[int, int]]], R_sigma: set[tuple[int, int]]) -> set[tuple[int, int]]:
    """
    L_res(I) = ⋂_i L_i (intersection over a non-empty family).
    Convention: if losses empty, residual is R_sigma (no interface information).
    """
    if not losses:
        return set(R_sigma)
    cur = set(losses[0])
    for L in losses[1:]:
        cur.intersection_update(L)
    return cur


def rho(L_res: set[tuple[int, int]]) -> int:
    return int(len(L_res))


def delta_gain(*, L_res: set[tuple[int, int]], L_j: set[tuple[int, int]], R_sigma: set[tuple[int, int]]) -> int:
    """
    Δ_j(I) := #(L_res(I) ∩ A_j) where A_j := R_sigma \\ L_j.
    Equivalent: # (L_res \\ L_j)
    """
    return int(len(set(L_res.difference(L_j))))


def greedy_select(
    *,
    R_sigma: set[tuple[int, int]],
    losses_by_view: list[set[tuple[int, int]]],
    max_steps: int,
) -> list[int]:
    """
    Greedy policy: iteratively pick the view that maximizes Δ.
    Returns selected view indices.
    """
    if int(max_steps) < 0:
        raise ValueError("max_steps must be >= 0")
    chosen: list[int] = []
    cur_losses: list[set[tuple[int, int]]] = []
    for _t in range(int(max_steps)):
        L_res = residual_loss(losses=cur_losses, R_sigma=R_sigma)
        if len(L_res) == 0:
            break
        best_j = None
        best_gain = -1
        for j, L_j in enumerate(losses_by_view):
            if j in chosen:
                continue
            g = delta_gain(L_res=L_res, L_j=L_j, R_sigma=R_sigma)
            if g > best_gain:
                best_gain = g
                best_j = j
        if best_j is None:
            break
        chosen.append(int(best_j))
        cur_losses.append(set(losses_by_view[int(best_j)]))
    return chosen
