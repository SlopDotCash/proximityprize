#!/usr/bin/env python3
"""Recompute the first-order slot certificates at reference length 4096.

Exact integer transcription of `rowSlots`, `columnSlots`, `stageStaircase`,
`firstOrderExceptionConstant` and `firstOrderListWeight`, as used by
`ArkLib/Research/ProximityGap/Frontier/FineGridFirstOrderSecurity.lean`.

    python3 probe_first_order_fine_grid.py            # verify the stated certificates
    python3 probe_first_order_fine_grid.py --search 37 86
    python3 probe_first_order_fine_grid.py --search 57 170

The search mode walks a coarse parameter grid under a cap on the limiting exception
constant and a cap on the multiplicity. It reproduces the two parameter tables below.
It is not exhaustive, so smaller agreement counts may exist off its grid.
"""

from fractions import Fraction as Fr
from math import log2
import sys

N = 4096
RATES = ((1, 2), (1, 4), (1, 8), (1, 16))

# (k, A, m, M, mu, h) at reference length 128, with the documented slot surpluses.
LEGACY = (
    ((64, 89, 43, 12, 59, 1426), 546),
    ((32, 61, 35, 15, 66, 1217), 2576),
    ((16, 42, 26, 13, 67, 1181), 2520),
    ((8, 29, 22, 13, 79, 1321), 116),
)

# (A, (m, M, mu, h), Theta, staircase bound T, list constant C) in prize-rate order.
MAIN = (
    (2836, (86, 24, 215, 17200), Fr(13, 5), 119500, 5146851),
    (1932, (86, 39, 172, 13760), Fr(17, 5), 228020, 2056867),
    (1318, (86, 47, 215, 17200), Fr(9, 2), 414728, 2200781),
    (902, (86, 60, 387, 30960), Fr(6), 1270630, 6075100),
)
WIDE = (
    (2831, (170, 54, 612, 48960), Fr(21, 8), 1711215, 96741451),
    (1926, (170, 76, 935, 74800), Fr(7, 2), 5176094, 138925816),
    (1313, (170, 94, 510, 40800), Fr(9, 2), 3996175, 25849285),
    (899, (170, 102, 612, 48960), Fr(6), 5717015, 25632097),
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rank_bound(m, M, t):
    """sum_{s<m} min(m-s, min(t,s)+1-(t-M)) with truncated subtraction."""
    cut = max(0, t - M)
    return sum(min(m - s, max(0, min(t, s) + 1 - cut)) for s in range(m))


def row_slots(n, m, M, mu, h):
    return sum(n * rank_bound(m, M, t) * max(0, h + 1 - t) for t in range(mu + 1))


def column_slots(k, A, m, M, mu, h):
    return sum((min(t, M) + 1) * max(0, m * A - k * t) * max(0, h + 1 - t)
               for t in range(mu + 1))


def staircase(mu, M):
    return Fr(max(0, mu - M) * M * (M + 1)) + Fr(M * (M + 1) * (2 * M + 1), 6)


def exception_constant(n, D, A, h, mu, M):
    """`firstOrderExceptionConstant` at the agreement-incidence ratio, for mu > 0."""
    theta, T, rest = Fr(n - D, A - D), staircase(mu, M), max(0, n - D - 1)
    tail = (2 * mu - 1) * h + theta * (h + mu + 4 * D * mu * h) + rest * mu
    return tail + (24 * D * D * h + 8 * D) * theta**2 * T + 4 * D * rest * theta * T


def normalized_bound(theta, rho, mu, h, T):
    """The multiple of n^2 proved by `exception_le`."""
    return ((2 * mu - 1) * h + theta * (h + mu)
            + (4 * theta * rho * mu * h + mu + 8 * rho * theta**2 * T)
            + (24 * rho**2 * h * theta**2 * T + 4 * rho * theta * T))


def list_weight(K, mu, M):
    """`firstOrderListWeight K mu M`."""
    weight = 0
    while mu > 0:
        if M == 0:
            weight += mu
        else:
            weight += mu * (1 + 2 * K * (mu - 1))
            M -= 1
        mu -= 1
    return weight


def verify(label, table, cap_bits):
    print(f"{label}: exception constant at most 2^{cap_bits} n^2")
    for (num, den), (A, (m, M, mu, h), theta, T, C) in zip(RATES, table):
        k, rho = N * num // den, Fr(num, den)
        rows, columns = row_slots(N, m, M, mu, h), column_slots(k, A, m, M, mu, h)
        require(k < A <= N and M <= N and mu < N, "parameter ranges")
        require(rows < columns, "slot certificate")
        require(rows >= column_slots(k, A - 1, m, M, mu, h), "one agreement fewer fails")
        require(N - k <= theta * (A - k) and theta >= 1, "incidence ratio")
        require(staircase(mu, M) <= T, "staircase")
        bound = normalized_bound(theta, rho, mu, h, T)
        require(bound <= 2**cap_bits, "normalized exception bound")
        for b in (1, 2, 2**18):
            n = b * N
            require(exception_constant(n, b * k - 1, b * A, h, mu, M) <= bound * n * n,
                    "closed exception constant")
        weight = list_weight(k, mu, M)
        require(C == -(-weight // (A - k)), "list constant")
        require(A * A < N * (k - 1), "below the finite Johnson agreement")
        print(f"  rate {num}/{den}: radius {N - A}/{N} = {(N - A) / N:.5f}, "
              f"(m, M, mu, h) = {(m, M, mu, h)}, surplus {columns - rows}, "
              f"bound 2^{log2(bound):.2f} n^2, list at most {C} n")


def minimal_agreement(k, m, M, mu, h, ranks):
    heights = [max(0, h + 1 - t) for t in range(mu + 1)]
    rows = N * sum(r * w for r, w in zip(ranks, heights))

    def passes(A):
        return rows < sum((min(t, M) + 1) * max(0, m * A - k * t) * heights[t]
                          for t in range(mu + 1))

    if not passes(N):
        return None
    low, high = k, N
    while high - low > 1:
        middle = (low + high) // 2
        low, high = (low, middle) if passes(middle) else (middle, high)
    return high


def limiting_cost(rho, A, h, mu, M):
    theta, T = (1 - rho) / (Fr(A, N) - rho), staircase(mu, M)
    return (24 * rho**2 * h * theta**2 * T + 4 * rho * (1 - rho) * theta * T
            + 4 * rho * theta * mu * h)


def search(cap_bits, max_multiplicity):
    multiplicities = [m for m in (12, 16, 20, 24, 28, 32, 36, 43, 50, 60, 72, 86, 100,
                                  120, 140, 170) if m <= max_multiplicity]
    for num, den in RATES:
        k, rho, best = N * num // den, Fr(num, den), None
        for m in multiplicities:
            caps = sorted({max(1, round(f * m)) for f in
                           (0.2, 0.25, 0.28, 0.32, 0.36, 0.4, 0.45, 0.5, 0.55, 0.6, 0.7)})
            for M in caps:
                jets = sorted({max(M, round(f * m)) for f in
                               (1.0, 1.2, 1.37, 1.6, 2.0, 2.5, 3.0, 3.6, 4.5, 5.5)})
                for mu in jets:
                    ranks = [rank_bound(m, M, t) for t in range(mu + 1)]
                    for h in sorted({int(f * mu) for f in (2, 3, 4, 6, 9, 14, 24, 40, 80)}):
                        A = minimal_agreement(k, m, M, mu, h, ranks)
                        if A is None:
                            continue
                        cost = limiting_cost(rho, A, h, mu, M)
                        if cost > 2**cap_bits:
                            continue
                        if best is None or (A, cost) < best[:2]:
                            best = (A, cost, (m, M, mu, h))
        A, cost, parameters = best
        print(f"rate {num}/{den}: agreement {A}/{N}, radius {N - A}/{N}, "
              f"(m, M, mu, h) = {parameters}, limiting cost 2^{log2(cost):.2f} n^2",
              flush=True)


def main():
    if len(sys.argv) == 4 and sys.argv[1] == "--search":
        search(int(sys.argv[2]), int(sys.argv[3]))
        return
    for (k, A, m, M, mu, h), surplus in LEGACY:
        require(column_slots(k, A, m, M, mu, h) - row_slots(128, m, M, mu, h) == surplus,
                "length-128 surplus")
    print("Length-128 surpluses 546, 2576, 2520, 116 reproduced.")
    verify("Field size at least 2^165 n^2", MAIN, 37)
    verify("Field size at least 2^171 n^2", WIDE, 43)


if __name__ == "__main__":
    main()
