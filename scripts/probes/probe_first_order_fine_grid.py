#!/usr/bin/env python3
"""Recompute the first-order slot certificates at reference length 4096.

Exact integer transcription of `cappedTent`, `rowSlots`, `columnSlots`, `stageStaircase`,
`firstOrderExceptionConstant` and `firstOrderListWeight`, as used by
`ArkLib/Research/ProximityGap/Frontier/FineGridFirstOrderSecurity.lean`.

    python3 probe_first_order_fine_grid.py
    python3 probe_first_order_fine_grid.py --search 2 2827 2834 100 900 4

The default run verifies both certificate tables. The search mode takes the rate
denominator, a range of agreement counts and a range and step for the multiplicity. For
each agreement count it reports the certificate with the least normalized exception bound
that it finds. The height is the least one satisfying the weighted slot inequality, so
within the scanned multiplicities the reported bound is minimal up to the step in `m`.
"""

from fractions import Fraction as Fr
from math import log2
import sys

N = 4096
RATES = (2, 4, 8, 16)

# (k, A, m, M, mu, h) at reference length 128, with the documented slot surpluses.
LEGACY = (
    ((64, 89, 43, 12, 59, 1426), 546),
    ((32, 61, 35, 15, 66, 1217), 2576),
    ((16, 42, 26, 13, 67, 1181), 2520),
    ((8, 29, 22, 13, 79, 1321), 116),
)

# (A, (m, M, mu, h), list constant C) in prize-rate order.
MAIN = (
    (2834, (116, 35, 160, 10333), 3722270),
    (1930, (112, 50, 210, 13205), 3891790),
    (1316, (108, 59, 277, 16613), 4624878),
    (901, (104, 67, 365, 22123), 5864546),
)
WIDE = (
    (2827, (824, 254, 1137, 471498), 1369562863),
    (1922, (612, 278, 1148, 360879), 649560740),
    (1308, (876, 483, 2237, 1058306), 2486297660),
    (895, (488, 321, 1705, 470485), 615760719),
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rank_bound(m, M, t):
    """sum_{s<m} min(m-s, min(t,s)+1-(t-M)) with truncated subtraction."""
    cut = max(0, t - M)
    return sum(min(m - s, max(0, min(t, s) + 1 - cut)) for s in range(m))


def capped_tent(L, w):
    """`cappedTent L w`: a tent of base L capped at height w."""
    return w * (L + 1 - w) if 2 * w <= L + 1 else (L + 1) ** 2 // 4


def closed_rank(m, M, t):
    return capped_tent(max(0, m - max(0, t - M)), min(t, M) + 1)


def row_slots(n, m, M, mu, h):
    return sum(n * closed_rank(m, M, t) * max(0, h + 1 - t) for t in range(mu + 1))


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
    for den, (A, (m, M, mu, h), C) in zip(RATES, table):
        k, rho = N // den, Fr(1, den)
        theta, T = Fr(N - k, A - k), staircase(mu, M)
        rows, columns = row_slots(N, m, M, mu, h), column_slots(k, A, m, M, mu, h)
        require(k < A <= N and M <= N and M <= mu < N, "parameter ranges")
        require(rows < columns, "slot certificate")
        require(rows >= column_slots(k, A - 1, m, M, mu, h), "one agreement fewer fails")
        require(T.denominator == 1, "integral staircase")
        bound = normalized_bound(theta, rho, mu, h, T)
        require(bound <= 2**cap_bits, "normalized exception bound")
        for b in (1, 2, 2**18):
            n = b * N
            require(exception_constant(n, b * k - 1, b * A, h, mu, M) <= bound * n * n,
                    "closed exception constant")
        require(C == -(-list_weight(k, mu, M) // (A - k)), "list constant")
        require(A * A < N * (k - 1), "below the finite Johnson agreement")
        print(f"  rate 1/{den}: radius {N - A}/{N} = {(N - A) / N:.6f}, "
              f"(m, M, mu, h) = {(m, M, mu, h)}, surplus {columns - rows}, "
              f"Theta = {theta}, T = {T}, bound 2^{log2(bound):.2f} n^2, list at most {C} n")


def cheapest(k, A, m, caps):
    """Least normalized bound over the caps M and every truncation mu, in floats."""
    import numpy as np

    rho, theta = k / N, (N - k) / (A - k)
    last = (m * A) // k + 1
    t = np.arange(last + 1, dtype=np.float64)
    best = None
    for M in caps:
        w = np.minimum(t, M) + 1
        L = np.maximum(0.0, m - np.maximum(0.0, t - M))
        tent = np.where(2 * w <= L + 1, w * (L + 1 - w), np.floor((L + 1) ** 2 / 4))
        net = w * np.maximum(0.0, m * A - k * t) - N * tent
        partial, moment = np.cumsum(net), np.cumsum(net * t)
        usable = (partial > 0) & (t >= M)
        if not usable.any():
            continue
        mu = t[usable]
        h = np.maximum(np.floor(moment[usable] / partial[usable]) + 1, mu)
        T = (mu - M) * M * (M + 1) + M * (M + 1) * (2 * M + 1) / 6
        bound = ((2 * mu - 1) * h + theta * (h + mu) + 4 * theta * rho * mu * h + mu
                 + 8 * rho * theta**2 * T + 24 * rho**2 * h * theta**2 * T
                 + 4 * rho * theta * T)
        i = int(np.argmin(bound))
        candidate = (float(bound[i]), M, int(mu[i]), int(h[i]))
        if best is None or candidate < best:
            best = candidate
    return best


def search(den, low, high, m_low, m_high, m_step):
    k, rho = N // den, Fr(1, den)
    for A in range(low, high + 1):
        best = None
        for m in range(m_low, m_high + 1, m_step):
            found = cheapest(k, A, m, range(1, m + 1, max(1, m // 60)))
            if found is None:
                continue
            width = max(1, m // 60)
            found = cheapest(k, A, m, range(max(1, found[1] - width), found[1] + width + 1))
            if best is None or found[0] < best[0]:
                best = found + (m,)
        if best is None:
            print(f"A = {A}: no certificate in the scanned range", flush=True)
            continue
        _, M, mu, h, m = best
        while row_slots(N, m, M, mu, h) >= column_slots(k, A, m, M, mu, h):
            h += 1  # repair float rounding in the least height
        bound = normalized_bound(Fr(N - k, A - k), rho, mu, h, staircase(mu, M))
        print(f"A = {A}: radius {N - A}/{N}, (m, M, mu, h) = {(m, M, mu, h)}, "
              f"bound 2^{log2(bound):.2f} n^2", flush=True)


def main():
    if len(sys.argv) == 8 and sys.argv[1] == "--search":
        search(*(int(x) for x in sys.argv[2:]))
        return
    for m in range(1, 31):
        for M in range(0, 35):
            for t in range(0, 70):
                require(closed_rank(m, M, t) == rank_bound(m, M, t), "closed rank profile")
    for (k, A, m, M, mu, h), surplus in LEGACY:
        require(column_slots(k, A, m, M, mu, h) - row_slots(128, m, M, mu, h) == surplus,
                "length-128 surplus")
    print("Closed rank profile and length-128 surpluses 546, 2576, 2520, 116 reproduced.")
    verify("Field size at least 2^165 n^2", MAIN, 37)
    verify("Field size at least 2^180 n^2", WIDE, 52)


if __name__ == "__main__":
    main()
