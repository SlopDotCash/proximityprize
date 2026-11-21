#!/usr/bin/env python3
"""Recompute the weighted Johnson ladder at length 2^30 and the window-free ceilings.

Exact integer transcription of the upstream `IsJohnsonWeightedCertificate` and
`johnsonWeightedRefinedExceptionCount`, as used by
`ArkLib/Research/ProximityGap/Frontier/JohnsonBudgetLadder.lean`, and of the two binomial
counts behind `ArkLib/Research/ProximityGap/Frontier/FieldUniformMcaCeilings.lean`.

    python3 probe_johnson_budget_ladder.py
    python3 probe_johnson_budget_ladder.py --search 44 48

The default run verifies every rung in the Lean table. The search mode takes budget
exponents and reports, for each prize rate, the least agreement count it finds with an
exceptional count of at most 2^beta. It scans multiplicities on a geometric grid and the
four largest admissible jet cutoffs, so smaller counts may exist off that grid.
"""

from fractions import Fraction as Fr
from math import comb, isqrt, log2
import sys

N = 2**30
RATES = (2, 4, 8, 16)

# (k, A, m, B, H, beta), copied from `JohnsonBudgetLadder.productionRungs`.
RUNGS = (
    (536870912, 809436144, 1, 1, 32, 36), (268435456, 632740718, 2, 3, 11, 36),
    (134217728, 483183820, 1, 3, 18, 36), (67108864, 364507091, 1, 4, 20, 36),
    (536870912, 800832444, 3, 4, 17, 38), (268435456, 597588455, 3, 6, 18, 38),
    (134217728, 443740243, 2, 6, 30, 38), (67108864, 326934125, 2, 9, 30, 38),
    (536870912, 787677771, 5, 7, 36, 40), (268435456, 576017749, 4, 8, 51, 40),
    (134217728, 419537945, 4, 12, 53, 40), (67108864, 305133330, 4, 16, 61, 40),
    (536870912, 771039427, 13, 18, 204, 44), (268435456, 552579357, 12, 24, 245, 44),
    (134217728, 395422598, 11, 31, 298, 44), (67108864, 282712840, 10, 41, 345, 44),
    (536870912, 764044098, 34, 48, 1167, 48), (268435456, 543143957, 31, 62, 1453, 48),
    (134217728, 385879738, 29, 82, 1722, 48), (67108864, 274060575, 26, 105, 2062, 48),
    (536870912, 761164849, 85, 120, 7331, 52), (268435456, 539364921, 80, 160, 8846, 52),
    (134217728, 382103221, 73, 207, 10717, 52), (67108864, 270660568, 67, 269, 12634, 52),
    (536870912, 760012142, 218, 308, 45353, 56), (268435456, 537861339, 202, 404, 55643, 56),
    (134217728, 380608005, 188, 532, 66224, 56), (67108864, 269317315, 171, 685, 78775, 56),
    (536870912, 759552892, 551, 779, 286038, 60),
    (268435456, 537264063, 511, 1022, 350892, 60),
    (134217728, 380015046, 470, 1330, 422581, 60),
    (67108864, 268785235, 431, 1725, 498973, 60),
    (536870912, 759370333, 1384, 1957, 1819526, 64),
    (268435456, 537026949, 1288, 2576, 2224789, 64),
    (134217728, 379779812, 1186, 3355, 2677136, 64),
    (67108864, 268574235, 1087, 4349, 3162777, 64),
    (536870912, 759269061, 8800, 12445, 73197565, 72),
    (268435456, 536895487, 8170, 16340, 89729468, 72),
    (134217728, 379649432, 7520, 21270, 108031540, 72),
    (67108864, 268457309, 6864, 27457, 128159002, 72),
    (536870912, 759253107, 55397, 78343, 2976353139, 80),
    (268435456, 536874782, 51422, 102844, 3649224462, 80),
    (134217728, 379628900, 47262, 133678, 4399911812, 80),
    (67108864, 268438896, 43530, 174121, 5172783508, 80),
    (536870912, 759250594, 353489, 499909, 119410580657, 88),
    (268435456, 536871521, 321834, 643668, 149239787421, 88),
    (134217728, 379625666, 296500, 838629, 179514362354, 88),
    (67108864, 268435997, 267250, 1069001, 215645934036, 88),
    (536870912, 759250199, 2191876, 3099780, 4789979957073, 96),
    (268435456, 536871008, 2191876, 4383752, 5483610685215, 96),
    (134217728, 379625157, 1772178, 5012477, 7684764909404, 96),
    (67108864, 268435540, 1753501, 7014005, 8231083334507, 96),
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def moments(D, A, m, B):
    """N, W, R, T in closed form; valid when D*B <= m*A, so no source width truncates."""
    u = min(B, m - 1)
    return ((B + 1) * (m * A) - D * (B * (B + 1) // 2),
            (m * A) * (B * (B + 1) // 2) - D * (B * (B + 1) * (2 * B + 1) // 6),
            (u + 1) * m - u * (u + 1) // 2,
            m * (u * (u + 1) // 2) - u * (u + 1) * (2 * u + 1) // 6)


def moments_by_sums(D, A, m, B):
    u = min(B, m - 1)
    return (sum(max(0, m * A - D * j) for j in range(B + 1)),
            sum(j * max(0, m * A - D * j) for j in range(B + 1)),
            sum(m - b for b in range(u + 1)),
            sum(b * (m - b) for b in range(u + 1)))


def certificate(n, D, A, m, B):
    """Height and cleared exception numerator of a certificate, or None."""
    if m < 1 or B < 1 or D * B >= m * A or B > 2 * D + 1 or A <= D:
        return None
    N_, W, R, T = moments(D, A, m, B)
    slope = N_ - n * R
    if slope <= 0:
        return None
    H = max(B, max(0, W - n * T) // slope)
    numerator = ((2 * B - 1) * H + (n - D - 1) * B) * (A - D) + (n - D) * (
        H + B + (2 * D - 1) * H * (2 * B - 1))
    return H, numerator


def verify():
    for D, A, m, B in ((5, 9, 3, 4), (7, 12, 4, 5), (31, 50, 6, 8), (63, 90, 2, 2), (3, 40, 9, 5)):
        require(D * B <= m * A and moments(D, A, m, B) == moments_by_sums(D, A, m, B),
                "closed moments")
    table = {}
    for k, A, m, B, H, beta in RUNGS:
        D = k - 1
        require(2 <= k <= A <= N, "ranges")
        found = certificate(N, D, A, m, B)
        require(found is not None and found[0] == H, "certificate and height")
        require(found[1] <= 2**beta * (A - D), "exception count within the budget")
        table.setdefault(beta, {})[N // k] = N - A
    print("Safe error counts at length 2^30 over every finite field with at least "
          "2^(128+beta) elements:")
    print("  beta   rate 1/2   rate 1/4   rate 1/8  rate 1/16")
    for beta in sorted(table):
        print(f"  {beta:4d}" + "".join(f"  {table[beta][den]:9d}" for den in RATES))
    johnson = [N - isqrt(N * (N // den - 1)) - 1 for den in RATES]
    print("  Johnson error counts: " + ", ".join(str(e) for e in johnson))
    for den, e in zip(RATES, johnson):
        require(0 < e - table[96][den] <= 100, "exponent 96 within 100 of Johnson")


def ceilings():
    upper_budget = 175865058349821587478617952204192862
    require(128 * upper_budget < comb(128, 66) <= 128 * (upper_budget + 1), "upper budget")
    for h, k in ((128, 64), (256, 64), (256, 32), (512, 32)):
        require(h * upper_budget < comb(h, k + 2), "lists of the budget's size")
    for h, k in ((256, 128), (256, 64), (256, 32), (512, 32)):
        require(h * (2 * (2**128 - 1) + 1) < comb(h, k + 2), "lists of size 2B + 1")
    print("Ceilings: 31/64, 95/128, 111/128, 239/256 for budgets up to "
          f"2^{log2(upper_budget):.2f}; 63/128, 95/128, 111/128, 239/256 below 2^256.")


def feasible(n, D, A, m, budget):
    top, best = (m * A - 1) // D, None
    for B in range(max(1, top - 3), top + 1):
        found = certificate(n, D, A, m, B)
        if found is not None and found[1] <= budget * (A - D):
            if best is None or found[1] < best[2]:
                best = (B, found[0], found[1])
    return best


def least_agreement(n, D, m, budget):
    low, high = D + 1, n
    if feasible(n, D, high, m, budget) is None:
        return None
    while high - low > 1:
        middle = (low + high) // 2
        low, high = (low, middle) if feasible(n, D, middle, m, budget) else (middle, high)
    return high


def search(beta):
    budget = 2**beta
    for den in RATES:
        D = N // den - 1
        cap, grid, m = max(8, 2 * isqrt(2 ** max(0, beta - 30))), [], 1
        while m <= cap:
            grid.append(m)
            m = max(m + 1, int(m * 1.25))
        best = None
        for m in grid:
            A = least_agreement(N, D, m, budget)
            if A is not None and (best is None or A < best[0]):
                best = (A, m)
        if best is None:
            print(f"beta {beta}, rate 1/{den}: no certificate found", flush=True)
            continue
        low, high = max(1, int(best[1] / 1.3)), int(best[1] * 1.3) + 2
        for m in range(low, high + 1, max(1, (high - low) // 400)):
            A = least_agreement(N, D, m, budget)
            if A is not None and A < best[0]:
                best = (A, m)
        A, m = best
        while feasible(N, D, A - 1, m, budget) is not None:
            A -= 1
        B, H, numerator = feasible(N, D, A, m, budget)
        print(f"beta {beta}, rate 1/{den}: errors {N - A}, (k, A, m, B, H) = "
              f"({D + 1}, {A}, {m}, {B}, {H}), count 2^{log2(Fr(numerator, A - D)):.4f}",
              flush=True)


def main():
    if len(sys.argv) > 2 and sys.argv[1] == "--search":
        for beta in sys.argv[2:]:
            search(int(beta))
        return
    verify()
    ceilings()


if __name__ == "__main__":
    main()
