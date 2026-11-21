#!/usr/bin/env python3
"""Check four punctured coset complements by rank over a prime field.

The unknowns are the coefficients of the differences P_i-P_0, 1 <= i <= 3.
At every retained point the three heads other than its own coset must agree.
There is only a common head exactly when the constraint matrix has full rank.
"""

from itertools import combinations


def dimension(p, groups, holes):
    width = 2 * len(groups[0])
    pivots = {}
    for group_index, group in enumerate(groups):
        retained_heads = [i for i in range(4) if i != group_index]
        for x in group:
            if x in holes:
                continue
            powers = [pow(x, j, p) for j in range(width)]
            for i in retained_heads[1:]:
                row = [0] * (3 * width)
                for head, sign in ((i, 1), (retained_heads[0], -1)):
                    if head:
                        start = (head - 1) * width
                        row[start:start + width] = [sign * y % p for y in powers]
                for col in sorted(pivots):
                    if row[col]:
                        multiple = row[col]
                        row = [(v - multiple * w) % p for v, w in zip(row, pivots[col])]
                lead = next((j for j, v in enumerate(row) if v), None)
                if lead is not None:
                    inv = pow(row[lead], -1, p)
                    pivots[lead] = [v * inv % p for v in row]
    return 3 * width - len(pivots)


def check(p, g, n):
    m = n // 4
    if pow(g, n, p) != 1 or len({pow(g, i, p) for i in range(n)}) != n:
        raise ValueError("invalid domain")
    groups = [[pow(g, 4 * i + j, p) for i in range(m)] for j in range(4)]
    domain = sum(groups, [])
    total = 0
    for count in range(m + 1):
        for holes in combinations(domain, count):
            if dimension(p, groups, set(holes)):
                raise ArithmeticError(f"unexpected four-head solution at {p=}, {holes=}")
            total += 1
    # Erase m+1 coordinates outside the first fiber. Its lone head may
    # differ by the locator of the 2m-1 remaining off-fiber coordinates.
    if not dimension(p, groups, set((groups[1] + groups[2])[:m+1])):
        raise ArithmeticError("the sharp boundary example was missed")
    print(f"p={p} n={n} dimension={2*m} puncturings={total} nonconstant_head_families=0")


if __name__ == "__main__":
    check(17, 2, 8)
    check(13, 2, 12)
    check(17, 3, 16)
    check(97, 8, 16)
