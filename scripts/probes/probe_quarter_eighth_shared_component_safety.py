"""Exact received-jet, Jacobian-power, and common-resultant certificates."""

from dataclasses import dataclass
from fractions import Fraction

N = 2**30


@dataclass(frozen=True)
class Instance:
    rate_denominator: int
    agreements: int
    first_y: int
    first_total: int
    second_y: int
    second_total: int
    # Each row lists Jacobian exponent, jet multiplicity, scalar cap, and 4 beta.
    parameters: tuple


CASES = (
    Instance(4, 575218846, 6, 28150537, 12, 41, (
        (5, 256, 3270000, 1), (6, 256, 5230000, 2),
        (10, 512, 14630000, 5), (17, 512, 53130000, 9),
        (29, 2048, 328390000, 10))),
    Instance(8, 417566306, 8, 11711847, 18, 51, (
        (5, 512, 4590000, 1), (5, 128, 4500000, 2),
        (6, 512, 6240000, 4), (7, 256, 11080000, 5),
        (8, 256, 21400000, 5), (11, 256, 48650000, 7),
        (16, 512, 112670000, 11))),
)


def ceil_div(x, y):
    return (x + y - 1) // y


def interpolant_surplus(d, t, mu, b, h):
    columns = sum((h - j + 1) * max(mu * t - j * d, 0) for j in range(b + 1))
    rows = N * sum((mu - j) * (h - j + 1) for j in range(mu))
    return columns - rows


def component_cap(b, d, t, m, row):
    a, mu, s, beta4 = row
    reserve = Fraction(beta4, 4)
    W = 3 * t - 1
    assert b * d <= W and a * (b - 1) >= b and mu * t >= W
    A = 8 - Fraction(4, a)
    B = Fraction(5 * t, d) - 18 * b - 1
    C = (9 * b * b - b) * d - (2 + 8 * reserve / a) * N
    x = max(b * d, min(-B * d / (2 * A), W))
    gap = (A * x * x / d + B * x + C) / 5
    jmax = (mu * t - 1) // d
    assert s > jmax
    assert (s - jmax + 1) * (mu * gap - Fraction(W**2, 2 * d)) > (
        jmax * mu * b * N + m * N * mu * (mu + 1) // 2)

    D = 2 * b * W - b * b * d - b
    H = 2 * b * m - b * b
    y = ceil_div(a * (W - d), d)
    v = max(b * a + b - 1, y)
    assert (s + 1) * reserve * N > a * H * (v + 1) * a * (D + W)
    nonsimple = (2 * b - 1) * m - b * b
    return b * s + max(m * jmax, m * y + nonsimple)


def check(case):
    t, h, m = case.agreements, case.first_total, case.second_total
    d, e = N // case.rate_denominator - 1, N - t
    bmax, companion_y = case.first_y, case.second_y
    surpluses = (interpolant_surplus(d, t, 3, bmax, h),
                 interpolant_surplus(d, t, 6, companion_y, m))
    assert min(surpluses) > 0 and h >= bmax and m >= companion_y
    first_core = t - 511
    assert 4 * first_core > N + 4 * d
    # On a small scalar-degree factor, a 4096-point sample forces an affine head.
    nlines = 4096
    identity = Fraction(nlines * t - m * N, nlines - m)
    assert identity * (1 - Fraction(3 * (m - 1), nlines - m)) > d
    caps = [0, e // 512 + 1]
    assert caps[1] >= nlines
    for b, row in enumerate(case.parameters, start=2):
        caps.append(component_cap(b, d, t, m, row))
    assert len(caps) == bmax + 1
    slots = [0]
    for c in range(1, bmax + 1):
        slots.append(max(slots[c - i] + caps[i] for i in range(1, c + 1)))
    bounds = []
    for c in range(bmax + 1):
        residual = (bmax - c) * (m - c) + (companion_y - c) * (h - c)
        for j in range(c + 1):
            if j <= 3:
                heads = j * (e + 1)
            else:
                union = ceil_div(j * first_core**2, first_core + (j - 1) * d)
                heads = j * N - (j - 1) * union
            bounds.append((m + residual + heads + slots[c - j], j, c))
    total, heads, common_degree = max(bounds)
    assert total <= 2 * N
    print(f"Rate 1/{case.rate_denominator}: safe through {e:,}; maximum {total:,} "
          f"at {heads} large heads and common Y-degree {common_degree}.")
    print("Interpolation surpluses", surpluses, "and component caps", caps[1:])


if __name__ == "__main__":
    for instance in CASES:
        check(instance)
