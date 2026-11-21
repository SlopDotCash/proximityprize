#!/usr/bin/env python3
"""Verify dimensions and strict resultant bounds for the cubic incidence floor."""

from probe_second_prime_intrinsic_quartic import require


def capacity(h, v, d):
    return sum((h - j + 1) * (v - j * d) for j in range(min(h, (v - 1) // d) + 1))


def main():
    n, d, t = 2**30, 2**26 - 1, 396013787
    b, m = 3, 13
    e = n - t
    labels = 2 * n + 1 - m
    cubic_gap = sum((m - j + 1) * (t - j * d) for j in range(b + 1)) - (m + 1) * n
    require(cubic_gap == 70683404, "first interpolant")
    require(e + 1 > 4128 and 3 * (e + 1) + m < 2 * n, "all lower factors")

    h, weight = 2**27, 230335609
    require(labels > h * m, "divisibility of the entire interpolation space")
    dim = capacity(h, t, d) - (h + 1) * n
    require(capacity(h - b, t - weight - 1, d) < dim
            <= capacity(h - b, t - weight, d), "sharp factor weight bound")
    require(b * d <= weight, "leading weight")
    reverse = (6 * b - 2) * weight - 3 * b * b * d
    multiplicities = (6 * n + reverse) // 7
    require(multiplicities == 1187983055, "local reverse intersections")

    s, mu = 715000000, 3000
    jet = mu * (mu + 1) // 2
    codimension = (mu - 1) * multiplicities + n
    variables = sum((s - j + 1) * (mu * t - j * d) for j in range(b))
    cost = (s + 1 - m) * codimension + m * n * jet
    require(variables - cost == 8270513734954, "strict polynomial jet surplus")
    scalar_degree = b * s + (b - 1) * (m - b)
    require(scalar_degree == 2145000020 < labels, "scalar resultant")
    require(e + 1 == 677728038, "Hamming step")
    print(f"agreement={t}  good_error_count={e}  radius_numerator={e + 1}")
    print(f"weight<={weight}  multiplicity_sum<={multiplicities}")
    print(f"variables={variables}  cost<={cost}  scalar_degree<={scalar_degree}")


if __name__ == "__main__":
    main()
