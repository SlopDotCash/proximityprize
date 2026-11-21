#!/usr/bin/env python3
"""Check both terminal cubic cases and the denominator-free multiplier dimensions."""

from probe_second_prime_intrinsic_quartic import require
from probe_second_prime_normalized_hessian import capacity


def main():
    n, d, t, m = 2**30, 2**26 - 1, 357913943, 34
    e = n - t
    labels = 2 * n + 1 - (e + 1) - m
    require(labels == 1431655733, "cubic component population")
    h, weight = 2**25, 290805098
    require(m * h < labels, "all window interpolants are multiples")
    lower = capacity(h, 5, t, d) - (h + 1) * n
    require(capacity(h - 3, 2, t - weight - 1, d) < lower, "weight cap")

    eta, s, power = 12000000, 400000000, 40
    polar_x = 6 * weight - 9 * d - 3
    polar_z = 6 * m - 9
    dimension = (3 * power + 3) * power * (polar_x + weight)
    require(polar_x == 1140850818 and dimension == 7043747106720, "raw matrix size")
    require(power * (3 * d - d) > 2 * d and s >= power * polar_z, "source ranges")
    low_surplus = (s + 1) * (power * eta - 3 * d) - power * polar_z * dimension
    require(low_surplus == 56528137246257411, "Jacobian-power surplus")
    require(3 * s + 2 * m == 1200000068 < labels - (5 * m - 6), "simple labels")

    order_sum = (23 * weight - 54 * d + 8 * eta) // 3
    require(order_sum == 1053546217, "large polar degree forces small jet cost")
    mu = 64
    variables = capacity(s, 2, mu * t, d)
    cost = (s + 1 - m) * ((mu - 1) * order_sum + n) + m * n * (mu * (mu + 1) // 2)
    require(variables - cost == 428325079668489781, "intrinsic jet surplus")
    require(3 * s + 2 * (m - 3) < labels, "all component labels")
    print(f"weight<={weight} labels>={labels} low_jacobian_surplus={low_surplus}")
    print(f"large_jacobian_order_sum<={order_sum} high_jet_surplus={variables-cost}")
    print(f"ruled_out=irreducible-value-cubic errors={e} length={n}")


if __name__ == "__main__":
    main()
