#!/usr/bin/env python3
"""Check the cubic persistent-polar and polynomial-multiplier certificate."""

from probe_second_prime_intrinsic_quartic import require
from probe_second_prime_normalized_hessian import capacity


def main():
    n, d, t = 2**30, 2**26 - 1, 379125682
    e, m = n - t, 10
    labels = 2 * n + 1 - 33
    require(capacity(33, 3, t, d) - 34 * n == 28432674, "cubic interpolation")
    require(3 * (e + 1) + 3 * 4128 + 33 < 2 * n, "low-degree components")
    require(capacity(m, 5, t, d) - (m + 1) * n == 142274788, "total degree cap")

    h, weight = 214748361, 248381592
    require(m * h < labels, "divisibility")
    lower = capacity(h, 5, t, d) - (h + 1) * n
    if_heavier = capacity(h - 3, 2, t - weight - 1, d)
    require(if_heavier == 41742638856158859 < lower == 41742639225021161, "weight cap")

    polar_x = 6 * weight - 9 * d - 3
    polar_z = 6 * m - 9
    simple = labels - (5 * m - 6)
    intersection = weight - d
    defect = (2 * polar_x - 2 * intersection) * polar_z // (simple - polar_z)
    require(polar_x == 886309782 and polar_z == 51 and defect == 33, "persistent polars")
    hessian = 15 * weight - 24 * d
    order_sum = (2 * n + 3 * hessian - 8 * (2 * intersection - defect)
                 + 2 * (weight - 3 * d)) // 5
    require(order_sum == 1137312751, "branchwise singularity charge")

    mu, s = 4287, 715827867
    variables = capacity(s, 2, mu * t, d)
    order_cost = (mu - 1) * order_sum + n
    cost = (s + 1 - m) * order_cost + m * n * (mu * (mu + 1) // 2)
    require(variables - cost == 48948548771097, "strict jet surplus")
    require(3 * s + 2 * (m - 3) == 2147483615 < labels, "scalar resultant")
    require(e + 1 == 694616143, "Hamming threshold")
    print(f"weight<={weight} polar_defect<={defect} multiplicity_sum<={order_sum}")
    print(f"jet_surplus={variables-cost} scalar_degree<={3 * s + 14} labels>={labels}")
    print(f"good_errors={e} threshold_numerator>={e+1} denominator={n}")


if __name__ == "__main__":
    main()
