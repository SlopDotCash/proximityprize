#!/usr/bin/env python3
"""Check the normalized Hessian and multiplier jet certificate over the second prime."""

from probe_second_prime_intrinsic_quartic import require


def capacity(total_degree, value_degree, weight, d):
    return sum(
        (total_degree + 1 - j) * max(weight - j * d, 0)
        for j in range(value_degree + 1)
    )


def main():
    n, d, t = 2**30, 2**26 - 1, 395205072
    e = n - t
    labels = 2 * n + 1 - 13

    require(capacity(13, 3, t, d) - 14 * n == 30247654, "initial cubic")
    require(3 * (e + 1) + 3 * 4128 + 13 < 2 * n, "low-degree components")
    require(capacity(7, 5, t, d) - 8 * n == 89756689, "total degree cap")
    for m in range(3, 6):
        derivative = 6 * m - 9 + 2 * d * (5 * m - 9)
        require(derivative + 13 - m < 2 * n, "small moving cubic")

    h, weight = 300000000, 231144321
    require(7 * h < labels, "divisibility of all interpolants")
    dimension = capacity(h, 5, t, d) - (h + 1) * n
    require(dimension == 87256696953767048, "dimension lower bound")
    capacity_if_larger = capacity(h - 6, 2, t - weight - 1, d)
    require(capacity_if_larger == 87256696689083760 < dimension, "weight bound")

    hessian = 15 * weight - 24 * d
    order_sum = (6 * n + hessian) // 7
    require(hessian == 1856552103 and order_sum == 1185571863, "finite intersections")

    mu, s, m = 4129, 715827875, 7
    order_cost = (mu - 1) * order_sum + n
    variables = capacity(s, 2, mu * t, d)
    cost = (s + 1 - m) * order_cost + m * n * (mu * (mu + 1) // 2)
    require(order_cost == 4895114392288, "sum of local codimensions")
    require(variables - cost == 15729676125399, "strict dimension surplus")
    require(3 * s + 2 * (m - 3) == 2147483633 < labels, "scalar resultant")
    require(e + 1 == 678536753, "threshold lower endpoint")
    print(f"weight<={weight} finite_intersections<={hessian} order_sum<={order_sum}")
    print(f"strict_surplus={variables-cost} resultant_degree<={3 * s + 8} labels>={labels}")
    print(f"good_errors={e} threshold_numerator>={e+1} denominator={n}")


if __name__ == "__main__":
    main()
