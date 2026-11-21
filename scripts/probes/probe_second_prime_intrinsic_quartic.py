#!/usr/bin/env python3
"""Verify the integer inequalities excluding the second-prime quartic factor."""


def capacity(total_degree, strict_weight, d):
    return sum(
        (total_degree - j + 1) * max(strict_weight - j * d, 0)
        for j in range(total_degree + 1)
    )


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def main():
    n = 2**30
    d = 2**26 - 1
    t = (n - 1) // 3 + 2
    b, m, h = 4, 34, 119
    labels = 2 * n + 1 - m
    require(labels > h * m and t == 357913943, "initial witness and Bézout bounds")

    section_dimension = capacity(h, t, d) - (h + 1) * n
    weight = 302954072
    require(capacity(h - b, t - weight - 1, d) < section_dimension
            <= capacity(h - b, t - weight, d), "maximum possible weight")
    require(section_dimension == 6375345000 and weight >= b * d, "factor capacity")

    reverse_degree = (6 * b - 2) * weight - 3 * b * b * d
    require(all(r * (3 * r - 2) >= 7 * r - 6 for r in range(1, b + 1)),
            "intersection multiplicity")
    multiplicity_sum = (reverse_degree + 6 * n) // 7
    require(reverse_degree == 3443764160 and multiplicity_sum == 1412316443,
            "reverse resultant bounds")

    mu, s, loss = 64, 2**26, 2**19
    jet_dimension = mu * (mu + 1) // 2
    require(mu * (t - loss) > (b - 1) * d and s >= b - 1,
            "all variable ranges nonempty")
    variables = sum(
        (s - j + 1) * (mu * (t - loss) - j * d) for j in range(b)
    )
    constraints = mu * multiplicity_sum * (s + m * jet_dimension + 1)
    require(variables - constraints == 40640596161682872, "strict dimension surplus")

    outliers = m * (jet_dimension + 1) * n // (loss + 1)
    retained = labels - outliers
    scalar_degree = b * s + (b - 1) * (m - b)
    require(outliers == 144903915 and retained == 2002579700, "exceptional incidences")
    require(retained > scalar_degree == 268435546, "strict scalar resultant bound")
    print(f"t={t}  W<={weight}  sum(r_x)<={multiplicity_sum}")
    print(f"variables={variables}  constraints<={constraints}")
    print(f"retained>={retained}  resultant_degree<={scalar_degree}")


if __name__ == "__main__":
    main()
