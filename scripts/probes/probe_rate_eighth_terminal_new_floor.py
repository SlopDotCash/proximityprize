"""Exact arithmetic for the rate-eighth second-prime safety bound."""

from fractions import Fraction

N = 2**30
D = N // 8 - 1
T = 417_685_570
ERRORS = N - T
FIRST = 4170
SECOND = 63
WEIGHT = 3 * T - 1
PARAMETERS = {
    # value degree: (Jacobian power, received jet order, scalar degree)
    2: (12, 1024, 20_000_000),
    3: (7, 256, 8_000_000),
    4: (6, 512, 8_000_000),
    5: (7, 128, 18_000_000),
    6: (8, 128, 34_000_000),
    7: (10, 128, 81_000_000),
    8: (12, 1024, 168_000_000),
}


def ceil_div(a, b):
    return (a + b - 1) // b


def interpolant_surplus(multiplicity, ordinate_degree, total_degree):
    columns = sum(
        (total_degree - j + 1) * max(0, multiplicity * T - j * D)
        for j in range(ordinate_degree + 1)
    )
    rows = sum((multiplicity - j) * (total_degree - j + 1) for j in range(multiplicity))
    return columns - rows * N


def nonhead_cap(b, a, mu, s):
    # Lower bound for 5(tW/d-R), as a convex quadratic in W.
    A = Fraction(8) - Fraction(4, a)
    B = Fraction(5 * T, D) - 18 * b - 1
    C = (9 * b * b - b) * D - (2 + Fraction(8, a)) * N
    x = max(b * D, min(-B * D / (2 * A), WEIGHT))
    gap = (A * x * x / D + B * x + C) / 5
    high_y = (mu * T - 1) // D
    assert s > high_y and mu * T >= WEIGHT
    assert a * (b * D - D) >= b * D
    high_slack = (s - high_y + 1) * (mu * gap - Fraction(WEIGHT**2, 2 * D))
    high_slack -= high_y * mu * b * N + SECOND * N * mu * (mu + 1) // 2
    assert high_slack > 0, (b, "high polar", high_slack)

    norm_degree = 2 * b * WEIGHT - b * b * D - b
    norm_height = 2 * b * SECOND - b * b
    low_y = ceil_div(a * (WEIGHT - D), D)
    v = max(b * a + b - 1, low_y)
    columns = (v + 1) * a * (norm_degree + WEIGHT)
    low_slack = (s + 1) * N - a * norm_height * columns
    assert low_slack > 0, (b, "low polar", low_slack)
    # m is a total scalar/value degree. The discriminant costs at most
    # (2b-1)m-b^2 scalar exceptions.
    exceptions = (2 * b - 1) * SECOND - b * b
    cap = max(FIRST * SECOND, b * s + SECOND * high_y, b * s + SECOND * low_y + exceptions)
    return cap


def main():
    assert interpolant_surplus(3, 8, FIRST) > 0
    assert interpolant_surplus(4, 12, SECOND) > 0
    # A value-linear component containing more than FIRST*SECOND sections
    # has scalar/value degree at most SECOND; the 4096-point secant test applies.
    sample = 4096
    ident = Fraction(sample * T - SECOND * N, sample - SECOND)
    assert ident * (1 - Fraction(3 * (SECOND - 1), sample - SECOND)) > D
    assert FIRST * SECOND > sample
    small_head = ERRORS // 512 + 1
    assert small_head >= FIRST * SECOND
    caps = {1: small_head}
    for b, params in PARAMETERS.items():
        caps[b] = nonhead_cap(b, *params)
    # At most eight ordinate degree units can be distributed among the factors.
    # Include unused degree slots through the zero initialization.
    total = [0]
    for k in range(1, 9):
        total.append(max(total[k - b] + caps[b] for b in range(1, k + 1)))
    core = T - 511
    assert 4 * core > N + 4 * D
    for j in range(9):
        if j <= 3:
            covered = j * (ERRORS + 1)
        else:
            U = ceil_div(j * core * core, core + (j - 1) * D)
            covered = j * N - (j - 1) * U
        all_labels = FIRST + total[8-j] + covered
        assert all_labels <= 2 * N, (j, all_labels)
        print(f"{j} large heads: at most {all_labels:,} labels")
    print("Component caps", caps)
    print("Safe errors", f"{ERRORS:,}", "first failure at least", f"{ERRORS+1:,}")


if __name__ == "__main__":
    main()
