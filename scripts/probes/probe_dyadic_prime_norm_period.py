#!/usr/bin/env python3
"""Reconstruct two dyadic prime-norm periods with integer arithmetic."""

from dataclasses import dataclass


@dataclass(frozen=True)
class Case:
    coefficients: tuple[int, ...]
    n: int
    p: int
    g: int
    b: int
    lower: int
    ratio_num: int
    ratio_den: int


CASES = (
    Case((-1, -1, 0, 1), 256, 4283494302159617, 3800919073425889,
         4275064871947385, 223, 21, 10),
    Case((-1, 1) + (0,)*15 + (1,), 1024,
         126205134105047729256068842055334737587878534445324289139206048206460929,
         50329493603183882829305332600678170099788838530533491465177960535524808,
         100685202267360666308840825564462321244913838955279264336631534863815633,
         990, 41, 20),
)


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def multiply_by_x(values, monic):
    """Coordinates of X times a polynomial in the power basis modulo monic."""
    shift = [0] + values[:-1]
    return [a - values[-1] * b for a, b in zip(shift, monic[:-1])]


def determinant(rows):
    """Fraction-free elimination with row pivoting."""
    a = [row.copy() for row in rows]
    sign, denominator = 1, 1
    for j in range(len(a)-1):
        pivot_row = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot_row is None:
            return 0
        if pivot_row != j:
            a[j], a[pivot_row] = a[pivot_row], a[j]
            sign *= -1
        pivot = a[j][j]
        for i in range(j+1, len(a)):
            for k in range(j+1, len(a)):
                numerator = a[i][k]*pivot - a[i][j]*a[j][k]
                a[i][k], remainder = divmod(numerator, denominator)
                require(remainder == 0, "nonexact Bareiss division")
        denominator = pivot
    return sign*a[-1][-1]


def norm_one_plus_power(monic, m):
    vector = [1] + [0]*(len(monic)-2)
    for _ in range(m):
        vector = multiply_by_x(vector, monic)
    vector[0] += 1
    rows = []
    for _ in range(len(monic)-1):
        rows.append(vector)
        vector = multiply_by_x(vector, monic)
    return abs(determinant(rows))


def check(case):
    n, p, g, b = case.n, case.p, case.g, case.b
    require(norm_one_plus_power(case.coefficients, n//2) == p, "prime norm")
    require(sum(c*pow(g,i,p) for i,c in enumerate(case.coefficients))%p == 0,
            "polynomial root in the prime field")
    require(n & (n-1) == 0 and pow(g,n//2,p) == p-1, "exact dyadic order")
    require(0 < b < p and n*n <= p, "sparse nonprincipal instance")
    x, score = b, 0
    for _ in range(n):
        score += max(p*p - 20*min(x,p-x)**2, -p*p)
        x = x*g % p
    require(x == b and score > case.lower*p*p, "strict real-part certificate")
    log_upper = p.bit_length() - (n.bit_length()-1)
    require(p < n*(1 << log_upper), "binary logarithm")
    require((case.ratio_den*case.lower)**2 > case.ratio_num**2*n*log_upper,
            "logarithmic coefficient")
    print(f"n={n} p={p} bits={p.bit_length()} Re(period)>{case.lower} "
          f"ratio>{case.ratio_num}/{case.ratio_den}")


if __name__ == "__main__":
    for entry in CASES:
        check(entry)
