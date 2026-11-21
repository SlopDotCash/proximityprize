#!/usr/bin/env python3
"""Verify the integer parts of the dyadic signed-determinant period bound."""

def determinant(rows):
    """Fraction-free elimination, with row interchanges at zero pivots."""
    rows = [r.copy() for r in rows]
    sign = previous = 1
    for k in range(len(rows) - 1):
        pivot_row = next((i for i in range(k, len(rows)) if rows[i][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            rows[k], rows[pivot_row] = rows[pivot_row], rows[k]
            sign = -sign
        pivot = rows[k][k]
        for i in range(k + 1, len(rows)):
            for j in range(k + 1, len(rows)):
                num = rows[i][j] * pivot - rows[i][k] * rows[k][j]
                quotient, rem = divmod(num, previous)
                if rem:
                    raise ArithmeticError("nonexact Bareiss division")
                rows[i][j] = quotient
        previous = pivot
    return sign * rows[-1][-1]


def check_cosets(prime, dimension):
    h = next(x for x in range(1, prime) if pow(x, dimension, prime) == prime-1)
    for b in range(1, prime):
        values = [b * pow(h, i, prime) % prime for i in range(dimension)]
        for scale in (1, 2):
            if scale == 1:
                lifts = [v if v <= prime//2 else v-prime for v in values]
            else:
                lifts = [2*v-prime for v in values]
            columns = [lifts]
            for _ in range(1, dimension):
                prev = columns[-1]
                columns.append([-prev[-1], *prev[:-1]])
            det = determinant(columns)
            modulus = scale * prime
            if not det or det % modulus**(dimension-1):
                raise ArithmeticError("determinant divisibility failed")
            square_norm = sum(a*a for a in lifts)
            if det**2 > square_norm**dimension:
                raise ArithmeticError("Hadamard comparison failed")


def main():
    for d in (2, 4, 8):
        for p in (17, 97):
            check_cosets(p, d)
    n = 2**30
    for p, gap in (
        (365375409332725729550921208179070755120141565953, 14184505),
        (730750818665451459101842416358141509841924915201, 14107900),
    ):
        target = (n//32)**128
        if not gap**128 * 2*p < target < (gap+1)**128 * 2*p:
            raise ArithmeticError("production root enclosure failed")
        print(f"p={p}, uniformly |eta_b| < {n-gap} at nonzero frequencies")


if __name__ == "__main__":
    main()
