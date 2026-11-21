#!/usr/bin/env python3
"""Check common Fermat factors against the sparse-subgroup condition (python-flint)."""
from flint import fmpz


# (odd coefficient, power of two, Proth witness, binary orders of 2 and 3).
# Candidate primes were tabulated at https://mathoverflow.net/q/70548 .
LARGE = (
    (3, 41, 5, 39, 39), (21, 41, 5, 40, 40), (9, 67, 5, 64, 65),
    (5, 127, 3, 126, 127), (3, 209, 5, 208, 208), (7, 320, 3, 317, 320),
    (29, 4727, 3, 4725, 4727), (9, 9431, 5, 9429, 9430),
    (81, 12189, 5, 12186, 12188), (81, 28285, 5, 28282, 28284),
)


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def check_order(p, a, j):
    # Exact order 2^j in an odd prime field is equivalent to this single power.
    require(pow(fmpz(a), fmpz(1) << (j - 1), p) == p - 1, f"order of {a}")


def main():
    n = 1 << 26
    gcd = ((fmpz(1) << n) - 1).gcd(fmpz(3)**n - 1)
    small = ((5, 2, 2), (17, 3, 4), (257, 4, 8), (65537, 5, 16), (13631489, 19, 20))
    product = 1
    for p, j2, j3 in small:
        require(fmpz(p).is_prime(), "small prime")
        check_order(p, 2, j2)
        check_order(p, 3, j3)
        require(p < 1 << (2 * max(j2, j3)), "small-prime sparsity test")
        product *= p
    require(gcd == product, "exact gcd factorization through exponent 2^26")
    print(f"gcd at 2^26 = {gcd}; all five prime fields have p < |<2,3>|^2", flush=True)

    for k, e, witness, j2, j3 in LARGE:
        p = (fmpz(k) << e) + 1
        require(k % 2 and k < 1 << e, "Proth form")
        require(pow(fmpz(witness), (p-1)//2, p) == p-1, "Proth primality certificate")
        check_order(p, 2, j2)
        check_order(p, 3, j3)
        require(p < fmpz(1) << (2 * max(j2, j3)), "large-prime sparsity test")
        print(f"{k}*2^{e}+1 proved prime; order exponents {j2}, {j3}; dense", flush=True)


if __name__ == "__main__":
    main()
