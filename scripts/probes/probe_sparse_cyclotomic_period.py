#!/usr/bin/env python3
"""Exact real-part certificate for a Gaussian period at Phi_36960(2)."""

from collections import Counter
from fractions import Fraction as F
from functools import cache
from math import factorial, isqrt
from pathlib import Path
import argparse
import configparser
import hashlib


@cache
def cyclotomic_at_two(n):
    """Compute Phi_n(2) from the product over all divisors."""
    value = 2**n - 1
    for d in range(1, isqrt(n) + 1):
        if n % d:
            continue
        for index in {d, n // d} - {n}:
            value, rem = divmod(value, cyclotomic_at_two(index))
            if rem:
                raise ArithmeticError("nonintegral cyclotomic factor")
    return value


def check(condition, message):
    if not condition:
        raise ArithmeticError(message)


def cos_lower(upper):
    """Lower bound for cos(2*pi*x) on 0 <= x <= upper <= 1/2."""
    # Classical rational bounds 333/106 < pi < 355/113.
    argument_lo = 2 * F(333, 106) * upper
    argument_hi = 2 * F(355, 113) * upper
    return sum((-1)**j * (argument_lo if j % 2 == 0 else argument_hi)**(2*j)
               / factorial(2*j) for j in range(6))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, default=Path(__file__).resolve().parent
                        / "certificates" / "phi36960-primo.cert", help="PRIMO certificate to bind")
    args = parser.parse_args()
    n = 36960
    p = cyclotomic_at_two(n)
    check(n == 2**5*3*5*7*11, "factorization of order")
    check((p-1) % n == 0 and n**2 <= p, "splitting and sparse domain")
    check(pow(2,n,p) == 1 and all(pow(2,n//q,p) != 1 for q in (2,3,5,7,11)), "exact order")
    if args.certificate:
        payload = args.certificate.read_bytes()
        check(hashlib.sha256(payload).hexdigest() == "5629407e2f4fa92922f64fc12eeff5bedcd99fe9a3570c19cbb316d38f1553fe", "incorrect certificate digest")
        candidate = configparser.ConfigParser(allow_no_value=True)
        candidate.read_string(payload.decode("ascii"))
        check(int(candidate["Candidate"]["N$"], 16) == p, "incorrect PRIMO candidate")
    grid = 4096
    bins = Counter()
    x = 1
    for _ in range(n):
        t = min(x, p-x)
        right = (grid*t+p-1)//p
        bins[right] += 1
        x = 2*x % p
    check(x == 1 and sum(bins.values()) == n, "incomplete orbit")
    # Round down each cosine bound before aggregation; the final certificate has denominator 10^8.
    scale = 10**8
    total = sum(count * (scale*cos_lower(F(j,grid))).__floor__() for j,count in bins.items())
    check(total > 0 and (n<<7666)>p, "logarithmic upper bound")
    check(total**2 > 4*n*7666*scale**2, "constant-two separation")
    print(f"n={n} subgroup order; p=Phi_{n}(2), {p.bit_length()} bits")
    print(f"Re(period) >= {total}/{scale} > 2*sqrt({n}*7666)")
    print(f"integer square-test margin = {total**2 - 4*n*7666*scale**2}")


if __name__ == "__main__":
    main()
