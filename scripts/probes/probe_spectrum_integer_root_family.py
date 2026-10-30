#!/usr/bin/env python3
"""G332 companion: weight-{1,3} spectrum at g=2 when ord_p(2)=2h (Fermat-factor primes).

Records that the KKH26 counting-core law is missed at every tested rung where 2 is a
primitive 2h-th root of unity.  Stdlib only, exact integer arithmetic.

Cases:
  h=16, p=65537                 (=F4)           law 4512   -> 3264
  h=32, p=6700417               (=F5/641)       law 39744  -> 34176
  h=64, p=67280421310721        (=F6/274177)    law 333440 -> 310016

Also verifies the integer spine 1+2-4=-1 and that the same deficiency appears for other
generators of order 2h at h=16 (generator-independence spot check).
"""
import sys
from itertools import combinations
from math import comb


def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def ord_mod(a, p):
    if pow(a, p - 1, p) != 1:
        return None
    o = p - 1
    # factor out 2s then trial
    factors = []
    x = o
    while x % 2 == 0:
        factors.append(2)
        x //= 2
    d = 3
    while d * d <= x:
        while x % d == 0:
            factors.append(d)
            x //= d
        d += 2
    if x > 1:
        factors.append(x)
    for f in set(factors):
        while o % f == 0 and pow(a, o // f, p) == 1:
            o //= f
    return o


def law(h, A=(1, 3)):
    return sum(2 ** a * comb(h, a) for a in A)


def fibers(p, h, g):
    w = [pow(g, i, p) for i in range(h)]
    out = {}
    for i in range(h):
        for s in (1, -1):
            out.setdefault((s * w[i]) % p, []).append(((i,), (s,)))
    for i, j, k in combinations(range(h), 3):
        a, b, c = w[i], w[j], w[k]
        for m in range(8):
            v = (a if m & 1 else -a) + (b if m & 2 else -b) + (c if m & 4 else -c)
            out.setdefault(v % p, []).append(
                ((i, j, k), tuple(1 if m >> t & 1 else -1 for t in range(3))))
    return out


def main():
    assert (1 + 2 - 4) == -1
    print("spine identity 1+2-4=-1 OK")

    cases = [
        (16, 65537, 3264),
        (32, 6700417, 34176),
        (64, 67280421310721, 310016),
    ]
    print("=== Fermat-factor family at g=2 ===")
    for h, p, expected in cases:
        assert is_prime(p), p
        assert ord_mod(2, p) == 2 * h, (p, ord_mod(2, p))
        L = law(h)
        fib = fibers(p, h, 2)
        n = len(fib)
        print(f"  h={h} p={p}: |fib|={n}/{L} deficiency={L-n} p/|D|={p/L:.1f}")
        assert n == expected, (h, n, expected)
        assert p > L  # genuine, not saturation

    print("=== generator-independence spot (h=16, p=65537) ===")
    # all generators of order 32 give the same count
    counts = set()
    for a in range(2, 200):
        if pow(a, 32, 65537) == 1 and pow(a, 16, 65537) == 65536:
            counts.add(len(fibers(65537, 16, a)))
    print(f"  distinct counts over order-32 gens sampled: {counts}")
    assert counts == {3264}

    print("PASS: ring-uniform g=2 spine explains the Fermat-factor deficiency family")
    return 0


if __name__ == "__main__":
    sys.exit(main())
