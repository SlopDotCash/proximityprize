#!/usr/bin/env python3
"""#466 OC lane: Galois equidistribution of embedding incidences for the FULL support-6
height-1 relation pool.

Claim under test (the Lean brick `_OCGaloisEmbeddingEquidistribution.lean`):
for the FULL Galois-stable pool of support-<=6 height-1 negacyclic relations
r(X) in Z[X]/(X^m + 1), the per-embedding vanishing count

    count(a) = #{ r in Pool : r(w^a) == 0 mod p },   a in (Z/2m)^*

is EXACTLY constant in a (Galois equivariance: r vanishes at a*c iff sigma_c(r)
vanishes at a, and the pool is sigma-stable). Hence the OC-PIECEB probe's measured
"concentration at a=1" is orbit-representative search bias, NOT a property of the pool,
and transversal coverage is all-or-nothing.

Also reports: total incidences, count(1), and checks total == n_units * count(1).
"""

import itertools
import sys


def primitive_2m_root(p, M):
    """Find an element of multiplicative order M mod p (requires M | p-1)."""
    assert (p - 1) % M == 0
    for g in range(2, p):
        # candidate w = g^((p-1)/M)
        w = pow(g, (p - 1) // M, p)
        # check exact order M
        ok = True
        m2 = M
        for q in prime_factors(M):
            if pow(w, M // q, p) == 1:
                ok = False
                break
        if ok and pow(w, M, p) == 1:
            return w
    raise RuntimeError("no root found")


def prime_factors(x):
    fs = set()
    d = 2
    while d * d <= x:
        while x % d == 0:
            fs.add(d)
            x //= d
        d += 1
    if x > 1:
        fs.add(x)
    return fs


def is_prime(x):
    if x < 2:
        return False
    for d in range(2, int(x ** 0.5) + 1):
        if x % d == 0:
            return False
    return True


def run_cell(n, p, support):
    m = n // 2          # negacyclic degree
    M = 2 * m           # = n; embeddings indexed by (Z/2m)^* acting on 2m-th roots
    assert (p - 1) % M == 0
    w = primitive_2m_root(p, M)
    units = [a for a in range(M) if __import__("math").gcd(a, M) == 1]
    # precompute wpow[e] for e in Z/M
    wpow = [pow(w, e, p) for e in range(M)]

    # Pool: coefficient vectors v over Z/m indices (negacyclic, degree < m),
    # support exactly `support`, heights +-1.
    # r(w^a) = sum_j v_j * w^(a*j) mod p.
    counts = {a: 0 for a in units}
    total_pool = 0
    for supp in itertools.combinations(range(m), support):
        for signs in itertools.product((1, -1), repeat=support):
            total_pool += 1
            for a in units:
                s = 0
                for j, sg in zip(supp, signs):
                    s += sg * wpow[(a * j) % M]
                if s % p == 0:
                    counts[a] += 1
    vals = [counts[a] for a in units]
    equal = len(set(vals)) == 1
    total = sum(vals)
    print(f"n={n} m={m} p={p} support={support} pool={total_pool}")
    print(f"  per-embedding counts: {dict(counts)}")
    print(f"  EQUIDISTRIBUTED: {equal}   total={total}  n_units={len(units)}  "
          f"count(1)={counts[1]}  total==n_units*count(1): {total == len(units) * counts[1]}")
    return equal, total == len(units) * counts[1]


def thin_primes(n, lo_beta, hi_beta, limit=3):
    """primes p == 1 mod n in [n^lo_beta, n^hi_beta], first `limit`."""
    out = []
    p = n ** lo_beta // n * n + 1
    while len(out) < limit and p < n ** hi_beta:
        if p % n == 1 and is_prime(p):
            out.append(p)
        p += n
    return out


def main():
    all_ok = True
    for n, support in [(16, 6), (16, 4), (32, 6)]:
        for p in thin_primes(n, 2, 4, limit=2):
            eq, tot = run_cell(n, p, support)
            all_ok = all_ok and eq and tot
    print()
    print(f"ALL CELLS EQUIDISTRIBUTED + total=n_units*count(1): {all_ok}")
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
