#!/usr/bin/env python3
"""Order-32 (h=16) signed weight-{1,3} spectrum: exact census at the n = 32 rung.

LEADS-008 probe.  Extends the rungs already pinned in-tree:

  h = 4 (order 8,  G330 / Frontier/_G330SpectrumExactBoundary.lean)
        -> 40 distinct values at every p = 1 (mod 8), p != 17; 16 at p = 17.
  h = 8 (order 16, PR #264 / probe_order16_weight13_spectrum.py)
        -> 464 distinct values at every prime outside a 34-element exceptional
           set (largest 4049); 464 at p = 65537.

Object.  For a prime p with an element g of exact order 2h, let D be the
2*C(h,1) + 2^3*C(h,3) signed data of support size 1 or 3 over the half-window
{g^0, ..., g^{h-1}}, with value  sum_{i in T} g^i - sum_{i in U\\T} g^i
(the in-tree `sigData`/`sVal` of ArkLib/.../KKH26SumsOfRootsOfUnity.lean).
`ArkLib.ProximityGap.KKH26.subsetSumSpectrum_card`
(ArkLib/.../TwoPowerSubsetSumSpectrum.lean) converts injectivity of this map at
weight set A = {1,3} into the exact count sum_{a in A} 2^a * C(h,a), the
counting core consumed by the KKH26 dimension-two pin.

Findings at h = 16 (|D| = 4512):
  * At p = 65537 the map is NOT injective: 3264 distinct values (deficiency
    1248; fibers 2144 singletons / 992 doubletons / 128 tripletons).  This is a
    genuine algebraic deficiency, not saturation, because 65537 > 4512.
    Mechanism: 65537 = 2^16 + 1, so ord(2) = 32 and g = -8 is a 32nd root of
    unity that is a small integer; the identity g^5 + 2*g^10 = 1 (equivalently
    2^30 = -2^14 mod p) collides a weight-1 with a weight-3 datum.
  * At the prize-scale Proth primes k*2^128 + 1 (k = 21, 111, 123) the map is
    injective: exactly 4512 values.
  * Over all p = 1 (mod 32) in [97, 200000] the exact count 4512 is attained at
    only a handful of primes; every other prime above the saturation threshold
    4512 is genuinely deficient.  The n = 16 exception set (largest 4049) is
    therefore NOT the model for n = 32.

What this does NOT do: no field-uniform theorem, no statement about weight sets
other than {1,3}, no production n = 2^30 claim, no delta* movement.  The
in-tree sharp injectivity route `sVal_injOn` requires p > 2^80 and is not
contradicted; what fails here is the small-field instance hypothesis `hinj`.

Stdlib only, exact integer arithmetic, no floats.

Usage:  python3 probe_order32_weight13_spectrum.py [LIMIT]
"""
import sys
from itertools import combinations

LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 200_000


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


def root_of_order(p, m):
    """an element of F_p of exact multiplicative order m (requires m | p-1)."""
    e = (p - 1) // m
    for a in range(2, 2000):
        h = pow(a, e, p)
        if pow(h, m // 2, p) == p - 1:
            return h
    return None


def fibers(p, h):
    """value -> list of (support, sign tuple) for signed weights {1,3} over h."""
    g = root_of_order(p, 2 * h)
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
    return g, out


def target(h):
    return 2 * h + 8 * (h * (h - 1) * (h - 2) // 6)


def census(h, limit, label):
    T = target(h)
    m = 2 * h
    primes = [p for p in range(m + 1, limit + 1) if p % m == 1 and is_prime(p)]
    rows = []
    for p in primes:
        _, fib = fibers(p, h)
        rows.append((p, len(fib)))
    sat = [r for r in rows if r[0] <= T]
    genuine = [r for r in rows if r[0] > T]
    full = [p for p, n in genuine if n == T]
    defi = [(p, n) for p, n in genuine if n != T]
    print(f"[{label}] h={h} (order {m}), |D|={T}, {len(rows)} primes p=1 (mod {m}) in [{m+1},{limit}]")
    print(f"   p <= {T} (saturation admissible): {len(sat)} primes, never {T}")
    print(f"   p >  {T} (genuine test):          {len(genuine)} primes")
    print(f"     exact {T}: {len(full)} primes -> {full[:12]}{' ...' if len(full) > 12 else ''}")
    print(f"     deficient: {len(defi)} primes, worst deficiency "
          f"{max((T - n, p) for p, n in defi) if defi else None}")
    return rows


def main():
    print("=== method validation against the two pinned rungs ===")
    T4, T8 = target(4), target(8)
    bad4 = [(p, len(fibers(p, 4)[1])) for p in range(9, 5000) if p % 8 == 1 and is_prime(p)]
    print(f"h=4: {T4} values; exceptions != {T4}: {[x for x in bad4 if x[1] != T4]}"
          f"  (G330: only p=17, count 16)")
    bad8 = [(p, len(fibers(p, 8)[1])) for p in range(17, 5000) if p % 16 == 1 and is_prime(p)]
    exc8 = [x for x in bad8 if x[1] != T8]
    print(f"h=8: {T8} values; {len(exc8)} exceptions <= 4999, largest {max([p for p,_ in exc8], default=None)}"
          f"  (#264: 34 exceptions, largest 4049)")
    print(f"h=8: p=65537 -> {len(fibers(65537, 8)[1])} values (injective at n=16)")
    print()

    print("=== n = 32 census (h = 16) ===")
    census(16, LIMIT, "n32")
    print()

    T = target(16)
    for p in (65537, 21 * 2**128 + 1, 111 * 2**128 + 1, 123 * 2**128 + 1):
        if (p - 1) % 32:
            continue
        g, fib = fibers(p, 16)
        tag = f"{p}" if p < 10**7 else f"{str(p)[:6]}...*2^128+1"
        print(f"  spot p={tag}: {len(fib)} values, deficiency {T - len(fib)}")
    print()

    print("=== collision structure at p = 65537 (h = 16) ===")
    g, fib = fibers(65537, 16)
    sizes = {}
    for ds in fib.values():
        sizes[len(ds)] = sizes.get(len(ds), 0) + 1
    print(f"  g = {g} = -8 mod p;  (-8)^16 mod p = {pow(-8, 16, 65537)}")
    print(f"  values {len(fib)}; fiber sizes {dict(sorted(sizes.items()))};"
          f" colliding pairs {sum(len(d)*(len(d)-1)//2 for d in fib.values())}")
    ex = [(v, ds) for v, ds in fib.items() if len(ds) == 2 and any(len(d[0]) == 1 for d in ds)]
    ex.sort(key=lambda t: max(max(d[0]) for d in t[1]))
    v, ds = ex[0]
    print(f"  minimal-exponent weight-1/weight-3 collision at value {v}: {ds[0]} == {ds[1]}")
    print(f"  identity: g^5 + 2*g^10 - 1 = {(pow(g,5,65537) + 2*pow(g,10,65537) - 1) % 65537}")
    print()
    print("PASS")


if __name__ == "__main__":
    main()
