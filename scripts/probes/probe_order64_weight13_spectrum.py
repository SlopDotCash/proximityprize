#!/usr/bin/env python3
"""Order-64 (h=32) signed weight-{1,3} spectrum: exact census at the n = 64 rung.

Extends the rungs already pinned in-tree / in open PRs:

  h = 4  (order 8,  G330)  -> 40 values except p = 17.
  h = 8  (order 16, #264)  -> 464 values outside a 34-prime set; injective at 65537.
  h = 16 (order 32, #292 / G331) -> NOT injective at 65537 (3264 vs 4512).
  h = 32 (order 64, this probe / G332) -> NOT injective at 65537 (13761 vs 39744).

Object.  For a prime p with an element g of exact order 2h, let D be the
2*C(h,1) + 2^3*C(h,3) signed data of support size 1 or 3 over the half-window
{g^0, ..., g^{h-1}}.  ArkLib.ProximityGap.KKH26.subsetSumSpectrum_card converts
injectivity of this map at weight set A = {1,3} into the exact count
sum_{a in A} 2^a * C(h,a).

Findings at h = 32 (|D| = 39744):
  * At p = 65537 the map is NOT injective: 13761 distinct values (deficiency
    25983).  Genuine, not saturation: 65537 > 39744.
    Mechanism: g = 8224 has order 64; g^3 - g^6 + g^16 = 1 (= g^0) collides a
    weight-1 datum with a weight-3 datum.
  * At the prize-scale Proth prime 21*2^128+1 the map is injective: exactly 39744.
  * Spot checks: p = 12289 -> 12160; p = 641 -> 641 (saturation).

What this does NOT do: no field-uniform theorem, no production claim, no delta*
movement.  Open PR #300 already prints 13761 / 39744 as side data via a
monomial-pencil route; this probe is the spectrum injectivity reading.

Stdlib only, exact integer arithmetic, no floats.

Usage:  python3 probe_order64_weight13_spectrum.py
"""
import sys
from itertools import combinations


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
    e = (p - 1) // m
    for a in range(2, 8000):
        h = pow(a, e, p)
        if pow(h, m // 2, p) == p - 1:
            return h
    return None


def fibers(p, h, g=None):
    if g is None:
        g = root_of_order(p, 2 * h)
    if g is None:
        raise RuntimeError(f"no root of order {2*h} mod {p}")
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


def main():
    print("=== method validation against pinned rungs ===")
    T4, T8, T16, T32 = target(4), target(8), target(16), target(32)
    assert T4 == 40 and T8 == 464 and T16 == 4512 and T32 == 39744

    bad4 = [(p, len(fibers(p, 4)[1])) for p in range(9, 2000) if p % 8 == 1 and is_prime(p)]
    exc4 = [x for x in bad4 if x[1] != T4]
    assert exc4 == [(17, 16)], exc4
    print(f"h=4: {T4} values; exceptions {exc4}  (G330: only p=17, count 16)")

    g8, fib8 = fibers(65537, 8)
    assert len(fib8) == T8
    print(f"h=8: p=65537 -> {len(fib8)} values (injective at n=16, #264)")

    g16, fib16 = fibers(65537, 16)
    assert len(fib16) == 3264
    print(f"h=16: p=65537 -> {len(fib16)} values (G331 / #292: deficient)")

    print()
    print("=== n = 64 spots (h = 32) ===")
    spots = [
        (641, None),
        (12289, None),
        (65537, 8224),  # Lean certificate generator
        (21 * 2**128 + 1, None),
    ]
    expected = {
        641: 641,
        12289: 12160,
        65537: 13761,
        21 * 2**128 + 1: 39744,
    }
    for p, gfix in spots:
        g, fib = fibers(p, 32, gfix)
        n = len(fib)
        tag = str(p) if p < 10**7 else f"{str(p)[:8]}... (=21*2^128+1)"
        print(f"  p={tag}: g={g}, |fib|={n}/{T32}, deficiency {T32 - n}")
        assert n == expected[p], (p, n, expected[p])

    print()
    print("=== collision structure at p = 65537 (h = 32, g = 8224) ===")
    g, fib = fibers(65537, 32, 8224)
    assert pow(g, 64, 65537) == 1
    assert pow(g, 32, 65537) == 65536
    assert (pow(g, 3, 65537) - pow(g, 6, 65537) + pow(g, 16, 65537)) % 65537 == 1
    print(f"  g = {g}; g^64 = 1; g^32 = -1; g^3 - g^6 + g^16 = 1 (= g^0)")
    print(f"  values {len(fib)}; colliding pairs "
          f"{sum(len(d)*(len(d)-1)//2 for d in fib.values())}")
    # Exhibit the Lean collision fiber
    v = 1
    ds = fib[v]
    print(f"  fiber at value 1: {ds[:6]}{' ...' if len(ds) > 6 else ''}")
    assert any(d[0] == (0,) and d[1] == (1,) for d in ds)
    assert any(d[0] == (3, 6, 16) and d[1] == (1, -1, 1) for d in ds)

    print()
    print(
        "PASS: order-64 weight-{1,3} spectrum non-injective at p=65537 "
        "(13761 vs 39744); injective at prize-scale Proth; G330/G331 integers reproduced"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
