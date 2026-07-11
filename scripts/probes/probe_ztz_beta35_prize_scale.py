#!/usr/bin/env python3
"""Prime-supply probe for the β = 3 and β = 5 Thorner–Zaman rungs AT THE PRIZE MODULUS
n = 2^30 (#466).

Finds >= 12 primes p ≡ 1 (mod 2^30) inside each window [n^β, 2·n^β] (β = 3: [2^90, 2^91],
β = 5: [2^150, 2^151]), in the two-factor Lucas shape p − 1 = 2^e·c (c a small odd prime)
with witness g (g = 3 first).  Primality screening beyond the exact-MR range is a strong
52-base Miller–Rabin screen — the Lean kernel Lucas certificate is the actual proof; any
screening false positive would simply fail to certify in Lean.

Provenance: mirrors scripts/probes/probe_ztz_beta4_prize_scale.py (β = 4, [2^120, 2^121]).
"""

_MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
_EXTRA_BASES = tuple(range(41, 200, 4))


def is_prime_exact_small(n: int) -> bool:
    if n < 2:
        return False
    for p in _MR_BASES:
        if n % p == 0:
            return n == p
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in _MR_BASES:
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def is_probable_prime_big(n: int) -> bool:
    if n < 2:
        return False
    for p in _MR_BASES:
        if n % p == 0:
            return n == p
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in _MR_BASES + _EXTRA_BASES:
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def lucas_witness(p: int, c: int):
    pm1 = p - 1
    for g in (3, 2, 5, 6, 7, 10, 11, 12, 13, 17):
        if pow(g, pm1, p) != 1:
            continue
        if pow(g, pm1 // 2, p) == 1:
            continue
        if pow(g, pm1 // c, p) == 1:
            continue
        return g
    return None


def find_rung(beta: int, want: int = 12):
    n = 1 << 30
    lo, hi = n ** beta, 2 * n ** beta
    bits = 30 * beta
    found = []
    for c in range(3, 1 << 21, 2):
        if len(found) >= want * 3:
            break
        if not is_prime_exact_small(c):
            continue
        k = c.bit_length()
        for e in (bits - k, bits + 1 - k):
            if e < 30:
                continue
            p = (1 << e) * c + 1
            if lo <= p <= hi and is_probable_prime_big(p):
                g = lucas_witness(p, c)
                if g is not None:
                    found.append((p, c, e, g))
    found.sort(key=lambda t: (t[1], t[0]))
    chosen = sorted(found[:want])
    return n, lo, hi, chosen


def main():
    for beta in (3, 5):
        n, lo, hi, chosen = find_rung(beta)
        print(f"# n = 2^30, beta = {beta}, window [2^{30*beta}, 2^{30*beta+1}] = [{lo}, {hi}]")
        print(f"# emitting {len(chosen)}")
        for (p, c, e, g) in chosen:
            assert p - 1 == (1 << e) * c and (p - 1) % n == 0 and lo <= p <= hi
            assert is_prime_exact_small(c) and c % 2 == 1
            assert pow(g, p - 1, p) == 1
            assert pow(g, (p - 1) // 2, p) != 1
            assert pow(g, (p - 1) // c, p) != 1
            print(f"p={p} c={c} e={e} g={g}")


if __name__ == "__main__":
    main()
