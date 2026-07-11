#!/usr/bin/env python3
"""Prime-supply probe for the β = 4 Thorner–Zaman rung AT THE PRIZE MODULUS n = 2^30 (#466).

Finds >= 12 primes p ≡ 1 (mod 2^30) inside the window [n^4, 2·n^4] = [2^120, 2^121],
each in the two-factor Lucas shape

    p − 1 = 2^e · c,   c an odd prime (c small, so `norm_num` is instant),

with a Lucas witness g (g = 3 first):

    g^(p−1) = 1 (mod p),  g^((p−1)/2) ≠ 1 (mod p),  g^((p−1)/c) ≠ 1 (mod p).

Primality screening at 121 bits uses Miller–Rabin with the fixed 12-base set plus 40
extra deterministic bases; the fixed set is only PROVEN exact below 3.3e24, so at this
size MR is a (cryptographically strong) screen — the Lean kernel's Lucas certificate is
the actual proof, and any false positive would simply fail to certify in Lean.  The odd
cofactor c <= 2^21 is checked with the exact small-range test.

Provenance: mirrors scripts/probes/probe_ztz_beta4_ladder.py (same shapes); window/scale
mirrors scripts/probes/probe_w16_tz_prize_scale.py (n = 2^30, beta = 2, 60-bit) but at
beta = 4 (120-bit).
"""

_MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
_EXTRA_BASES = tuple(range(41, 200, 4))  # deterministic extra screen bases


def is_prime_exact_small(n: int) -> bool:
    """Exact for n < 3.3e24 (12-base deterministic Miller-Rabin)."""
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
    """Strong MR screen with 52 bases (12 fixed + 40 extra). Lean is the final arbiter."""
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


def main():
    n = 1 << 30
    lo, hi = n ** 4, 2 * n ** 4  # [2^120, 2^121]
    assert lo == 1 << 120 and hi == 1 << 121
    want = 12
    found = []  # (p, c, e, g)
    # p = 2^e * c + 1 in [2^120, 2^121] with c odd prime; prefer smallest c.
    # For c in [2^k, 2^(k+1)) we need e in {120-k-1, 120-k} for p to land in window.
    for c in range(3, 1 << 21, 2):
        if len(found) >= want * 3:  # gather a pool, then rank
            break
        if not is_prime_exact_small(c):
            continue
        k = c.bit_length()
        for e in (120 - k, 121 - k):
            if e < 30:
                continue
            p = (1 << e) * c + 1
            if lo <= p <= hi and is_probable_prime_big(p):
                g = lucas_witness(p, c)
                if g is not None:
                    found.append((p, c, e, g))
    # rank by smallest cofactor c (cheapest norm_num), take 12, sort by p
    found.sort(key=lambda t: (t[1], t[0]))
    chosen = sorted(found[:want])
    print(f"# n = 2^30, beta = 4, window [2^120, 2^121] = [{lo}, {hi}]")
    print(f"# pool {len(found)}, emitting {len(chosen)}")
    for (p, c, e, g) in chosen:
        # independent re-assertions
        assert p - 1 == (1 << e) * c and (p - 1) % n == 0 and lo <= p <= hi
        assert is_prime_exact_small(c) and c % 2 == 1
        assert pow(g, p - 1, p) == 1
        assert pow(g, (p - 1) // 2, p) != 1
        assert pow(g, (p - 1) // c, p) != 1
        print(f"p={p} c={c} e={e} g={g}")


if __name__ == "__main__":
    main()
