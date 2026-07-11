#!/usr/bin/env python3
"""Prime-supply probe for the concrete β = 4 Thorner–Zaman ladder (#466).

For each target n ∈ {128, 256, 512, 1024} = 2^{7,8,9,10} this finds ≥ 12 primes
p ≡ 1 (mod n) inside the window [n^4, 2·n^4], each in the two-factor Lucas shape

    p − 1 = 2^e · c,   c an odd prime,   e ≥ log2(n),

and picks a Lucas witness g (g = 3 first) with

    g^(p−1) = 1 (mod p),  g^((p−1)/2) ≠ 1 (mod p),  g^((p−1)/c) ≠ 1 (mod p).

Everything is exact: deterministic Miller–Rabin (a set of bases that is proven
correct below 3.3·10^24, far above the ~2^41 ceiling here) plus exact integer
arithmetic. Output is paste-ready Lean certificate data.

Provenance: mirrors scripts/probes/probe_ztz_beta3_ladder.py; independent of it.
"""

# Deterministic Miller–Rabin: this base set certifies primality for all
# n < 3,317,044,064,679,887,385,961,981 (>> 2^41). Exact, no probabilism.
_MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d = n - 1
    r = 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in _MR_BASES:
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


def factor_two_odd(m: int):
    """Return (e, c) with m = 2^e * c, c odd."""
    e = 0
    while m % 2 == 0:
        m //= 2
        e += 1
    return e, m


def lucas_witness(p: int, c: int):
    """Return smallest g in {3,2,5,6,7,...} certifying p via 2-factor Lucas, or None."""
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


def _small_odd_primes(bound: int):
    return [c for c in range(3, bound, 2) if is_prime(c)]


def find_rung(n: int, want: int = 12, c_bound: int = 1 << 16):
    """Find `want` primes p = 1 (mod n) in [n^4, 2n^4] of shape p-1 = 2^e * c,
    c an odd prime, PREFERRING the smallest odd cofactor c (largest 2-adic
    valuation e) so the norm_num primality check on c stays instant."""
    lo = n ** 4
    hi = 2 * n ** 4
    k = n.bit_length() - 1  # n = 2^k, so p = 1 (mod n) needs e >= k
    pool = {}  # p -> (c, e, g), deduped
    for c in _small_odd_primes(c_bound):
        # e ranges so that p = 2^e * c + 1 lands in [lo, hi]
        e = k
        while (1 << e) * c + 1 <= hi:
            if e >= k:
                p = (1 << e) * c + 1
                if lo <= p <= hi and is_prime(p):
                    # exact 2-adic factorization: c odd => valuation is exactly e
                    ee, cc = factor_two_odd(p - 1)
                    if ee == e and cc == c:
                        g = lucas_witness(p, c)
                        if g is not None and p not in pool:
                            pool[p] = (c, e, g)
            e += 1
    # rank by smallest cofactor c, then by p, take the first `want`
    ranked = sorted(pool.items(), key=lambda kv: (kv[1][0], kv[0]))
    chosen = [(p, c, e, g) for (p, (c, e, g)) in ranked[:want]]
    chosen.sort(key=lambda t: t[0])  # ascending p for readable Lean literals
    return lo, hi, chosen


def main():
    for e_n, n in [(7, 128), (8, 256), (9, 512), (10, 1024)]:
        lo, hi, res = find_rung(n, 12)
        print(f"# ===== n = {n} = 2^{e_n}, beta = 4, window [n^4, 2n^4] = [{lo}, {hi}] "
              f"= [2^{4*e_n}, 2^{4*e_n+1}] =====")
        print(f"# found {len(res)} primes p = 1 (mod {n}) of shape p-1 = 2^e * c (c odd prime)")
        # sanity re-check every returned prime independently
        for (p, c, e, g) in res:
            assert p - 1 == 2 ** e * c, (p, c, e)
            assert is_prime(c) and c % 2 == 1
            assert (p - 1) % n == 0
            assert pow(g, p - 1, p) == 1
            assert pow(g, (p - 1) // 2, p) != 1
            assert pow(g, (p - 1) // c, p) != 1
            assert lo <= p <= hi
        # Lean prime theorems
        for (p, c, e, g) in res:
            print(f"private theorem prime_{p} : Nat.Prime {p} :=")
            print(f"  lucasTwoFactor {c} {e} {g} (by norm_num) (by norm_num)")
            print(f"    (by rw [← binaryPow_eq_pow]; decide)")
            print(f"    (by rw [← binaryPow_eq_pow]; decide)")
            print(f"    (by rw [← binaryPow_eq_pow]; decide)")
        # Lean finset literal
        primes = [str(p) for (p, c, e, g) in res]
        print("# finset literal:")
        print("      {" + ", ".join(primes) + "}")
        print(f"# hpow target: (({n} : ℕ) : ℝ) ^ (4 : ℝ) = {n**4}")
        print()


if __name__ == "__main__":
    main()
