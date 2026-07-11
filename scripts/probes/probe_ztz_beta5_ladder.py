#!/usr/bin/env python3
"""Prime sieve for the QUINTIC (beta = 5) Thorner-Zaman ladder extension (#466).

For each target modulus n in {16, 32, 64} we find primes p with
  * p in the window [n^5, 2*n^5],
  * p == 1 (mod n),
  * p - 1 = 2^e * c with c an odd PRIME (two-factor Lucas shape),
  * a Lucas witness g (try g = 3 first) satisfying
        g^(p-1)      == 1 (mod p),
        g^((p-1)/2)  != 1 (mod p),
        g^((p-1)/c)  != 1 (mod p).

Primality is decided by deterministic Miller-Rabin (exact well below 2^64:
witness set {2,3,5,7,11,13,17,19,23,29,31,37} is a proof for n < 3.3e24).

Emits paste-ready Lean `lucasTwoFactor c e g` certificate data plus the
Finset literal for each rung.  Deterministic; no randomness.

Windows:
  n = 16 -> [2^20, 2^21] = [1048576, 2097152]
  n = 32 -> [2^25, 2^26] = [33554432, 67108864]
  n = 64 -> [2^30, 2^31] = [1073741824, 2147483648]
"""

# Deterministic Miller-Rabin witnesses: a proof of primality for all n < 3.3e24.
_MR_WITNESSES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]


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
    for a in _MR_WITNESSES:
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


def two_factor(pm1: int):
    """Return (e, c) with pm1 = 2^e * c, c odd; c may or may not be prime."""
    e = 0
    c = pm1
    while c % 2 == 0:
        c //= 2
        e += 1
    return e, c


def lucas_witness(p: int, c: int, e: int):
    """Smallest g in {3,2,5,7,...} that is a valid two-factor Lucas witness."""
    pm1 = p - 1
    for g in (3, 2, 5, 6, 7, 10, 11, 12, 13):
        if g % p == 0:
            continue
        if pow(g, pm1, p) != 1:
            continue
        if pow(g, pm1 // 2, p) == 1:
            continue
        if pow(g, pm1 // c, p) == 1:
            continue
        return g
    return None


def find_rung(n: int, count: int = 12):
    lo = n ** 5
    hi = 2 * n ** 5
    results = []
    # walk p == 1 (mod n) upward through the window
    p = lo + ((1 - lo) % n)  # smallest p >= lo with p == 1 (mod n)
    if p < lo:
        p += n
    while p <= hi and len(results) < count:
        if is_prime(p):
            e, c = two_factor(p - 1)
            # need c an ODD PRIME and e >= log2(n) so that p == 1 (mod n)
            if c > 1 and is_prime(c):
                g = lucas_witness(p, c, e)
                if g is not None:
                    assert (2 ** e) * c == p - 1
                    assert p % n == 1
                    results.append((p, c, e, g))
        p += n
    return lo, hi, results


def emit(n: int):
    lo, hi, res = find_rung(n, 12)
    print(f"# ===== n = {n}, beta = 5, window [{lo}, {hi}] = [2^{lo.bit_length()-1}, 2^{hi.bit_length()-1}] =====")
    print(f"# found {len(res)} certified primes (need 12)")
    if len(res) < 12:
        print("# !!! INSUFFICIENT PRIMES !!!")
    for (p, c, e, g) in res:
        print(f"private theorem prime_{p} : Nat.Prime {p} :=")
        print(f"  lucasTwoFactor {c} {e} {g} (by norm_num) (by norm_num)")
        print(f"    (by rw [← binaryPow_eq_pow]; decide)")
        print(f"    (by rw [← binaryPow_eq_pow]; decide)")
        print(f"    (by rw [← binaryPow_eq_pow]; decide)")
    print(f"# Finset literal ({n}):")
    lit = ", ".join(str(p) for (p, _, _, _) in res)
    print(f"# {{{lit}}}")
    print(f"# n^5 = {lo}")
    # sanity: all witnesses uniform?
    gs = set(g for (_, _, _, g) in res)
    print(f"# witness set used: {sorted(gs)}")
    print()
    return res


if __name__ == "__main__":
    for n in (16, 32, 64):
        emit(n)
