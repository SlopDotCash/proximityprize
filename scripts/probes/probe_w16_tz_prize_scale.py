#!/usr/bin/env python3
"""
probe_w16_tz_prize_scale.py — thread res:tz-prize-scale (#466, TZ ladder to prize scale)

Sieve explicit witnesses for `TZPrimeSupply n beta supply` at beta = 2 for the dyadic
rungs n = 2^k, k = 16 .. 30 (prize scale n = 2^30), i.e. primes

    p ≡ 1 (mod 2^k),   p in [n^2, 2*n^2] = [2^{2k}, 2^{2k+1}].

To make each prime KERNEL-CHEAP to certify in Lean (no native_decide), we restrict the
sieve to primes of the shape

    p = 2^a * c + 1,   c an odd PRIME,   a = max(k, 2k - 20)   (so c has <= 21 bits),

so that p - 1 = 2^a * c has exactly two distinct prime factors {2, c}: the Lucas
certificate (Mathlib `lucas_primality`) then needs only three modular exponentiations
    g^(p-1) = 1,  g^((p-1)/2) != 1,  g^((p-1)/c) != 1
and one norm_num primality check on the <= 21-bit cofactor c.

Verification is fully deterministic: Miller-Rabin with the 12-base set
{2,3,5,7,11,13,17,19,23,29,31,37} is a proven deterministic primality test below
3.3 * 10^24 > 2^64 > all numbers used here; sympy.isprime cross-checks.

Output: per-rung witness tables + generated Lean code blocks (stdout + scratch files).
"""

import sys

MR_BASES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
DET_LIMIT = 3317044064679887385961981  # deterministic MR limit for these bases


def is_prime(n: int) -> bool:
    """Deterministic Miller-Rabin for n < 3.3e24."""
    assert n < DET_LIMIT
    if n < 2:
        return False
    for p in MR_BASES:
        if n % p == 0:
            return n == p
    d = n - 1
    r = 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in MR_BASES:
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


def v2(n: int) -> int:
    a = 0
    while n % 2 == 0:
        n //= 2
        a += 1
    return a


def find_witness(p: int, c: int) -> int:
    """Smallest g in small primes with g^((p-1)/2) != 1 and g^((p-1)/c) != 1 mod p.
    (g^(p-1) = 1 is automatic by Fermat since p is prime and g < p.)"""
    for g in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59]:
        if pow(g, (p - 1) // 2, p) != 1 and pow(g, (p - 1) // c, p) != 1:
            assert pow(g, p - 1, p) == 1
            return g
    raise RuntimeError(f"no small witness for p={p}")


def sieve_rung(k: int, want: int = 20):
    """Find `want` primes p = 2^a*c + 1 (c odd prime) with p ≡ 1 mod 2^k,
    p in [2^(2k), 2^(2k+1)]."""
    n = 1 << k
    lo, hi = n * n, 2 * n * n
    a = max(k, 2 * k - 20)
    assert a >= k
    c_lo = lo >> a
    c_hi = hi >> a
    out = []
    c = c_lo | 1  # first odd candidate
    while len(out) < want and c <= c_hi:
        if is_prime(c):
            p = (c << a) + 1
            if lo <= p <= hi and is_prime(p):
                g = find_witness(p, c)
                # --- independent verification block ---
                assert p % n == 1, (k, p)
                assert p - 1 == (1 << a) * c
                assert c % 2 == 1 and v2(p - 1) == a
                assert lo <= p <= hi
                try:
                    import sympy
                    assert sympy.isprime(p) and sympy.isprime(c)
                except ImportError:
                    pass
                out.append((p, c, a, g))
        c += 2
    if len(out) < want:
        raise RuntimeError(f"rung k={k}: only {len(out)} witnesses below c_hi")
    return out


LEAN_PRIME = """private theorem prime_{p} : Nat.Prime {p} :=
  lucasTwoFactor {c} {a} {g} (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
"""


def emit_rung(k: int, rows):
    n = 1 << k
    lo = n * n
    primes = [p for (p, _, _, _) in rows]
    lines = []
    lines.append(f"/-! ### Rung `n = 2^{k} = {n}`, β = 2: window `[{lo}, {2*lo}]` -/\n")
    for (p, c, a, g) in rows:
        lines.append(LEAN_PRIME.format(p=p, c=c, a=a, g=g))
    pl = ", ".join(str(p) for p in primes)
    memb = []
    for i, p in enumerate(primes):
        memb.append(
            f"  have h{i+1} : ({p} : ℕ) ∈ tzWindow {n} (2 : ℝ) := by\n"
            f"    rw [mem_tzWindow]\n"
            f"    exact ⟨prime_{p}, by decide, by rw [hpow]; norm_num,"
            f" by rw [hpow]; norm_num⟩"
        )
    memb_block = "\n".join(memb)
    thm = f"""/-- **Concrete discharge of `TZPrimeSupply` for `n = 2^{k} = {n}`, `β = 2`.**
The window `[{n}², 2·{n}²] = [{lo}, {2*lo}]` contains the twenty
explicit primes below, all `≡ 1 (mod {n})`; each is Lucas-certified via the two-factor
shape `p − 1 = 2^a·c` (`c` an odd prime of at most 21 bits). -/
theorem tzPrimeSupply_{n}_two : TZPrimeSupply {n} (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : (({n} : ℕ) : ℝ) ^ (2 : ℝ) = {lo} := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
{memb_block}
  have hsub : ({{{pl}}} : Finset ℕ) ⊆ tzWindow {n} (2 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (20 : ℕ) = ({{{pl}}} : Finset ℕ).card := by decide
    _ ≤ (tzWindow {n} (2 : ℝ)).card := Finset.card_le_card hsub
"""
    lines.append(thm)
    return "\n".join(lines)


def s128_budget_note():
    """Numeric honesty check: can beta=2 at n=2^30 ever feed the s=128 ceiling budget?"""
    import math
    mu, n = 7, 1 << 30
    for beta in (2, 3):
        for r in (2, 3):
            a = (2 ** r) * math.comb(64, r)
            pairs = a * a - a  # |collisionPairs| = offDiag of sigData square
            budget = pairs * (448 * math.log(2)) / (beta * 30 * math.log(2))
            x = float(n) ** beta
            heur = x / ((n / 2) * math.log(1.5 * x))  # ~ primes ≡1 mod n in [x,2x]
            print(f"  mu=7 r={r} beta={beta}: budget≈{budget:.3e}, "
                  f"heuristic window supply≈{heur:.3e}, "
                  f"{'FEASIBLE' if heur > budget else 'INFEASIBLE (window too thin)'}")


def main():
    ks = list(range(16, 31))
    scratch = ("/private/tmp/claude-501/-Users-shawwalters-ethereumroadmap-upstream-"
               "lean-research-ArkLib/515e83f2-d331-468d-84dd-89b67f383ddf/scratchpad")
    all_rows = {}
    for k in ks:
        rows = sieve_rung(k)
        all_rows[k] = rows
        print(f"k={k:2d} n=2^{k}: 20 primes found, first={rows[0][0]}, "
              f"last={rows[-1][0]}, a={rows[0][2]}, max c={max(c for _, c, _, _ in rows)}")
    print("\n[s=128 ceiling budget honesty check at n = 2^30]")
    s128_budget_note()
    import os
    os.makedirs(scratch, exist_ok=True)
    for k in ks:
        with open(f"{scratch}/rung_{k}.lean", "w") as f:
            f.write(emit_rung(k, all_rows[k]))
    print(f"\nLean blocks written to {scratch}/rung_<k>.lean")


if __name__ == "__main__":
    main()
