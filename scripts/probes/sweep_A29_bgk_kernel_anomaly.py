#!/usr/bin/env python3
"""
sweep_A29_bgk_kernel_anomaly.py  —  Actionable A29 part 2 (the WHERE-IS-M>0 question).

The prize-scale sweep (sweep_A29_bgk_kernel.py) found M(p,n)=0 for ALL thin large
primes (n << p^{1/4}).  That is the *expected* clean behaviour: with no char-p
anomaly the dyadic subgroup has no zero-sum 3-subset (M=0 in char 0, preserved).
The OPEN BGK core lives precisely where M>0 -- the anomaly primes.  This script
hunts them and characterizes:

  (A) the onset prime: as p grows past a threshold relative to n, M drops to 0 and
      STAYS 0 (the anomaly is a *small-p* / *thick* phenomenon, not a prize-scale one);
  (B) the maximum M ever achieved over a dense prime scan, vs sqrt(n) (BGK) and n (trivial);
  (C) the parity law  M odd <=> p | 2^n-1  and the 6|M law, on the M>0 sample;
  (D) the Fermat-factor correlation: when p | F_j (F_j=2^{2^j}+1), the element 1 lies
      in a zero-sum triple (u=1 obstruction).  Tabulate M for those primes vs generic.

KEY structural fact this probe makes precise:
  For the u=1 obstruction to be active we need p | 2^n - 1 AND n | p-1.
  2^n - 1 = prod_{j<k} F_j.  A prime divisor q of F_j has q = 1 (mod 2^{j+1}),
  and in fact for j>=2, q = 1 (mod 2^{j+2}).  So q | F_j can satisfy n=2^k | q-1
  only for small enough k -- this is the "range-k cutoff" of the Rosetta stone.
"""

import math
import statistics
from sympy import isprime, factorint


def subgroup_2pow(p, k):
    n = 2 ** k
    if (p - 1) % n:
        return None
    m = (p - 1) // n
    import random
    rng = random.Random(999 + p)
    for _ in range(300):
        a = rng.randrange(2, p)
        h = pow(a, m, p)
        if pow(h, n // 2, p) != 1 and pow(h, n, p) == 1:
            return frozenset(pow(h, i, p) for i in range(n))
    return None


def kernelM(p, mu_set):
    return sum(1 for u in mu_set if (-(1 + u)) % p in mu_set)


# ----------------------------------------------------------------------------
# (A)+(B)+(C): dense small-p scan -- find ALL primes p=1 mod n up to a cap,
# record M.  This is the regime where the char-p anomaly lives.
# ----------------------------------------------------------------------------

def dense_scan(k, p_cap):
    n = 2 ** k
    p = n + 1
    rows = []
    while p <= p_cap:
        if isprime(p):
            mu = subgroup_2pow(p, k)
            if mu is not None and len(mu) == n:
                M = kernelM(p, mu)
                mers = (pow(2, n, p) == 1)
                rows.append((p, M, mers))
        p += n
    return rows


def run():
    print("=" * 92)
    print("A29 part 2 — WHERE is the BGK kernel M(p,n) > 0?  (anomaly localization)")
    print("=" * 92)

    for k in (2, 3, 4, 5):
        n = 2 ** k
        # scan all primes p = 1 mod n up to a cap; cap shrinks as n grows so the
        # work stays bounded but we always cover p from n^1 up to >> n^4 (thin).
        p_cap = max(4_000_000, 300 * n * n)
        rows = dense_scan(k, p_cap)
        Mpos = [(p, M, mers) for (p, M, mers) in rows if M > 0]
        allM = [M for (_, M, _) in rows]
        print("\n" + "-" * 92)
        print(f"[n={n}]  dense scan p=1 mod {n}, p<= {p_cap:,}   (#primes scanned: {len(rows)})")
        if not allM:
            print("   no primes found.")
            continue
        print(f"   M>0 in {len(Mpos)}/{len(rows)} primes.  max M = {max(allM)}  "
              f"(sqrt(n)={math.sqrt(n):.2f}, n={n})")
        if Mpos:
            # onset: largest p with M>0 (the anomaly tail)
            last_pos = max(p for (p, _, _) in Mpos)
            # ratio p/n^4 at the last positive (thinness at onset)
            print(f"   largest p with M>0: {last_pos:,}  -> p^(1/4)/n = {last_pos**0.25/n:.3f} "
                  f"(M>0 needs n NOT << p^(1/4): the anomaly is a THICK-regime phenomenon)")
            # parity law check + 6|M check on the M>0 sample
            par_ok = all((M % 2 == 1) == mers for (_, M, mers) in Mpos)
            six = [(p, M) for (p, M, _) in Mpos if M % 6 != 0]
            print(f"   parity law (M odd <=> p|2^n-1) on M>0 sample: {'HOLDS' if par_ok else 'VIOLATED'}")
            print(f"   6|M law on M>0 sample: {'HOLDS' if not six else f'offenders {six[:8]}'}")
            # show the largest-M witnesses
            top = sorted(Mpos, key=lambda r: -r[1])[:8]
            print(f"   top-M witnesses (p, M, p|2^n-1):")
            for (p, M, mers) in top:
                fac = factorint(p - 1)
                v2 = fac.get(2, 0)
                print(f"      p={p:>10}  M={M:>3}  M/sqrt(n)={M/math.sqrt(n):.3f}  "
                      f"p|2^n-1={mers}  v2(p-1)={v2}  p^(1/4)/n={p**0.25/n:.2f}")

    # ----------------------------------------------------------------------------
    # (D) Fermat-factor obstruction range-cutoff: for each k, can ANY prime p with
    # n=2^k | p-1 divide a Fermat number F_j (j<k)?  (the u=1 active set)
    # ----------------------------------------------------------------------------
    print("\n" + "=" * 92)
    print("[D] u=1 obstruction reachability:  primes p with n|p-1 AND p|F_j  (F_j=2^{2^j}+1)")
    print("    For each k, list prime factors q of F_0..F_{k-1} with 2^k | q-1.")
    print("=" * 92)
    # known small Fermat factorizations
    fermat = {
        0: [3],
        1: [5],
        2: [17],
        3: [257],
        4: [65537],
        5: [641, 6700417],
        6: [274177, 67280421310721],
    }
    for k in range(2, 8):
        n = 2 ** k
        active = []
        for j in range(k):
            for q in fermat.get(j, []):
                if (q - 1) % n == 0:
                    active.append((j, q))
        print(f"   n={n:4d}:  active (j,q with 2^k|q-1) = {active if active else 'NONE'}"
              + (f"   <- u=1 reachable" if active else "   <- u=1 obstruction UNREACHABLE at this n"))
    print("\n   => If the active set is empty for the prize n=2^32, the famous 'u=1 / Mersenne'")
    print("      obstruction is VACUOUS at prize scale; the parity law has no instances and the")
    print("      open BGK magnitude is the generic (non-u=1) zero-sum-triple count.")


if __name__ == "__main__":
    run()
