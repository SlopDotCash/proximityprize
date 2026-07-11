#!/usr/bin/env python3
"""G102: is the depth-5 pair-concentration chain extremally tight? (exact integers)

The G87 depth-four discharge rests on J_4 <= (M+1) n^6 with M = pair-sum concentration,
fed by Stepanov (Garcia-Voloch / Heath-Brown-Konyagin): M <= ~4 n^{2/3}.  The depth-5
analog chain gives J_5 <= (M+1) n^8, reported ~2^26 over budget at M ~ n^{2/3}.

QUESTION: can ANY sound envelope B(n, M) (valid for all sets in all ambient groups)
do better than ~M n^8, i.e. could better constants/chains close depth 5 from (n, M) alone?

WITNESS (hybrid interval x Sidon): B_ET = Erdos-Turan Sidon set of size b (max elt < 2b^2),
S = { W*x + u : x in B_ET, u in [0, M) } with W := 5*M.
  - |S| = b*M            (div/mod injectivity)
  - pairConc(S) <= 2*M   (pair sums decompose, Sidon gives <=2, interval gives <=M)
  - 5-sums land in { W*sigma + t : sigma <= 5*(2b^2), t <= 5(M-1) }:
      |T| <= (10 b^2 + 1) * (5M - 4)
  - Cauchy-Schwarz:  J_5 >= n^10 / |T|   with n = bM.

TESTS
  (1) small-scale exact: build S, verify Sidon property of B_ET, pairConc bound, and
      exact J_5 (integer convolution) vs the CS floor and vs the chain (2M+1) n^8.
  (2) production arithmetic: n0 = 509 * 2^21 (~2^30), M = 2^21 (so pairConc <= 2^22 =
      4 n^{2/3} = exactly the Stepanov level).  Compare the CS floor with the exact
      depth-5 budget  B5 = 219!! * n^5 // (C(110,5)^2 * 105!)  at n = 2^30 (and n0).
  (3) the dichotomy margin: the largest constant M for which an (n,M)-envelope is not
      already refuted by the witness, i.e. M_max = max{ M : witnessFloor(n,M) <= B5 }.
  (4) empirical pair-sum concentration of REAL mu_n in F_p at small scales, to judge
      whether "M(mu_n) = O(1)" (the only surviving (n,M) route) is empirically plausible.
"""

import math
import sys
from collections import Counter


# ---------- Erdos-Turan Sidon set ----------

def sieve_primes(limit):
    s = [True] * (limit + 1)
    s[0] = s[1] = False
    for i in range(2, int(limit ** 0.5) + 1):
        if s[i]:
            for j in range(i * i, limit + 1, i):
                s[j] = False
    return [i for i, v in enumerate(s) if v]


def et_sidon(p):
    """Erdos-Turan: {2p*i + (i^2 mod p)} for i < p, subset of [0, 2p^2)."""
    return [2 * p * i + (i * i) % p for i in range(p)]


def is_sidon(A):
    c = Counter()
    for i, a in enumerate(A):
        for b in A[i:]:
            c[a + b] += 1
    return all(v <= 1 for v in c.values())


def pair_conc(S):
    """max over c != 0 (here: all c, S subset of positive naturals) of ordered pairCount."""
    c = Counter()
    for a in S:
        for b in S:
            c[a + b] += 1
    return max(c.values())


def exact_J5(S):
    """J_5 = sum_a N_5(a)^2 by exact integer polynomial convolution."""
    L = max(S)
    # coefficient array of sum_{s in S} x^s
    base = [0] * (L + 1)
    for s in S:
        base[s] += 1
    cur = base
    for _ in range(4):
        cur = poly_mul(cur, base)
    return sum(v * v for v in cur)


def poly_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                if bj:
                    out[i + j] += ai * bj
    return out


# ---------- production budget ----------

def dfact(k):
    r = 1
    while k > 1:
        r *= k
        k -= 2
    return r


def budget5(n, r=110, s=5):
    return (dfact(2 * r - 1) * n ** s) // (math.comb(r, s) ** 2 * math.factorial(r - s))


def witness_floor(b, M):
    n = b * M
    T = (10 * b * b + 1) * (5 * M - 4)
    return n ** 10 // T


def main():
    print("=" * 78)
    print("(1) small-scale exact hybrid witness")
    print("=" * 78)
    for (p, M) in [(5, 4), (7, 4), (7, 8), (11, 8)]:
        B = et_sidon(p)
        assert is_sidon(B), f"ET not Sidon at p={p}?!"
        W = 5 * M
        S = [W * x + u for x in B for u in range(M)]
        assert len(set(S)) == p * M
        mc = pair_conc(S)
        j5 = exact_J5(S)
        floor = witness_floor(p, M)
        chain = (2 * M + 1) * (p * M) ** 8
        print(f"  b={p:3d} M={M:3d} n={p*M:4d}: pairConc={mc:4d} (<= 2M={2*M}) "
              f"J5={j5:.3e}  CSfloor={floor:.3e}  chain={chain:.3e}")
        print(f"        J5/floor = {j5/floor:8.2f}   chain/J5 = {chain/j5:8.2f}")
        assert mc <= 2 * M
        assert j5 >= floor

    print()
    print("=" * 78)
    print("(2) production arithmetic (exact integers)")
    print("=" * 78)
    n30 = 2 ** 30
    B5_30 = budget5(n30)
    print(f"  depth-5 budget at n=2^30:  B5 = {B5_30:.4e}  (log2 = {math.log2(B5_30):.2f})")
    b, M = 509, 2 ** 21
    n0 = b * M
    fl = witness_floor(b, M)
    print(f"  witness b=509 (prime), M=2^21, n0=b*M={n0} (~2^{math.log2(n0):.3f})")
    print(f"  pairConc(S) <= 2M = 2^22;  GV level 4*n^(2/3) = {4*round(n30**(2/3)):.3e} = 2^22")
    print(f"  witness CS floor = {fl:.4e}  (log2 = {math.log2(fl):.2f})")
    print(f"  floor / B5(2^30) = 2^{math.log2(fl) - math.log2(B5_30):.2f}")
    B5_n0 = budget5(n0)
    print(f"  floor / B5(n0)   = 2^{math.log2(fl) - math.log2(B5_n0):.2f}")
    verdict = "NO-GO HOLDS: (n,M)-envelopes cannot close depth 5 at Stepanov M" \
        if fl > B5_30 else "no-go FAILS"
    print(f"  --> {verdict}")

    print()
    print("=" * 78)
    print("(3) dichotomy: largest M with witnessFloor <= B5 (the surviving (n,M) window)")
    print("=" * 78)
    # scan M (powers and refinement), b chosen so b*M ~ 2^30 with b prime-ish
    primes = sieve_primes(200000)
    lo, hi = 1, 2 ** 22
    while lo < hi:
        mid = (lo + hi + 1) // 2
        btarget = max(2, n30 // mid)
        bp = max(q for q in primes if q <= btarget) if btarget <= 200000 else btarget
        if witness_floor(bp, mid) <= budget5(bp * mid):
            lo = mid
        else:
            hi = mid - 1
    btarget = max(2, n30 // lo)
    bp = max(q for q in primes if q <= btarget) if btarget <= 200000 else btarget
    print(f"  M_max ~= {lo}  (b={bp}, n={bp*lo:.3e}) -> an (n,M)-route needs pair-sum")
    print(f"  concentration M(mu_n) <= ~{lo} at n=2^30 -- i.e. essentially CONSTANT.")

    print()
    print("=" * 78)
    print("(4) empirical pair-sum concentration of real mu_n in F_p")
    print("=" * 78)
    # subgroups mu_n of F_p^*, n | p-1, n ~ p^{1/4} (production beta ~ 4.27)
    cases = []
    for p in sieve_primes(4000000):
        if p < 10000:
            continue
        n = round(p ** 0.25)
        for m in range(max(4, n - 8), n + 9):
            if (p - 1) % m == 0:
                cases.append((p, m))
                break
    picked = []
    seen = set()
    for (p, m) in cases:
        k = int(math.log2(p))
        if k not in seen and m >= 8:
            seen.add(k)
            picked.append((p, m))
    for (p, m) in picked[:10]:
        g = None
        for cand in range(2, 200):
            x, ok = pow(cand, (p - 1) // m, p), True
            # x generates mu_m iff x^m=1 and x^(m/q) != 1 for prime q | m
            if pow(x, m, p) != 1:
                continue
            mm, qs = m, set()
            d = 2
            while d * d <= mm:
                if mm % d == 0:
                    qs.add(d)
                    while mm % d == 0:
                        mm //= d
                d += 1
            if mm > 1:
                qs.add(mm)
            if all(pow(x, m // q, p) != 1 for q in qs):
                g = x
                break
        if g is None:
            continue
        H = set()
        h = 1
        for _ in range(m):
            H.add(h)
            h = h * g % p
        c = Counter()
        Hl = sorted(H)
        for i, a in enumerate(Hl):
            for bb in Hl:
                s = (a + bb) % p
                if s:
                    c[s] += 1
        M_emp = max(c.values())
        print(f"  p={p:9d}  n={m:5d} (~p^{math.log(m)/math.log(p):.3f})  "
              f"M(mu_n)={M_emp:4d}   4n^(2/3)={4*m**(2/3):9.1f}")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
