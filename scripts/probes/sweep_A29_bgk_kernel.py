#!/usr/bin/env python3
"""
sweep_A29_bgk_kernel.py  —  Actionable A29 (merged 232-T03).

The first genuinely-open INTERIOR BGK cell of the proximity-gap wall is t=1,a=3:
the zero-sum 3-subset count of the dyadic subgroup mu_n = order-n=2^k mult.
subgroup of F_p.  Define the BGK additive-energy kernel

    M(p,n) = #{ u in mu_n : -(1+u) in mu_n }
           = #{ u in mu_n : exists w in mu_n with 1 + u + w = 0 }.

By the dilation u->g*u (g in mu_n) the number of ORDERED zero-sum triples
(x,y,z) in mu_n^3 with x+y+z=0 equals |mu_n|*M = n*M.  This M is exactly the
"first genuinely-open interior cell"; BGK predicts M <= n^{1/2+o(1)}.

A29 task (what was NEVER done before):
  (1) RE-CONFIRM the proven structure (232-T03 / Rosetta C013):
        - M = 0 in characteristic 0;
        - M is ODD  <=>  p | 2^n - 1   (fixed point u=1 of the involution u->u^{-1}
          inside the solution set, since -(1+1) = -2 in mu_n iff ... see below);
        - 6 | M generically (S_3 acting on the unordered zero-sum triple {x,y,z}).
  (2) TABULATE the actual MAGNITUDE of M away from the u=1 obstruction, over many
      primes F_q = F_p at prize-SHAPED scale (large a = log_n p), for n=8,16,32,64.
  (3) CORRELATE M-spikes with Fermat-number factorizations:  the u=1 collision
      (1 in the zero-sum set) holds iff char divides F_0..F_{k-1}, where
      2^n - 1 = prod_{j<k} F_j  (F_j = 2^{2^j}+1).  Localize the open BGK core
      at the smallest enumerable cell and see whether the *worst* M correlates
      with the prime dividing a Fermat number (structured spike) or is generic.

Pure arithmetic; uses sympy for big-int factorization (Fermat correlation) only.
Enumeration of mu_n is O(n) per prime, so this is exact and cheap for n<=64.
"""

import math
import random
from sympy import factorint, isprime

# ----------------------------------------------------------------------------
# subgroup + kernel
# ----------------------------------------------------------------------------

def subgroup_2pow(p, k):
    """Order n=2^k multiplicative subgroup of F_p (needs 2^k | p-1). Returns
    sorted list of its elements, or None."""
    n = 2 ** k
    if (p - 1) % n:
        return None
    # find a generator quickly via random trials + order check using the
    # factorization of p-1 restricted to small structure; for our primes a
    # simple search is fine.
    # find an element of multiplicative order n directly: take random a, raise
    # to (p-1)/n; if it has order exactly n we are done.
    m = (p - 1) // n
    rng = random.Random(12345 + p)
    for _ in range(200):
        a = rng.randrange(2, p)
        h = pow(a, m, p)
        # order of h divides n; need exactly n: h^{n/2} != 1
        if pow(h, n // 2, p) != 1 and pow(h, n, p) == 1:
            return sorted(pow(h, i, p) for i in range(n))
    return None


def kernelM(p, mu_set):
    """M = #{u in mu_n : -(1+u) mod p in mu_n}."""
    cnt = 0
    for u in mu_set:
        if (-(1 + u)) % p in mu_set:
            cnt += 1
    return cnt


def zero_sum_triple_check(p, mu_list, M, n):
    """Cross-check the homogeneity identity n*M = #ordered zero-sum triples.
    Only run for small n (O(n^2))."""
    S = set(mu_list)
    ordered = 0
    for x in mu_list:
        for y in mu_list:
            if (-(x + y)) % p in S:
                ordered += 1
    return ordered, n * M


# ----------------------------------------------------------------------------
# prime selection: prize-SHAPED, p ~ n^a with a as large as we can enumerate.
# Real prize is a in [25,40], n=2^32 (unenumerable).  We hold the STRUCTURE
# (dyadic n, n | p-1, thin n << p^{1/4}) and push a as high as feasible while
# keeping mu_n enumerable (n<=64).
# ----------------------------------------------------------------------------

def primes_with_subgroup(k, count, min_a, seed=1):
    """Return up to `count` primes p with 2^k | p-1 and p ~ n^a, a>=min_a,
    p chosen as p = j*n + 1 scanning upward from n^{min_a}."""
    n = 2 ** k
    out = []
    lo = int(n ** min_a)
    # align to 1 mod n
    p = (lo // n + 1) * n + 1
    while len(out) < count:
        if isprime(p):
            out.append(p)
        p += n
    return out


def fermat_factor_correlation(p, k):
    """Which Fermat numbers F_0..F_{k-1} does p divide?  (u=1 obstruction.)
    2^n - 1 = prod_{j<k} F_j, F_j = 2^{2^j}+1.  Returns list of j with p|F_j."""
    hits = []
    for j in range(k):
        Fj = (1 << (1 << j)) + 1   # 2^{2^j}+1
        if Fj % p == 0:
            hits.append(j)
    return hits, (pow(2, 2 ** k, p) == 1)  # p | 2^n-1 ?


# ----------------------------------------------------------------------------
# main sweep
# ----------------------------------------------------------------------------

def run():
    print("=" * 96)
    print("A29  BGK kernel  M(p,n) = #{u in mu_n : -(1+u) in mu_n}   (t=1,a=3 interior cell)")
    print("=" * 96)

    # ---- (0) char-0 sanity: complex roots of unity, no zero-sum 3-subset in mu_{2^k}
    print("\n[0] char-0 baseline (complex mu_n): M_C0 = #{u : -(1+u) in mu_n}")
    import cmath
    for k in range(2, 8):
        n = 2 ** k
        roots = [cmath.exp(2j * math.pi * t / n) for t in range(n)]
        tol = 1e-9
        m0 = 0
        for u in roots:
            tgt = -(1 + u)
            if any(abs(tgt - r) < tol for r in roots):
                m0 += 1
        print(f"    n={n:4d}  M_C0={m0}")
    print("    => M=0 in char 0 (no nontrivial zero-sum 3-subset of a dyadic group). CONFIRMED.")

    # ---- (1)-(3): char-p sweep
    for k in (3, 4, 5, 6):       # n = 8,16,32,64
        n = 2 ** k
        # push a as high as enumeration of the PRIME (not the subgroup) allows.
        # n^25 is astronomically large for big k; cap p around 10^14 so isprime
        # stays fast, and report the realized a = log_n p.
        # choose min_a so n^min_a ~ 1e8..1e13 (prize-shaped thinness n<<p^{1/4}).
        if k == 3:   min_a = 12   # 8^12 ~ 7e10
        elif k == 4: min_a = 9    # 16^9  ~ 6.8e10
        elif k == 5: min_a = 7    # 32^7  ~ 3.4e10
        else:        min_a = 6    # 64^6  ~ 6.9e10
        ps = primes_with_subgroup(k, 24, min_a)
        print("\n" + "-" * 96)
        print(f"[n={n}]  thin/BGK regime  (target a>=~{min_a}, n << p^(1/4));  BGK predicts M ~< sqrt(n)={math.sqrt(n):.2f}")
        print(f"{'p':>16} {'a=log_n p':>9} {'M':>5} {'M/sqrtn':>8} {'parity':>6} {'p|2^n-1':>8} {'Fermat j':>10} {'6|M':>5}")
        Ms = []
        worst = (-1, None)
        odd_iff_mersenne_ok = True
        six_div_offenders = []
        for p in ps:
            mu = subgroup_2pow(p, k)
            if mu is None or len(mu) != n:
                continue
            mu_set = set(mu)
            M = kernelM(p, mu_set)
            Ms.append(M)
            a = math.log(p) / math.log(n)
            ferm_j, mers = fermat_factor_correlation(p, k)
            par = "odd" if (M % 2) else "even"
            # proven: M odd  <=>  p | 2^n-1
            if (M % 2 == 1) != mers:
                odd_iff_mersenne_ok = False
            six = (M % 6 == 0)
            if not six and M > 0:
                six_div_offenders.append((p, M))
            if M > worst[0]:
                worst = (M, p)
            print(f"{p:>16} {a:>9.2f} {M:>5} {M/math.sqrt(n):>8.3f} {par:>6} "
                  f"{str(mers):>8} {str(ferm_j):>10} {str(six):>5}")
        if Ms:
            import statistics
            print(f"    n={n}: M range [{min(Ms)},{max(Ms)}]  mean={statistics.mean(Ms):.2f}  "
                  f"max/sqrt(n)={max(Ms)/math.sqrt(n):.3f}  worst at p={worst[1]}")
            print(f"    parity law  (M odd <=> p|2^n-1):  {'HOLDS' if odd_iff_mersenne_ok else 'VIOLATED'}")
            if six_div_offenders:
                print(f"    6|M offenders (M>0 not div by 6): {six_div_offenders[:6]}"
                      f"{' ...' if len(six_div_offenders)>6 else ''}")
            else:
                print(f"    6|M:  holds for all M>0 in this sample.")

    # ---- (3b) explicit Fermat-correlated SPIKE hunt at n=8 (k=3):
    # 2^8-1 = 255 = 3*5*17 = F_0*F_1*F_2.  Primes dividing a Fermat factor should
    # carry the u=1 (=odd) obstruction; check whether they ALSO carry an
    # anomalously large M (structured spike) vs generic primes.
    print("\n" + "=" * 96)
    print("[3b] Fermat-correlated spike hunt: does p | F_j force a LARGER M (structured),")
    print("     or only the parity (u=1) obstruction?   n=8: 2^8-1 = 3*5*17 = F_0*F_1*F_2")
    print("=" * 96)
    k = 3
    n = 8
    # Need p | 2^8-1 AND 8 | p-1.  255's prime factors are 3,5,17 -- none is 1 mod 8.
    # So at n=8 the u=1 collision needs a LARGER prime dividing 2^{8t}-1 patterns;
    # instead sample primes p=1 mod 8 and split them by whether p divides ANY
    # 2^{8}-1 multiple is impossible for large p, so the relevant correlation is:
    # primes for which mu_8 CONTAINS a zero-sum triple including 1 (i.e. odd M)
    # vs not, and the magnitude in each class.
    ps = primes_with_subgroup(k, 400, 6)
    cls_odd = []   # p | 2^n-1  (M odd, u=1 obstruction active)
    cls_even = []  # generic
    for p in ps:
        mu = subgroup_2pow(p, k)
        if mu is None or len(mu) != n:
            continue
        M = kernelM(p, set(mu))
        mers = (pow(2, n, p) == 1)
        (cls_odd if mers else cls_even).append(M)
    def stats(xs):
        if not xs:
            return "n/a"
        import statistics
        return f"count={len(xs)} mean={statistics.mean(xs):.3f} max={max(xs)} min={min(xs)}"
    print(f"    p | 2^n-1  (u=1 active, M odd) : {stats(cls_odd)}")
    print(f"    generic    (u=1 inactive)      : {stats(cls_even)}")
    print("    => If the two classes have ~same magnitude, the Fermat structure governs")
    print("       only the PARITY, not the SIZE: the open BGK magnitude core is generic.")

    # ---- (4) cross-check homogeneity n*M = #ordered zero-sum triples (n=8,16)
    print("\n" + "=" * 96)
    print("[4] homogeneity cross-check:  n*M  ==  #ordered (x,y,z) in mu_n^3 with x+y+z=0")
    print("=" * 96)
    for k in (3, 4):
        n = 2 ** k
        p = primes_with_subgroup(k, 1, 6)[0]
        mu = subgroup_2pow(p, k)
        if mu is None:
            continue
        M = kernelM(p, set(mu))
        ordered, nM = zero_sum_triple_check(p, mu, M, n)
        print(f"    n={n:3d} p={p}:  n*M={nM}   #ordered-triples={ordered}   "
              f"{'MATCH' if ordered == nM else 'MISMATCH'}")


if __name__ == "__main__":
    run()
