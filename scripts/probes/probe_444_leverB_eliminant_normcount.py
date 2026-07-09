#!/usr/bin/env python3
r"""
probe_444_leverB_eliminant_normcount.py  (#444 Lever-B: eliminant / norm-degree bound on the surplus)

TASK (Lever-B). The char-p SUPPLY surplus Spur_r = E_r(mu_n/F_p) - E_r^{c0} counts solutions of
  sum_{i<=r} z_i = sum_{j<=r} z'_j  in F_p  but NOT in Z[zeta_n]
i.e. short <=2r-term +-1 sums alpha of 2^mu-th roots of unity with  p | N(alpha),  N=Res(Phi_n,alpha).

The char-0 count of the PAIRED (genuine, Z[zeta]-vanishing) ones is exactly (2r-1)!! (combinatorial
antipode pairing of z_i with -z'_j on the unit circle); these contribute the brute baseline E_r^{c0}.

Lever-B QUESTION: bound the EXTRA (non-paired, char-p only) ones.  Concretely:
   N_relations(n,k) := # length-k +-1 relations alpha (alpha != 0 in Z[zeta]) -- the "supply alphabet";
   for a fixed prize p, # of those with p | N(alpha) -- the char-p-active subset (=the surplus carriers).
If # char-p-active <= C * (2r-1)!! with C bounded, then E_r <= (2n log m)^r and the prize closes.

We test, EXACTLY (brute) at n=8,16,32 and small calibration primes, AND with a char-0-proxy prime:
  (A) CALIBRATION: E_r^{c0} brute, the (2r-1)!! paired count, confirm formula is an UPPER bound.
  (B) RELATION CENSUS at depth k=2r: total non-zero +-1 relations, their NORM distribution,
      and the eliminant/resultant degree deg_p N(alpha) as a function of length -- the "degree budget".
  (C) For a FIXED p (calibration + BabyBear/KoalaBear proxy): # length-<=2r relations with p|N(alpha),
      i.e. the actual char-p carrier count, vs (2r-1)!!.  Is the ratio bounded?  Does it grow with p?
  (D) The decisive structural test: does the carrier count depend on p only through DIVISIBILITY
      (p | some fixed integer N(alpha)) -- in which case the "bound" is just "how many alpha have
      prize-size norm divisor", i.e. the SAME divisibility wall -- or is there a genuine degree cap?

HONESTY: most likely (D) bottoms out at the divisibility wall (the count of carriers IS the surplus,
restating the problem).  We report which, and never fabricate a bound on Spur_r.
"""
import itertools, math
from collections import Counter
import sympy

X = sympy.symbols('X')

# ---------- primitives ----------
def primes_1_mod_n(n, lo, hi):
    return [p for p in range(max(lo, n+1), hi) if p % n == 1 and sympy.isprime(p)]

def subgroup(n, p):
    g = int(sympy.primitive_root(p)); h = pow(g, (p-1)//n, p)
    H = []; x = 1
    for _ in range(n):
        H.append(x); x = x*h % p
    return H

def char0_vec(cby, n):
    """reduce a coeff-by-exponent dict to the Q-basis 1..zeta^{n/2-1} (zeta^{j+n/2}=-zeta^j)."""
    half = n // 2
    v = [0]*half
    for e, c in cby.items():
        e %= n
        if e < half: v[e] += c
        else:        v[e-half] -= c
    return tuple(v)

def is_zero_char0(cby, n):
    return all(c == 0 for c in char0_vec(cby, n))

def dfac(k):
    r = 1
    while k > 1:
        r *= k; k -= 2
    return r

def E_r_char0_brute(n, r):
    cnt = Counter()
    for x in itertools.product(range(n), repeat=r):
        cnt[char0_vec(Counter(x), n)] += 1
    return sum(c*c for c in cnt.values())

def E_r_modp(n, p, r, H):
    cnt = Counter()
    for x in itertools.product(H, repeat=r):
        cnt[sum(x) % p] += 1
    return sum(c*c for c in cnt.values())

_NORM_CACHE = {}
def norm_alpha(cby, n):
    key = (n, tuple(sorted((e % n, c) for e, c in cby.items() if c)))
    if key in _NORM_CACHE:
        return _NORM_CACHE[key]
    poly = sum(c * X**(e % n) for e, c in cby.items())
    if poly == 0:
        _NORM_CACHE[key] = 0; return 0
    Phi = sympy.cyclotomic_poly(n, X)
    N = abs(int(sympy.resultant(sympy.Poly(poly, X), sympy.Poly(Phi, X))))
    _NORM_CACHE[key] = N
    return N


# ---------- (A) calibration ----------
def calibration():
    print("### (A) CALIBRATION: E_r^c0 brute vs (2r-1)!! n^r (paired upper bound) ###")
    ok = True
    for a in (3, 4, 5):
        n = 2**a
        for r in (1, 2):
            if n**r > 1_500_000: continue
            Ec = E_r_char0_brute(n, r)
            form = dfac(2*r-1) * n**r
            ok &= (Ec <= form) and (r != 1 or Ec == n)
            print(f"  n={n:>2} r={r}: E_r^c0(brute)={Ec:>8}   (2r-1)!!n^r={form:>8}   brute<=formula? {Ec<=form}")
    print(f"  CALIBRATION OK (E_1=n; brute is the real baseline, formula over-counts): {ok}\n")
    return ok


# ---------- (B) relation census at depth k ----------
def relation_census(n, kmax):
    r"""
    Enumerate all length-k +-1 relations alpha (normalize first sign +, distinct exponents) for
    k=2..kmax.  Report:
      - total non-zero-in-char0 relations  (the supply alphabet at that length)
      - how many ARE zero in char0 (the paired ones -- these are the (2k-1)!!-type combinatorics)
      - the NORM distribution (which primes can divide), and the resultant degree deg = phi(n).
    """
    half = n // 2
    print(f"### (B) RELATION CENSUS n={n}: length-k +-1 relations, char-0-zero vs nonzero, norm support ###")
    print(f"    (resultant deg_X = phi(n) = {sympy.totient(n)}; norm N(alpha) has at most that many"
          f" prime factors, counted w/ multiplicity, of bounded SIZE)")
    print(f"  {'k':>2} | {'#nonzero(char0) alpha':>22} | {'#char0-zero (paired)':>20} | {'max odd prime | N':>18} | {'#distinct odd primes':>20}")
    for k in range(2, kmax+1):
        nz = 0; paired = 0; primefac = set(); maxp = 1
        for exps in itertools.combinations(range(n), k):
            for signs in itertools.product((1, -1), repeat=k):
                if signs[0] != 1:  # fix overall sign
                    continue
                cby = {e: s for e, s in zip(exps, signs)}
                if is_zero_char0(cby, n):
                    paired += 1
                    continue
                nz += 1
                N = norm_alpha(cby, n)
                if N > 1:
                    for q in sympy.factorint(N):
                        if q > 2:
                            primefac.add(q); maxp = max(maxp, q)
        print(f"  {k:>2} | {nz:>22} | {paired:>20} | {maxp:>18} | {len(primefac):>20}")
    print()


# ---------- (C) carrier count for a FIXED p ----------
def carrier_count(n, p, kmax):
    r"""
    For a FIXED prime p (==1 mod n), count length-<=k +-1 relations alpha with p | N(alpha)
    (alpha != 0 in char0).  This is the # of char-p surplus carriers up to depth k.  Compare to
    (2r-1)!! at k=2r.  If carrier_count <= C*(2r-1)!! with C O(1) and p-independent -> movement.
    """
    rows = []
    for k in range(2, kmax+1):
        carriers = 0
        for exps in itertools.combinations(range(n), k):
            for signs in itertools.product((1, -1), repeat=k):
                if signs[0] != 1:
                    continue
                cby = {e: s for e, s in zip(exps, signs)}
                if is_zero_char0(cby, n):
                    continue
                if norm_alpha(cby, n) % p == 0:
                    carriers += 1
        rows.append((k, carriers))
    return rows


def main():
    calibration()

    # (B) census on n=8 and n=16 (n=32 phi=16, depth blows up -> cap)
    relation_census(8, 6)
    relation_census(16, 5)

    # (C) carrier count vs paired count, calibration primes + char-0 proxy
    print("### (C) CHAR-P CARRIER COUNT  vs paired (2r-1)!! at depth k=2r, FIXED p ###")
    print("    carrier(k) = # length-<=k +-1 relations alpha (!=0 char0) with p | N(alpha).")
    print("    The supply surplus Spur_r is generated by carriers at depth k=2r.\n")
    for n in (8, 16):
        small = primes_1_mod_n(n, 0, 700)
        # pick a calibration prime that IS a carrier (small) and a proxy (huge) one
        for p, tag in [(small[2], f"small calib p={small[2]}"),
                       (2013265921, "BabyBear 2^27|p-1"),
                       (3221225473, "KoalaBear 2^30|p-1")]:
            kmax = 6 if n == 8 else 4
            rows = carrier_count(n, p, kmax)
            print(f"  n={n}  {tag}:")
            for k, c in rows:
                r = k / 2.0
                paired = dfac(k-1) if k % 2 == 0 else None  # (k-1)!! paired relations at length k (even)
                pstr = f"(k-1)!!={dfac(k-1)}" if k % 2 == 0 else "odd-len (no full pairing)"
                print(f"      k={k}: char-p carriers={c:>4}   paired {pstr}   "
                      f"ratio carriers/paired={ (c/dfac(k-1)) if (k%2==0 and dfac(k-1)) else float('nan'):.3f}")
            print()

    # (D) decisive structural test: is carrier count a DIVISIBILITY phenomenon (p | fixed N) or a
    #     degree-capped count?  Show: the SAME finite list of norms N(alpha) governs ALL p; a prime
    #     is a carrier IFF it divides one of these fixed integers.  So "bounding carriers for prize p"
    #     == "how many of the fixed N(alpha) are divisible by prize p" == DIVISIBILITY of N(alpha).
    print("### (D) STRUCTURAL: carrier(p) = #{alpha : p | N(alpha)} -- a DIVISIBILITY count over a")
    print("    FIXED finite multiset of integers {N(alpha)}.  Eliminant/degree gives |{N(alpha)}| and")
    print("    a SIZE bound on each N(alpha), but NOT a bound on how many are divisible by the prize p.\n")
    n = 16
    # show the actual norm multiset at depth 4 and its prime support; the eliminant degree is phi(n).
    deg = int(sympy.totient(n))
    norms = []
    for k in (2, 3, 4):
        for exps in itertools.combinations(range(n), k):
            for signs in itertools.product((1, -1), repeat=k):
                if signs[0] != 1: continue
                cby = {e: s for e, s in zip(exps, signs)}
                if is_zero_char0(cby, n): continue
                N = norm_alpha(cby, n)
                if N > 1:
                    norms.append(N)
    allprimes = set()
    for N in norms:
        for q in sympy.factorint(N):
            if q > 2: allprimes.add(q)
    print(f"  n={n}: depth<=4 gives {len(norms)} nonzero norms; resultant deg_X = phi(n) = {deg}")
    print(f"         => each |N(alpha)| <= (max|alpha| coeff-sum)^phi(n) is SIZE-bounded, but the")
    print(f"         number of DISTINCT odd primes dividing some N(alpha) at this depth = {len(allprimes)}")
    print(f"         and they range up to {max(allprimes)}.  A prize p is a carrier IFF p divides one")
    print(f"         of these {len(norms)} integers.  The eliminant bounds their SIZE")
    print(f"         (<= H^phi(n), H=coeff height) NOT their count of large prime divisors.")
    print()
    print("  KEY: # length-2r relations alpha is C(n,<=2r)*2^{2r} = (2r-1)!! paired + EXTRA. The EXTRA")
    print("  alpha each have an integer norm N(alpha) of size <= (2r)^{phi(n)} (eliminant/Bezout). Prize")
    print("  p is a surplus carrier IFF p | N(alpha). # carriers = #{alpha : p | N(alpha)} -- governed")
    print("  by whether the prize p (size ~ n*2^128) divides a relation norm of size up to (2r)^{phi(n)}.")
    print("  At r~log m, phi(n)=2^{mu-1} is ENORMOUS => norms are astronomically large => generically")
    print("  divisible by the prize p.  The eliminant gives the SIZE budget, the divisibility is the WALL.")


if __name__ == "__main__":
    main()
