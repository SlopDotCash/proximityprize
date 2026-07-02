#!/usr/bin/env python3
"""
probe_466_novel_n6_flattening_ladder.py  (#466 novel-math lane N6-arith-dynamics)

The empirical measure nu = (1/n) sum_{x in mu_n} delta_{x/p} on the circle is EXACTLY
invariant under the circle endomorphisms T_u : t -> u t mod 1 for every least-positive
representative u of mu_n.  Lane N6 asks whether effective measure rigidity /
Hochman-Shmerkin L^q flattening of convolutions gives leverage on
M(n,p) = max_{b!=0} |eta_b|.

This probe pins the three load-bearing quantitative claims of the lane note
(docs/kb/deltastar-466-novel-N6-arith-dynamics-2026-07-01.md):

  (1) THE EXACT DIMENSION LADDER.  D_2(nu^{*r}) = (2r*log n - log E_r)/log p, where
      E_r = (1/p) sum_{k mod p} |eta_k|^{2r} is the additive 2r-energy of mu_n.
      Prediction (the "three-regime law"): start exactly at 1/beta, climb at slope
      EXACTLY 1/beta per convolution while r < beta (Wick regime), saturate at
      1 - o(1) for r >= beta REGARDLESS of the size of the prize excess A_r
      (the functional is prize-blind past depth beta).

  (2) THE STRUCTURED/LACUNARY DICHOTOMY.  A small multiplier u for nu exists iff
      p | u^n - 1 (sparse structured family).  At the generalized-Fermat prime
      p = 65537 (mu_32 = <2>, a lacunary rank-1 semigroup = the measure-rigidity
      EXEMPT case) the measure is "atomic at every scale" (the Shmerkin inverse
      theorem's structure branch REALIZED) and eta_1 = n - c_B is near-maximal.
      Generic primes at the same and larger beta have min representative ~ p/n
      (no dynamics at all).

  (3) THE COARSE-SCALE PROFILE.  Renyi-2 dimension profile of nu across dyadic
      scales: generic primes ~ flat (dimension ~ 1 at coarse scales, atoms
      resolve at scale ~ n/p); the GF prime shows the geometric-progression
      atomic profile.

Everything is exact arithmetic + FFT at p ~ 6.5e4 .. 1.05e6; runtime seconds.
"""

import numpy as np
import math
import sys


# ----------------------------------------------------------------------------- primes
def is_prime(x: int) -> bool:
    if x < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if x % q == 0:
            return x == q
    d, s = x - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        v = pow(a, d, x)
        if v in (1, x - 1):
            continue
        for _ in range(s - 1):
            v = v * v % x
            if v == x - 1:
                break
        else:
            return False
    return True


def find_primes_1modn(start: int, n: int, count: int):
    out = []
    p = start - (start % n) + 1
    while len(out) < count:
        if p > start and is_prime(p):
            out.append(p)
        p += n
    return out


# ----------------------------------------------------------------------------- subgroup
def subgroup(p: int, n: int):
    """The unique multiplicative subgroup of order n in F_p^* (n | p-1)."""
    assert (p - 1) % n == 0
    m = (p - 1) // n
    # find a generator of F_p^*
    fac = []
    t = p - 1
    d = 2
    while d * d <= t:
        if t % d == 0:
            fac.append(d)
            while t % d == 0:
                t //= d
        d += 1
    if t > 1:
        fac.append(t)
    g = None
    for cand in range(2, p):
        if all(pow(cand, (p - 1) // q, p) != 1 for q in fac):
            g = cand
            break
    h = pow(g, m, p)  # generator of mu_n
    elems = []
    x = 1
    for _ in range(n):
        elems.append(x)
        x = x * h % p
    assert len(set(elems)) == n
    return sorted(elems)


# ----------------------------------------------------------------------------- analysis
def analyze(p: int, n: int, rmax: int = 10, label: str = ""):
    mu = subgroup(p, n)
    beta = math.log(p) / math.log(n)
    v = np.zeros(p)
    for x in mu:
        v[x] = 1.0
    eta = np.fft.fft(v)  # eta[k] = sum_x e(-2pi i k x / p); |eta| is what we need
    a = np.abs(eta)
    a2 = a * a
    # Parseval check: sum_{k!=0} |eta_k|^2 = n(p-n)
    pars = a2[1:].sum()
    pars_exact = n * (p - n)
    M = a[1:].max()
    kstar = int(np.argmax(a[1:]) + 1)
    C = M / math.sqrt(n * math.log(p / n))
    # exclude the trivial multipliers 1 and p-1 (T_1 = id, T_{p-1} = the reflection
    # t -> -t on the grid: an isometry, no dynamics)
    minrep = min(x for x in mu if x not in (1, p - 1))
    # small-multiplier audit: u <= 1000 with u^n = 1 mod p
    small_mults = [u for u in range(2, 1001) if pow(u, n, p) == 1]

    print(f"== {label}: p = {p}  n = {n}  beta = {beta:.3f}  m = {(p-1)//n}")
    print(f"   Parseval sum_(k!=0)|eta|^2 = {pars:.3f}  vs exact n(p-n) = {pars_exact}"
          f"   (rel err {abs(pars-pars_exact)/pars_exact:.2e})")
    print(f"   M = {M:.4f}  at k* = {kstar}   C = M/sqrt(n ln(p/n)) = {C:.4f}")
    print(f"   min representative of mu_n = {minrep}   (p/n = {p//n};"
          f" ratio = {minrep/(p/n):.3f})")
    print(f"   small multipliers u<=1000 (p | u^n - 1): {small_mults if small_mults else 'NONE'}")

    # dimension ladder
    logp = math.log(p)
    logn = math.log(n)
    print(f"   r | D_2(nu^(*r)) | increment | Wick pred    | A_r/Wick_r | regime")
    prev = None
    a2r = np.ones_like(a2[1:])
    for r in range(1, rmax + 1):
        a2r = a2r * a2[1:]              # |eta_k|^{2r}, k != 0
        S_r = a2r.sum()
        E_r = (n ** (2 * r) + S_r) / p  # the full energy count
        D2 = (2 * r * logn - math.log(E_r)) / logp
        A_r = S_r / p                   # DC-subtracted energy
        wick = math.prod(range(1, 2 * r, 2)) * float(n) ** r  # (2r-1)!! n^r
        wick_ratio = A_r / wick
        # Wick-conditional prediction for D_2
        E_wick = n ** (2 * r) / p + wick
        D2_wick = (2 * r * logn - math.log(E_wick)) / logp
        inc = "" if prev is None else f"{D2-prev:+.4f}"
        regime = "Wick" if r < beta else "saturated"
        print(f"   {r:2d} |   {D2:.4f}    |  {inc:>7s}  |  {D2_wick:.4f}     "
              f"|  {wick_ratio:8.3f}  | {regime}")
        prev = D2

    # coarse-scale Renyi-2 profile of nu itself
    pos = np.array(sorted(x / p for x in mu))
    prof = []
    smax = int(math.log2(p)) + 1
    for s in range(1, smax + 1):
        cells = np.floor(pos * (1 << s)).astype(np.int64)
        _, cnt = np.unique(cells, return_counts=True)
        mass2 = ((cnt / n) ** 2).sum()
        D2s = math.log(1.0 / mass2) / (s * math.log(2)) if mass2 < 1 else 0.0
        prof.append(D2s)
    prof_s = "  ".join(f"{x:.2f}" for x in prof)
    print(f"   coarse Renyi-2 dim profile D_2(nu; 2^-s), s=1..{smax}:")
    print(f"     {prof_s}")
    print()
    return dict(p=p, M=M, C=C, minrep=minrep)


def main():
    n = 32
    print("#466 lane N6-arith-dynamics: the flattening ladder in exact coordinates")
    print("=" * 78)
    # (a) generalized-Fermat prime: mu_32 = <2> (lacunary rank-1 invariance semigroup)
    analyze(65537, n, label="GF/lacunary  F4 = 2^16+1")
    # (b) generic control at the SAME beta ~ 3.2
    for p in find_primes_1modn(66000, n, 2):
        analyze(p, n, label="generic beta~3.2")
    # (c) generic primes at beta = 4  (p ~ n^4 = 2^20)
    for p in find_primes_1modn(1 << 20, n, 2):
        analyze(p, n, label="generic beta~4.0")

    # prize-point arithmetic for the note (no computation, just the constants)
    print("=" * 78)
    print("Prize-point constants (n = 2^30, p ~ n^4 = 2^120):")
    N = 2.0 ** 30
    lp = 120 * math.log(2)
    lpn = 90 * math.log(2)
    tgt = math.sqrt(N * lpn)
    print(f"  ln p = {lp:.1f}   r* = ln p ~ {lp:.0f}   target sqrt(n ln(p/n)) = 2^"
          f"{math.log2(tgt):.2f}")
    print(f"  prize gap n / target = 2^{math.log2(N/tgt):.2f} = p^"
          f"{math.log2(N/tgt)/120:.4f}")
    cstar = math.log(math.sqrt(N / lpn)) / math.log(lp)
    print(f"  log-rate sufficiency exponent c* (|eta| <= n (ln p)^-c suffices iff c >= c*):"
          f" c* = {cstar:.3f}")
    # dimension blindness at depth r* : DC term vs prize excess vs BGK excess
    r = 83
    log2_dc = 0.0  # normalized: E_r * p / n^{2r} = 1 + p A_r / n^{2r}
    log2_wick = 120 + sum(math.log2(j) for j in range(1, 2 * r, 2)) - 30 * r
    log2_bgk = 2 * r * math.log2(0.99 ** 1)  # (M/n)^{2r} with M = n^{0.99}: 2r*(-0.01*30)
    log2_bgk = -2 * r * 0.01 * 30
    log2_prize = 2 * r * (math.log2(tgt) - 30)
    print(f"  at depth r = {r}: relative L2 contributions (log2, vs DC term = 0):")
    print(f"    Wick excess  : {log2_wick:9.1f}")
    print(f"    prize-M floor: {log2_prize:9.1f}")
    print(f"    BGK-M floor  : {log2_bgk:9.1f}")
    print("  => D_2(nu^{*r}) = 1 - o(1) in EVERY scenario: the L^q-dimension functional")
    print("     cannot distinguish prize-true from BGK-tight at any saturated depth.")


if __name__ == "__main__":
    sys.exit(main())
