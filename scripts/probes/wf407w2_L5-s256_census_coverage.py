#!/usr/bin/env python3
"""
wf407-w2 / L5-s256 — census-coverage extent to s=256 (B3 follow-up).

QUESTION. At a FIXED prime field |F| = p < 2^256, for which dyadic fold scale
s = 2^m (with half-period N = s/2 = 2^(m-1)) is the finite-field collision/halo
census provably EQUAL to the char-0 census (no exotic mod-p coincidences)?

The in-tree depth-1 halo-free / collision threshold (HaloFreeThreshold.lean,
KKH26SumsOfRootsOfUnity.lean) is the resultant non-vanishing of a {-1,0,1}-coeff
polynomial of degree < N at a primitive 2^m-th root g in F_p.  Two engines:

  (L1, ell^1 / "coarse")  : |Res| <= (l1)^deg <= N^N    -> need  N^N      < p
  (L2, ell^2 / "Parseval"): Parseval halving of the bound -> need  (l2 thr) < p

The Parseval (DISPROOF_LOG O151) halving: |Res|^2 <= 8^{phi(2^m)} = 8^{N} so
|Res| <= 8^{N/2} = 2^{3N/2}, i.e. threshold exponent log2 = 3N/2 vs L1's
log2(N^N) = N*log2(N) = N*(m-1).

We compute both thresholds' log2 for m = 5..9 (s = 32..512) and check  thr < 2^256.
"""

import math

LOG2P = 256.0   # the prize ceiling |F| < 2^256

print("="*78)
print("CENSUS-COVERAGE THRESHOLDS  (need threshold log2 < 256 for |F| < 2^256)")
print("="*78)
print(f"{'m':>2} {'s=2^m':>7} {'N=s/2':>7} | {'L1 log2 = N*(m-1)':>20} {'<2^256?':>8} | "
      f"{'L2/Parseval = 3N/2':>20} {'<2^256?':>8}")
print("-"*78)

rows = []
for m in range(5, 10):
    s = 2**m
    N = 2**(m-1)
    # L1 (coarse resultant / ell^1):  |Res| <= N^N  -> log2 = N * log2(N) = N*(m-1)
    l1_log2 = N * (m - 1)
    # L2 (Parseval halving):  |Res| <= 8^{N/2} = 2^{3N/2} -> log2 = 1.5*N
    l2_log2 = 1.5 * N
    rows.append((m, s, N, l1_log2, l2_log2))
    print(f"{m:>2} {s:>7} {N:>7} | {l1_log2:>20.1f} {str(l1_log2<LOG2P):>8} | "
          f"{l2_log2:>20.1f} {str(l2_log2<LOG2P):>8}")

print()
print("INTERPRETATION")
print("-"*78)
# Largest s with coarse L1 threshold under 2^256
l1_ok = max((s for (m,s,N,l1,l2) in rows if l1 < LOG2P), default=0)
l2_ok = max((s for (m,s,N,l1,l2) in rows if l2 < LOG2P), default=0)
print(f"  coarse  (ell^1 / N^N)        covers up to  s = {l1_ok}")
print(f"  Parseval(ell^2 / 8^(N/2))    covers up to  s = {l2_ok}")
print()
print("  -> The Parseval halving moves the unconditional-coverage frontier")
print(f"     from s = {l1_ok} (coarse) to s = {l2_ok} (Parseval).")
