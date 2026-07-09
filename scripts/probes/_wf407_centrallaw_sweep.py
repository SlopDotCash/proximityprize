#!/usr/bin/env python3
"""
[centrallaw] MAIN SWEEP. Test R(n,p) = B / sqrt(n*ln(m)) for FLATNESS / TREND.

Two families:
  (A) FIXED-INDEX (prize regime): m held ~constant, n grows.  beta=log_n p -> 1.
  (B) THINNING (old BGK framing): n held ~constant, m grows.   thin subgroup.

For each (n,p) we compute B exactly (coset enumeration, O(m*n)=O(p) per prime).
We report B, sqrt(n), sqrt(n ln m), R=B/sqrt(n ln m), and C-fits.
"""
import numpy as np, math
from sympy import isprime, primitive_root, nextprime

def gauss_period_floor(p, n):
    m = (p - 1) // n
    g = primitive_root(p)
    gm = pow(g, m, p)
    mu = np.empty(n, dtype=np.int64)
    cur = 1
    for k in range(n):
        mu[k] = cur; cur = (cur * gm) % p
    tp = 2.0 * math.pi / p
    best = 0.0
    r = 1
    for t in range(m):
        prods = (r * mu) % p
        s = np.cos(tp*prods).sum() + 1j*np.sin(tp*prods).sum()
        a = abs(s)
        if a > best: best = a
        r = (r * g) % p
    return best, m

def find_prime_with(n, m_target):
    """Find prime p with n | (p-1) and (p-1)/n close to m_target. Search p = k*n+1."""
    best = None
    # we want (p-1)/n = m approx m_target => p approx n*m_target+1
    base = n * m_target + 1
    for delta in range(0, 200*n, n):  # step by n keeps n|(p-1)
        for cand in (base + delta, base - delta):
            if cand > 2 and (cand - 1) % n == 0 and isprime(cand):
                m = (cand - 1)//n
                if best is None or abs(m - m_target) < abs(best[1]-m_target):
                    best = (cand, m)
        if best is not None and abs(best[1]-m_target) <= 1:
            break
    return best

def find_prime_fixedm(n, m_target_list):
    """For fixed-index family: p = n*m + 1 prime for some m near targets."""
    for m in m_target_list:
        cand = n*m + 1
        if isprime(cand):
            return cand, m
    return None

print("="*92)
print("FAMILY A: FIXED-INDEX (prize regime) — m held ~constant, n GROWS.")
print("  If R grows in n at fixed m, the conjectured floor sqrt(n ln m) is WRONG.")
print("="*92)
print(f"{'n':>7} {'p':>11} {'m':>6} {'B':>10} {'sqrt(n)':>9} {'sqrt(n*ln m)':>12} {'R':>8} {'B/sqrt(n)':>9}")
# choose a target index m ~ 16 and grow n across two decades
import collections
familyA = collections.defaultdict(list)
for m_target in [8, 16, 32]:
    rows = []
    for n in [16, 24, 32, 48, 64, 96, 128, 192, 256, 384, 512, 768, 1024, 1536, 2048]:
        # find prime p = n*m+1 with m as close to m_target as possible
        res = None
        for m in [m_target, m_target+1, m_target-1, m_target+2, m_target-2,
                  m_target+3, m_target-3, m_target+4, m_target+5, m_target+6,
                  m_target+7, m_target+8]:
            if m < 2: continue
            cand = n*m + 1
            if isprime(cand):
                res = (cand, m); break
        if res is None: continue
        p, m = res
        B, mm = gauss_period_floor(p, n)
        R = B / math.sqrt(n * math.log(m))
        rows.append((n, p, m, B, R))
        print(f"{n:>7} {p:>11} {m:>6} {B:>10.4f} {math.sqrt(n):>9.3f} "
              f"{math.sqrt(n*math.log(m)):>12.3f} {R:>8.4f} {B/math.sqrt(n):>9.4f}")
    if rows:
        Rs = [r[4] for r in rows]
        ns = [r[0] for r in rows]
        # trend: linear fit of R vs ln(n)
        if len(Rs) >= 3:
            slope = np.polyfit(np.log(ns), Rs, 1)[0]
            print(f"   [m~{m_target}]  R range=[{min(Rs):.4f},{max(Rs):.4f}]  "
                  f"d R / d ln(n) slope = {slope:+.5f}   (FLAT if ~0)")
    print("-"*92)

print()
print("="*92)
print("FAMILY B: THINNING — n held ~constant, m GROWS (thin subgroup, beta away from 1).")
print("="*92)
print(f"{'n':>7} {'p':>11} {'m':>7} {'B':>10} {'sqrt(n*ln m)':>12} {'R':>8} {'B/sqrt(n)':>9}")
for n in [12, 16, 20]:
    rows = []
    for m_t in [4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384]:
        res = find_prime_with(n, m_t)
        if res is None: continue
        p, m = res
        if m < 3: continue
        B, mm = gauss_period_floor(p, n)
        R = B / math.sqrt(n * math.log(m))
        rows.append((n, p, m, B, R))
        print(f"{n:>7} {p:>11} {m:>7} {B:>10.4f} "
              f"{math.sqrt(n*math.log(m)):>12.3f} {R:>8.4f} {B/math.sqrt(n):>9.4f}")
    if len(rows) >= 3:
        Rs = [r[4] for r in rows]; ms = [r[2] for r in rows]
        slope = np.polyfit(np.log(ms), Rs, 1)[0]
        print(f"   [n={n}]  R range=[{min(Rs):.4f},{max(Rs):.4f}]  "
              f"d R / d ln(m) slope = {slope:+.5f}   (FLAT if ~0)")
    print("-"*92)
