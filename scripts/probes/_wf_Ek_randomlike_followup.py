#!/usr/bin/env python3
"""_wf_Ek_randomlike_followup.py  (#407 — Ek-randomlike, FOLLOW-UP: kill prime-noise confound)

First pass showed c_r(n) bouncing in 0.7..1.6 with NO clean monotone trend, because the actual
index m drifts and c_r is SENSITIVE to the specific prime (small-index resonances). This pass:

  (A) For each n=2^a, scans the first K primes p=m*n+1 with small index m in [8,64] and reports
      MIN / MEDIAN / MAX of c_5(n)  -> separates a stable trend from prime noise.
  (B) Tracks max_p c_5(n): does the WORST-case constant GROW with n, or stay flat?
  (C) c_r vs r at the WORST prime per n: does deep r inflate the worst case?
  (D) E_r / (n^{2r}/p + r! n^r) for a typical prime: is the diagonal exactly r! n^r (random-like)?

excess = E_r - n^{2r}/p ;  ratio_r = excess/(r! n^r) ;  c_r = ratio_r^{1/r}.
RANDOM-LIKE <=> sup over primes of c_r(n) BOUNDED in n and r.
"""
import numpy as np
import sympy
import math
import statistics

def primes_at_index_band(n, m_lo, m_hi, K):
    out = []
    m = m_lo
    while len(out) < K and m <= m_hi:
        p = m * n + 1
        if sympy.isprime(p):
            out.append((m, p))
        m += 1
    return out

def subgroup_indicator(p, n):
    g = int(sympy.primitive_root(p))
    h = pow(g, (p - 1) // n, p)
    ind = np.zeros(p, dtype=np.int64)
    x = 1
    for _ in range(n):
        ind[x] = 1
        x = x * h % p
    assert int(ind.sum()) == n
    return ind

def conv_sparse(supp, b, p):
    out = np.zeros(p, dtype=object)
    bl = b.tolist()
    for s in supp:
        out[s:] += np.array(bl[:p - s], dtype=object)
        if s > 0:
            out[:s] += np.array(bl[p - s:], dtype=object)
    return out

def Er_exact(p, n, rmax):
    ind = subgroup_indicator(p, n)
    supp = np.nonzero(ind)[0].tolist()
    res = {}
    cur = ind.astype(object).copy()
    res[1] = int(sum(int(v) * int(v) for v in cur))
    for r in range(2, rmax + 1):
        cur = conv_sparse(supp, cur, p)
        res[r] = int(sum(int(v) * int(v) for v in cur))
    return res

fac = [math.factorial(r) for r in range(0, 12)]

def c_r_of(res, n, p, r):
    excess = res[r] - n ** (2 * r) / p
    ratio = excess / (fac[r] * n ** r)
    return ratio ** (1.0 / r) if ratio > 0 else float('nan')

print("=" * 96)
print("(A/B) c_5(n) over a SAMPLE of K primes per n (index m in [8,64]).")
print("     RANDOM-LIKE <=> max_p c_5(n) bounded (flat) in n.")
print("=" * 96)
R = 5
K = 12
print(f"{'n':>5} | {'#p':>3} {'min c5':>7} {'med c5':>7} {'MAX c5':>7} | (m,p) at the MAX")
maxc5_by_n = {}
for a in range(3, 10):
    n = 1 << a
    plist = primes_at_index_band(n, 8, 64, K)
    rows = []
    for (m, p) in plist:
        res = Er_exact(p, n, R)
        rows.append((c_r_of(res, n, p, R), m, p))
    cs = [x[0] for x in rows if not math.isnan(x[0])]
    rows.sort()
    mx = rows[-1]
    maxc5_by_n[n] = mx[0]
    print(f"{n:>5} | {len(cs):>3} {min(cs):7.3f} {statistics.median(cs):7.3f} {max(cs):7.3f} | "
          f"m={mx[1]} p={mx[2]}")

print()
vals = [maxc5_by_n[n] for n in sorted(maxc5_by_n)]
print("ENVELOPE max_p c_5(n):", " ".join(f"{n}:{maxc5_by_n[n]:.3f}" for n in sorted(maxc5_by_n)))
print(f"  -> n in [8..512]: min={min(vals):.3f} max={max(vals):.3f} (last-first)={vals[-1]-vals[0]:+.3f}")

print()
print("=" * 96)
print("(C) WORST-PRIME c_r vs r at fixed n (deep-r inflation of the worst case?).")
print("=" * 96)
for a in (5, 6, 7, 8):
    n = 1 << a
    plist = primes_at_index_band(n, 8, 64, K)
    best = None
    for (m, p) in plist:
        res = Er_exact(p, n, 5)
        c5 = c_r_of(res, n, p, 5)
        if best is None or (not math.isnan(c5) and c5 > best[0]):
            best = (c5, m, p)
    _, m, p = best
    res = Er_exact(p, n, 8)
    cells = [f"c_{r}={c_r_of(res,n,p,r):5.3f}" for r in range(2, 9)]
    print(f" n={n:>4} (worst m={m} p={p}): " + "  ".join(cells))

print()
print("=" * 96)
print("(D) E_r / (n^{2r}/p + r! n^r) for the MEDIAN prime (~1 <=> diagonal is exactly r! n^r).")
print("=" * 96)
for a in (6, 7, 8):
    n = 1 << a
    plist = primes_at_index_band(n, 8, 64, K)
    m, p = plist[len(plist) // 2]
    res = Er_exact(p, n, 6)
    cells = []
    for r in range(2, 7):
        pred = n ** (2 * r) / p + fac[r] * n ** r
        cells.append(f"r={r}:{res[r]/pred:5.3f}")
    print(f" n={n:>4} (med m={m} p={p}): " + "  ".join(cells))

print()
print("READ:")
print("  max_p c_5(n) flat in n & c_r flat/decaying in r => RANDOM-LIKE, C bounded, arrow closes.")
print("  max_p c_5(n) or worst-c_r climbing in n/r       => C grows, arrow overshoots -> wall.")
