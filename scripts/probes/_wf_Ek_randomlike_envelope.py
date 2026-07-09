#!/usr/bin/env python3
"""_wf_Ek_randomlike_envelope.py  (#407 — Ek-randomlike, FINAL: is the WORST-case C bounded?)

Follow-up found: TYPICAL prime is exactly random-like (E_r/(main+r!n^r)->1.000), but the WORST
prime per fixed-index sample shows c_5 climbing 1.06->1.87 across n=8..256 then dipping at 512.
SETTLE the worst-case: is it (i) genuine unbounded growth, (ii) prime-resonance with a structured
subgroup, or (iii) a small-n transient?

This probe:
  (A) WIDE sample: for each n, scan ALL primes p=m*n+1 with m in [4, M_MAX] (M_MAX large) and report
      the true max c_5 over the FULL sample (not just first 12).  Worst-case envelope, honestly.
  (B) For the worst prime found, DIAGNOSE: print the additive-energy excess factor and check whether
      the subgroup mu_n has an unusual additive structure (e.g. contains an arithmetic progression,
      or E_2 itself is anomalously large -> the whole tower inflates).
  (C) Plot c_5(worst) against log2(n) to see if the trend is ~log n (=> sqrt(log n) overshoot,
      survivable) or ~poly (=> wall).  Also report the FRACTION of primes with c_5 > 1.3
      (does the bad set shrink, stay, or grow with n?).
"""
import numpy as np
import sympy
import math

def primes_at_index_band(n, m_lo, m_hi):
    out = []
    for m in range(m_lo, m_hi + 1):
        p = m * n + 1
        if p > 60000:      # keep length-p convolutions cheap
            break
        if sympy.isprime(p):
            out.append((m, p))
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
    return ind, h

def conv_sparse(supp, b, p):
    out = np.zeros(p, dtype=object)
    bl = b.tolist()
    for s in supp:
        out[s:] += np.array(bl[:p - s], dtype=object)
        if s > 0:
            out[:s] += np.array(bl[p - s:], dtype=object)
    return out

def Er_exact(p, n, rmax):
    ind, h = subgroup_indicator(p, n)
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

print("=" * 100)
print("(A) WIDE worst-case envelope: max c_5 over ALL primes p=m*n+1, m in [4, large], p<60000.")
print("    Also: E_2/(n+r!... ) check, fraction of primes with c_5>1.3, and the worst (m,p).")
print("=" * 100)
print(f"{'n':>5} {'#primes':>8} | {'min c5':>7} {'med c5':>7} {'MAX c5':>7} | {'frac>1.3':>8} | worst (m,p) and its c_2..c_5")
log2n = []
worst_c5 = []
for a in range(3, 10):  # n=8..512
    n = 1 << a
    plist = primes_at_index_band(n, 4, 5000)
    rows = []
    for (m, p) in plist:
        res = Er_exact(p, n, 5)
        rows.append((c_r_of(res, n, p, 5), m, p, res))
    cs = sorted(x[0] for x in rows if not math.isnan(x[0]))
    rows.sort(key=lambda x: (math.nan if math.isnan(x[0]) else x[0]))
    mx = rows[-1]
    frac = sum(1 for c in cs if c > 1.3) / len(cs)
    c2 = c_r_of(mx[3], n, mx[2], 2); c3 = c_r_of(mx[3], n, mx[2], 3)
    c4 = c_r_of(mx[3], n, mx[2], 4)
    med = cs[len(cs) // 2]
    log2n.append(a); worst_c5.append(mx[0])
    print(f"{n:>5} {len(plist):>8} | {cs[0]:7.3f} {med:7.3f} {mx[0]:7.3f} | {frac:8.3f} | "
          f"m={mx[1]} p={mx[2]} c2={c2:.3f} c3={c3:.3f} c4={c4:.3f} c5={mx[0]:.3f}")

print()
print("=" * 100)
print("(C) TREND of worst c_5 vs log2(n):  fit c5_worst = A + B*log2(n)  (B>0 small => ~log growth).")
print("=" * 100)
xs = np.array(log2n, dtype=float)
ys = np.array(worst_c5, dtype=float)
B, A = np.polyfit(xs, ys, 1)
print(f"  data: " + " ".join(f"(log2n={int(x)},c5={y:.3f})" for x, y in zip(xs, ys)))
print(f"  linear fit in log2(n):  c5_worst ~ {A:.3f} + {B:.4f}*log2(n)")
print(f"  -> if extrapolate to prize a=44: c5_worst ~ {A + B*44:.3f}")
# also try power fit c5 ~ A * n^B  == log-log slope
posmask = ys > 0
lx = np.log(2.0 ** xs[posmask]); ly = np.log(ys[posmask])
Bp, Ap = np.polyfit(lx, ly, 1)
print(f"  power fit:  c5_worst ~ {math.exp(Ap):.3f} * n^{Bp:.4f}   (exponent ~0 => bounded; >0 => grows)")

print()
print("=" * 100)
print("(B) STRUCTURE DIAGNOSIS of the worst prime at the LARGEST n: is the subgroup an AP / coset")
print("    of a smaller additive-rigid set?  Report E_2 excess and #3-term APs inside mu_n.")
print("=" * 100)
for a in (7, 8):
    n = 1 << a
    plist = primes_at_index_band(n, 4, 5000)
    best = None
    for (m, p) in plist:
        res = Er_exact(p, n, 5)
        c5 = c_r_of(res, n, p, 5)
        if best is None or (not math.isnan(c5) and c5 > best[0]):
            best = (c5, m, p, res)
    _, m, p, res = best
    ind, h = subgroup_indicator(p, n)
    H = set(np.nonzero(ind)[0].tolist())
    # count 3-term APs a, a+d, a+2d all in H (d!=0): structured sets have many
    Hl = sorted(H)
    Hset = H
    aps = 0
    for a0 in Hl:
        for d in range(1, p):
            if (a0 + d) % p in Hset and (a0 + 2 * d) % p in Hset:
                aps += 1
    e2 = res[2]
    e2_rand = n ** 4 / p + 2 * n ** 2 - n  # main + Sidon diagonal (2n^2 - n)
    print(f" n={n} worst m={m} p={p}: c5={best[0]:.3f}  E2={e2}  E2/E2_rand={e2/e2_rand:.4f}  "
          f"3APs(incl trivial d)={aps}  (random ~ n^3/p={n**3/p:.1f})")

print()
print("READ:")
print("  power-fit exponent ~0 (c5 bounded) + worst-case is a structured-prime resonance")
print("    => RANDOM-LIKE generically; worst case a BOUNDED constant => moment arrow survives.")
print("  exponent >0 / strong log-trend that doesn't saturate => C grows => wall stands.")
