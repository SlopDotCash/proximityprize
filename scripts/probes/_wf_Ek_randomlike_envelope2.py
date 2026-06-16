#!/usr/bin/env python3
"""_wf_Ek_randomlike_envelope2.py  (#407 — Ek-randomlike, FINAL fast: worst-case C bounded?)

Uses FLOAT FFT for E_r (validated EXACT-equal to integer counting in _wf_Ek-randomlike_0.py:
n=16 p=193 r=1..4 matched to the digit), so the wide prime sweep is cheap. AP count via FFT too.

GOAL: typical prime is exactly random-like (E_r/(main+r!n^r)->1.000). Settle the WORST prime per
fixed-index sample: is max_p c_5(n) a bounded constant, ~log n, or ~poly?
"""
import numpy as np
import sympy
import math

def primes_at_index_band(n, m_lo, m_hi, pmax):
    out = []
    for m in range(m_lo, m_hi + 1):
        p = m * n + 1
        if p > pmax:
            break
        if sympy.isprime(p):
            out.append((m, p))
    return out

def subgroup_indicator(p, n):
    g = int(sympy.primitive_root(p))
    h = pow(g, (p - 1) // n, p)
    ind = np.zeros(p)
    x = 1
    for _ in range(n):
        ind[x] = 1.0
        x = x * h % p
    return ind

def Er_via_fft(p, n, rmax):
    """E_r = (1/p) sum_b |S(b)|^{2r}; |S|^2 = FFT(indicator) abs2. EXACT (matches int counting)."""
    ind = subgroup_indicator(p, n)
    S = np.fft.fft(ind)
    a2 = np.abs(S) ** 2
    return {r: float(np.sum(a2 ** r) / p) for r in range(1, rmax + 1)}, a2, ind

fac = [math.factorial(r) for r in range(0, 14)]

def c_r_of(res, n, p, r):
    excess = res[r] - n ** (2 * r) / p
    ratio = excess / (fac[r] * n ** r)
    return ratio ** (1.0 / r) if ratio > 0 else float('nan')

print("=" * 104)
print("(A) WIDE worst-case envelope (FLOAT FFT, validated exact): max c_5 over ALL primes p=m*n+1,")
print("    m in [4, large], p<=PMAX.  min/med/MAX c5, fraction c5>1.3, worst (m,p) with c2..c5.")
print("=" * 104)
PMAX = 200000
print(f"{'n':>5} {'#p':>5} | {'min c5':>7} {'med c5':>7} {'MAX c5':>7} | {'frac>1.3':>8} | worst (m,p): c2 c3 c4 c5")
log2n = []; worst_c5 = []
worst_record = {}
for a in range(3, 11):  # n=8..1024
    n = 1 << a
    plist = primes_at_index_band(n, 4, 8000, PMAX)
    rows = []
    for (m, p) in plist:
        res, a2, ind = Er_via_fft(p, n, 5)
        rows.append((c_r_of(res, n, p, 5), m, p, res))
    cs = sorted(x[0] for x in rows if not math.isnan(x[0]))
    rows.sort(key=lambda x: (1e9 if math.isnan(x[0]) else x[0]))
    mx = rows[-1]
    worst_record[n] = (mx[1], mx[2])
    frac = sum(1 for c in cs if c > 1.3) / len(cs)
    c2 = c_r_of(mx[3], n, mx[2], 2); c3 = c_r_of(mx[3], n, mx[2], 3); c4 = c_r_of(mx[3], n, mx[2], 4)
    med = cs[len(cs) // 2]
    log2n.append(a); worst_c5.append(mx[0])
    print(f"{n:>5} {len(plist):>5} | {cs[0]:7.3f} {med:7.3f} {mx[0]:7.3f} | {frac:8.3f} | "
          f"m={mx[1]} p={mx[2]}: {c2:.2f} {c3:.2f} {c4:.2f} {mx[0]:.2f}")

print()
print("=" * 104)
print("(C) TREND of worst c_5 vs n.")
print("=" * 104)
xs = np.array(log2n, dtype=float)
ys = np.array(worst_c5, dtype=float)
B, A = np.polyfit(xs, ys, 1)
print("  data:", " ".join(f"(a={int(x)},c5={y:.3f})" for x, y in zip(xs, ys)))
print(f"  linear-in-log2n fit:  c5_worst ~ {A:.3f} + {B:.4f}*log2(n);  extrap a=44 -> {A+B*44:.3f}")
lx = np.log(2.0 ** xs); ly = np.log(ys)
Bp, Ap = np.polyfit(lx, ly, 1)
print(f"  power fit:  c5_worst ~ {math.exp(Ap):.3f} * n^{Bp:.4f}  (exp~0 bounded; >0 grows)")

print()
print("=" * 104)
print("(B) STRUCTURE of the worst prime at large n: E_2 excess & FFT 3-AP count vs random.")
print("=" * 104)
for a in (8, 9, 10):
    n = 1 << a
    if n not in worst_record:
        continue
    m, p = worst_record[n]
    res, a2, ind = Er_via_fft(p, n, 5)
    # 3-term AP count: T3 = (1/p) sum_b S(b)^2 * conj(S(2b))? Use real count:
    # #{(a,d): a,a+d,a+2d in H} = (1/p) sum_b Shat(b)*Shat(b)*conj(Shat(2b))  (real part), where
    # Shat(b)=sum_{x in H} e_p(b x). Standard 3AP formula.
    S = np.fft.fft(ind)
    idx2 = (2 * np.arange(p)) % p
    T3 = float(np.real(np.sum(S * S * np.conj(S[idx2]))) / p)
    e2 = res[2]; e2_rand = n ** 4 / p + 2 * n ** 2 - n
    T3_rand = n ** 3 / p  # random-set expected 3AP (incl trivial d=0 contributes n)
    print(f" n={n} worst m={m} p={p}: c5={c_r_of(res,n,p,5):.3f}  E2/E2rand={e2/e2_rand:.4f}  "
          f"3AP={T3:.1f} (rand~{T3_rand:.1f}, +n={n} trivial)  ratio={T3/(T3_rand+n):.3f}")

print()
print("READ: bounded worst-case (power exp ~0, flat) + structured-prime resonance => RANDOM-LIKE,")
print("      arrow survives.  Persistent log/poly climb that doesn't saturate => C grows => wall.")
