#!/usr/bin/env python3
"""
#466 r=3 R309: extending the lag/Weil machinery to the r=4 tower rung —
identities, q-scaling exponents, and the depth-2 rigidity question.

Setup: S = zero-removed Jacobi ladder on ℤ/m; lag₁(t) = Σ_j S_{j+t}·conj(S_j)
(depth-1 autocorrelation); W = S⋆S (self-convolution); lag₂(t) = Σ_c W_{c+t}·conj(W_c).

IDENTITIES (formalized in Lean, checked here at machine precision):
 (L1) Σ_a‖Ŝ‖⁴ = m·Σ_t‖lag₁(t)‖²      (autocorrelation Parseval, depth 1)
 (L2) Σ_a‖Ŝ‖⁸ = m·Σ_t‖lag₂(t)‖²      (same, applied to W: Ŵ = Ŝ²)

MECHANISM QUESTION (decides the honest r=4 named input): for t ≠ 0,
 - depth-1: lag₁(t) collapses (R30/R31) to two-character sums with ONE free
   F_q variable → curve Weil predicts ‖lag₁(t)‖ ~ C·poly(m)·√q  (exponent 1/2);
 - depth-2: lag₂(t) is quartic in J; linearization needs TWO free variables →
   surface (Deligne) scale would be ~C·poly(m)·q (exponent 1); a purely
   random/Gaussian angle model predicts ‖lag₂(t)‖ ~ √m·m·q² (exponent 2).
Measure the q-exponents at fixed m by regression over a long prime ladder.

CONSEQUENCE CHECK: Weil-rigidity of depth-1 lags predicts K₄ = Σ‖Ŝ‖⁴/(m³q²)
DESCENDS toward (1−2/m)² as q ≫ m³ (the Gaussian value 2 is a small-q
artifact); measure K₄ and K₈ vs q at fixed m.
"""

import cmath, math

def primitive_root(p):
    fac, n, d = [], p - 1, 2
    while d * d <= n:
        if n % d == 0:
            fac.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        fac.append(n)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fac):
            return g
    raise ValueError

def is_prime(n):
    return n >= 2 and all(n % r for r in range(2, int(math.isqrt(n)) + 1))

def data(p, m, k=1):
    g = primitive_root(p)
    ind = [0] * p
    x = 1
    for r in range(p - 1):
        ind[x] = r
        x = (x * g) % p
    zm = [cmath.exp(2j * math.pi * r / m) for r in range(m)]
    # J_j = sum_t lam^j(t) chi(1-t)
    J = [sum(zm[(j * ind[t]) % m] * zm[(k * ind[(1 - t) % p]) % m]
             for t in range(2, p)) for j in range(m)]
    S = [J[j] if j != 0 else 0j for j in range(m)]
    W = [sum(S[j] * S[(c - j) % m] for j in range(m)) for c in range(m)]
    Sh = [sum(zm[(a * j) % m] * S[j] for j in range(m)) for a in range(m)]
    lag1 = [sum(S[(j + t) % m] * S[j].conjugate() for j in range(m))
            for t in range(m)]
    lag2 = [sum(W[(c + t) % m] * W[c].conjugate() for c in range(m))
            for t in range(m)]
    return S, W, Sh, lag1, lag2

def main():
    print(__doc__.splitlines()[1])
    # (L1)/(L2) identities
    print("\n(L1/L2) lag-Parseval identities (machine precision):")
    for m, p in ((9, 19), (12, 37), (15, 31)):
        S, W, Sh, lag1, lag2 = data(p, m)
        l4 = sum(abs(s) ** 4 for s in Sh)
        r4 = m * sum(abs(x) ** 2 for x in lag1)
        l8 = sum(abs(s) ** 8 for s in Sh)
        r8 = m * sum(abs(x) ** 2 for x in lag2)
        ok = abs(l4 - r4) < 1e-6 * l4 and abs(l8 - r8) < 1e-6 * l8
        print(f"  m={m:>2} p={p:>3}: 4th {l4:.4e}={r4:.4e}  8th {l8:.4e}={r8:.4e}"
              f"  {'OK' if ok else 'FAIL'}")

    # q-exponents at fixed m
    for m in (9, 12):
        primes = [p for p in range(m + 1, 40000)
                  if p % m == 1 and is_prime(p)]
        # thin the ladder: geometric-ish selection
        sel, last = [], 0
        for p in primes:
            if p > last * 1.45:
                sel.append(p)
                last = p
        print(f"\nq-scaling at m = {m} ({len(sel)} primes to {sel[-1]}):")
        print(f"{'q':>7} {'sup|lag1|/√q':>12} {'sup|lag2|/q':>12} "
              f"{'sup|lag2|/q^2':>13} {'K4':>7} {'K8':>7}")
        pts1, pts2 = [], []
        for p in sel:
            S, W, Sh, lag1, lag2 = data(p, m)
            s1 = max(abs(lag1[t]) for t in range(1, m))
            s2 = max(abs(lag2[t]) for t in range(1, m))
            K4 = sum(abs(s) ** 4 for s in Sh) / (m ** 3 * p ** 2)
            K8 = sum(abs(s) ** 8 for s in Sh) / (m ** 5 * p ** 4)
            pts1.append((math.log(p), math.log(max(s1, 1e-12))))
            pts2.append((math.log(p), math.log(max(s2, 1e-12))))
            print(f"{p:>7} {s1/math.sqrt(p):>12.2f} {s2/p:>12.2f} "
                  f"{s2/p**2:>13.4f} {K4:>7.3f} {K8:>7.3f}")
        for name, pts in (("lag1", pts1), ("lag2", pts2)):
            n = len(pts)
            mx = sum(x for x, _ in pts) / n
            my = sum(y for _, y in pts) / n
            b = sum((x - mx) * (y - my) for x, y in pts) / sum(
                (x - mx) ** 2 for x, _ in pts)
            print(f"  {name}: measured q-exponent = {b:.3f} "
                  f"(curve-Weil 0.5 / surface-Deligne 1.0 / Gaussian-random 2.0)")
        print(f"  K4 endpoint vs (1-2/m)^2 = {(1-2/m)**2:.3f} "
              f"(Weil-rigidity predicts descent toward it as q >> m^3)")

if __name__ == "__main__":
    main()
