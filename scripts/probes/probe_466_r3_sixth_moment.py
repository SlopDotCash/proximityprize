#!/usr/bin/env python3
"""
#466 r=3 R306: the sixth moment — direct measurement vs the Hölder-composed
bound, and the circularity record.

CIRCULARITY (exact, formalized in Lean): Σ_a‖Ŝ(a)‖⁶ = m·Σ_c‖(S⋆S⋆S)(c)‖² —
the 6th moment of the DFT IS the full triple-convolution energy, i.e. the r=3
core itself (R23 TripleConvEnergyBound object).  A direct "SixthMomentBound"
is therefore NOT an input; the honest move is the two-input decomposition

  Σ_a‖Ŝ‖⁶ ≤ (sup_a‖Ŝ‖²)·(Σ_a‖Ŝ‖⁴) ≤ (B·mq)·(K₄·m³q²) = B·K₄·m⁴q³,

with B the (Gumbel, ~0.8·log m) flatness budget and K₄ the (O(1)) fourth
moment: a QUARTIC input + a log-flat input give the SEXTIC core within a
log-only loss.

MEASUREMENTS (m up to 1200, several primes x characters each):
 (M1) K₆ := Σ_a‖Ŝ‖⁶/(m⁴q³) directly — prediction under equidistribution:
      the average is Gumbel-IMMUNE: modes ~ complex Gaussian variance
      s²·q (s² = Σ_{j≠0}|J_j|²/(mq)·m ≈ m−2), E|G|⁶ = 6·(var)³ ⇒
      K₆ ≈ 6·((m−2)/m)³ → 6.  If K₆ is O(1)-flat, the r=3 core truth is
      C ≈ 3·K₆ + o(1) — ABSOLUTE — and only the INPUTS carry the log.
 (M2) waste of the Hölder chain: (B_meas·K₄_meas)/K₆ — how much the
      sup·quartic composition overpays (expected ~ log m /(K₆/K₄-ish)).
 (M3) the identity check Σ_a‖Ŝ‖⁶ = m·Σ_c‖(S⋆S⋆S)(c)‖² at small m (exact
      convolution, machine precision) — the circularity record.
"""

import cmath, math, sys

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

def primes_1mod(m, count):
    out, p = [], m + 1
    while len(out) < count and p < 10 ** 7:
        if p % m == 1 and is_prime(p):
            out.append(p)
        p += m
    return out

def moments(p, m, k):
    """returns (B_sup, K4, K6) from Shat(a) = m*T_a + 1 over the m modes."""
    g = primitive_root(p)
    ind = [0] * p
    x = 1
    for r in range(p - 1):
        ind[x] = r
        x = (x * g) % p
    zm = [cmath.exp(2j * math.pi * r / m) for r in range(m)]
    T = [0j] * m
    for t in range(2, p):
        T[ind[t] % m] += zm[(k * ind[(1 - t) % p]) % m]
    xs = [abs(m * T[a] + 1) ** 2 for a in range(m)]
    B = max(xs) / (m * p)
    K4 = sum(v ** 2 for v in xs) / (m ** 3 * p ** 2)
    K6 = sum(v ** 3 for v in xs) / (m ** 4 * p ** 3)
    return B, K4, K6

def identity_check(p, m, k):
    """(M3): sixth moment = m * triple-conv energy of Sfun (zero-removed)."""
    g = primitive_root(p)
    ind = [0] * p
    x = 1
    for r in range(p - 1):
        ind[x] = r
        x = (x * g) % p
    zm = [cmath.exp(2j * math.pi * r / m) for r in range(m)]
    J = [sum(zm[(j * ind[t]) % m] * zm[(k * ind[(1 - t) % p]) % m]
             for t in range(2, p)) for j in range(m)]
    S = [J[j] if j != 0 else 0j for j in range(m)]
    Sh = [sum(zm[(a * j) % m] * S[j] for j in range(m)) for a in range(m)]
    lhs = sum(abs(s) ** 6 for s in Sh)
    W3 = [sum(S[j1] * S[j2] * S[(c - j1 - j2) % m]
              for j1 in range(m) for j2 in range(m)) for c in range(m)]
    rhs = m * sum(abs(w) ** 2 for w in W3)
    return lhs, rhs

def main():
    print(__doc__.splitlines()[1])
    # (M3) circularity identity
    print("\n(M3) identity Σ‖Ŝ‖⁶ = m·Σ‖S⋆S⋆S‖² (exact, small cases):")
    for m, p in ((9, 19), (12, 37), (15, 31)):
        lhs, rhs = identity_check(p, m, 1)
        ok = abs(lhs - rhs) < 1e-6 * max(1.0, lhs)
        print(f"  m={m:>2} p={p:>3}: lhs = {lhs:.4e}  rhs = {rhs:.4e}  "
              f"{'OK' if ok else 'FAIL'}")
        if not ok:
            sys.exit(1)

    # (M1)/(M2) scaling
    ms = [9, 12, 18, 24, 36, 48, 72, 96, 144, 192, 288, 384, 480, 720, 960, 1200]
    print("\n(M1/M2) K6 direct vs composed B*K4 (5 primes x 3 chars per m):")
    print(f"{'m':>5} {'K6_med':>7} {'K6_max':>7} {'pred 6((m-2)/m)^3':>17} "
          f"{'B_med':>6} {'K4_med':>7} {'waste B*K4/K6':>13}")
    for m in ms:
        qs = primes_1mod(m, 5)
        Bs, K4s, K6s = [], [], []
        for q in qs:
            ks = [k for k in range(1, m) if math.gcd(k, m) == 1][:3]
            for k in ks:
                B, K4, K6 = moments(q, m, k)
                Bs.append(B); K4s.append(K4); K6s.append(K6)
        Bs.sort(); K4s.sort(); K6s.sort()
        n2 = len(K6s) // 2
        pred = 6 * ((m - 2) / m) ** 3
        waste = (Bs[n2] * K4s[n2]) / K6s[n2]
        print(f"{m:>5} {K6s[n2]:>7.3f} {K6s[-1]:>7.3f} {pred:>17.3f} "
              f"{Bs[n2]:>6.2f} {K4s[n2]:>7.3f} {waste:>13.2f}")
    print("\n  verdict: if K6_med is flat-in-m near the Gaussian value ~6, the r=3")
    print("  core truth has an ABSOLUTE constant (the Gumbel log lives only in the")
    print("  sup); the Hölder-composed route pays exactly that log as 'waste'.")

if __name__ == "__main__":
    main()
