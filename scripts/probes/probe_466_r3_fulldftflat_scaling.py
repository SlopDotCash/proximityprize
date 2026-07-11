#!/usr/bin/env python3
"""
#466 r=3 R305: is FullDFTFlat K = O(1) TRUE?  Scaling probe to m ~ 1000.

Ŝ(a) = m·T_{-a} + 1,  m·T_alpha = sum_e zeta_m^{-e·alpha} J_e — a DFT over
exactly m modes of the m Jacobi angles.  Under Katz (vertical) equidistribution
the normalized angles are iid-uniform-like, each mode ~ complex Gaussian of
variance m·q, modes asymptotically independent, so

    K(m, q, chi) := sup_a ‖Ŝ(a)‖² / (m·q)  ~  max of m Exp(1)  ~  log m + Gumbel,

INDEPENDENT of q (the sup is over m modes, not q/m residues).  Prediction:
K = Theta(log m) — FullDFTFlat with an ABSOLUTE K is expected FALSE.

Consumer tolerance (R302 reduction, C = (K³+9K+18)² = Theta(K⁶) = Theta(B³)
for B = K²): absolute C ⟺ bounded B; B = A·log m ⟹ C ~ 9A³·log³m
(sub-polynomial "quasi-flat" rung); K = m^{1/6} ⟹ C ~ m ⟹ E ≤ m⁴q³ — does
NOT fit the strict m³q³ target.

MEASUREMENTS:
 (S0) validation against the R302 exact probe (m=9, q=19, k=1: K = 1.865);
 (S1) K vs m: m over a near-geometric grid up to ~1000 (multiples of 3),
      several primes q ≡ 1 (m) and several characters k per m; report
      median / max, regress K_med against (a + b·log m) and (c·m^d);
 (S2) argmax structure: is the extremal mode a structured (a = 0 or small)
      or generic?  report the distribution;
 (S3) fixed-m q-scan (m = 60, 120): K vs q over many primes — flat in q?

Computation: T_alpha in O(q) via the index table (no FFT needed);
complex-float precision (sums of q unit terms; q ≤ ~60000 here).
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
    if n < 2:
        return False
    for r in range(2, int(math.isqrt(n)) + 1):
        if n % r == 0:
            return False
    return True

def primes_1mod(m, count, start=0):
    out, p = [], m + 1 + start * m
    while len(out) < count and p < 10 ** 7:
        if p % m == 1 and is_prime(p):
            out.append(p)
        p += m
    return out

def K_sup(p, m, k):
    """sup_a |m T_{-a} + 1|^2/(mq) and argmax, in O(q + m)."""
    g = primitive_root(p)
    # index table
    ind = [0] * p
    x = 1
    for r in range(p - 1):
        ind[x] = r
        x = (x * g) % p
    zm = [cmath.exp(2j * math.pi * r / m) for r in range(m)]
    T = [0j] * m
    for t in range(2, p):
        T[ind[t] % m] += zm[(k * ind[(1 - t) % p]) % m]
    best, arg = -1.0, -1
    for a in range(m):
        v = abs(m * T[a] + 1) ** 2 / (m * p)
        if v > best:
            best, arg = v, a
    return best, arg

def main():
    print(__doc__.splitlines()[1])
    # (S0) validation: R302's 1.865 was the max over the six order-9 characters
    K0 = max(K_sup(19, 9, k)[0] for k in (1, 2, 4, 5, 7, 8))
    print(f"\n(S0) validation m=9 q=19 max over k: K = {K0:.3f} "
          f"(R302 exact probe: 1.865)  {'OK' if abs(K0 - 1.865) < 0.01 else 'FAIL'}")
    if abs(K0 - 1.865) > 0.01:
        sys.exit(1)

    # (S1) scaling in m
    ms = [9, 12, 18, 24, 36, 48, 72, 96, 108, 144, 192, 240, 288, 384,
          480, 576, 720, 960, 1200]
    print("\n(S1) K vs m (5 primes x up to 3 characters per m):")
    print(f"{'m':>5} {'q_min':>7} {'K_med':>7} {'K_max':>7} {'K/log m':>8} "
          f"{'argmax@0?':>9}")
    med_pts = []
    for m in ms:
        qs = primes_1mod(m, 5)
        Ks, args = [], []
        for q in qs:
            ks = [k for k in range(1, m) if math.gcd(k, m) == 1][:3]
            for k in ks:
                K, a = K_sup(q, m, k)
                Ks.append(K)
                args.append(a)
        Ks.sort()
        Kmed, Kmax = Ks[len(Ks) // 2], Ks[-1]
        med_pts.append((m, Kmed))
        frac0 = sum(1 for a in args if a == 0) / len(args)
        print(f"{m:>5} {qs[0]:>7} {Kmed:>7.3f} {Kmax:>7.3f} "
              f"{Kmed / math.log(m):>8.3f} {frac0:>9.2f}")
    # regressions on medians
    import statistics
    xs = [math.log(m) for m, _ in med_pts]
    ys = [K for _, K in med_pts]           # linear-in-log model K = a + b log m
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    b = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
    a = my - b * mx
    res1 = statistics.pstdev([y - (a + b * x) for x, y in zip(xs, ys)])
    lys = [math.log(y) for y in ys]        # power model K = c m^d
    mly = sum(lys) / n
    d = sum((x - mx) * (ly - mly) for x, ly in zip(xs, lys)) / sum((x - mx) ** 2 for x in xs)
    c = math.exp(mly - d * mx)
    res2 = statistics.pstdev([ly - (math.log(c) + d * x) for x, ly in zip(xs, lys)])
    print(f"\n  fit K_med = {a:.3f} + {b:.3f}·log m   (resid sd {res1:.3f})")
    print(f"  fit K_med = {c:.3f}·m^{d:.3f}          (log-resid sd {res2:.3f})")
    print(f"  Gumbel prediction: b ≈ 1 (K ~ log m + O(1));"
          f" power exponent d ≈ (log-slope of log log m) — small d mimics log.")
    print(f"  VERDICT: K grows with m ⇒ FullDFTFlat with ABSOLUTE K is "
          f"{'REFUTED (growth measured)' if ys[-1] > ys[0] + 1.0 else 'not refuted at this range'}")

    # (S3) fixed-m q-scan
    print("\n(S3) fixed m, K vs q (k = 1):")
    for m in (60, 120):
        qs = primes_1mod(m, 12)
        Ks = []
        for q in qs:
            K, _ = K_sup(q, m, 1)
            Ks.append((q, K))
        line = " ".join(f"{q}:{K:.2f}" for q, K in Ks)
        Kv = [K for _, K in Ks]
        print(f"  m={m}: {line}")
        print(f"    -> spread [{min(Kv):.2f}, {max(Kv):.2f}], no q-trend expected "
              f"(sup is over m modes, not q/m)")

if __name__ == "__main__":
    main()
