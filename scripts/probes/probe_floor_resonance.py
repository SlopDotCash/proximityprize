#!/usr/bin/env python3
r"""
probe_floor_resonance.py  (#444 — floor-lower-bound attack)

GOAL.  The δ* "wall" route needs a TWO-SIDED barrier:  the worst Gauss period
    M(n) = max_{b != 0} |η_b|,   η_b = Σ_{x in μ_n} e_p(b x),   μ_n ⊂ F_p* order n,
should satisfy   M(n) >= c * sqrt(n log m),   m = (p-1)/n.
The matching UPPER bound C*sqrt(n log m) is measured + has a conditional Chernoff proof
(SalemZygmandChaining).  The Parseval/4th-moment LOWER bound (WorstPeriodLowerBound) only gives
M(n) >= sqrt(n) — it is MISSING the extra sqrt(log m) factor.

This probe tests the RESONANCE METHOD (Soundararajan; Bondarenko–Seip arXiv:1505.07840):
construct a structured resonator b* and ask whether |η_{b*}| / sqrt(n log m) -> c > 0.

KEY STRUCTURAL REDUCTION (Gauss-period coset law).  η_b depends on b only through the coset
b·μ_n in F_p* / μ_n, of which there are exactly m = (p-1)/n (plus b=0).  So
    M(n) = max over the m Gauss periods η_{g^j}, j=0..m-1   (g a generator of F_p*).
This is a list of m complex numbers each of average size sqrt(n) (Parseval: mean |η|^2 = n).
The question "is M >= c sqrt(n log m)" is EXACTLY "is the max of these m periods as large as a
max of m independent Gaussians of variance n" — i.e. is there NO destructive correlation that
suppresses the max below the sub-Gaussian extreme-value scale.

RESONATOR.  We test two resonance strategies:
  (R1) DIRECT max over all m cosets (ground truth M(n)).
  (R2) Bondarenko–Seip style multiplicative resonator: a frequency b supported (after the coset
       reduction) so that many η_{b r} for r in a GCD-structured set R align in phase.  We use the
       discrete analogue: pick the coset rep that maximizes the smoothed sum
       Σ_{r in R} Re( conj(phase) η_{b r} ) for R = a geometric progression in F_p* / μ_n.

We report:
  M/sqrt(n)            -- the Parseval-floor-normalized max (should grow ~ sqrt(log m))
  M/sqrt(n log m)      -- the resonance-floor-normalized max (should -> constant c>0)
  R2 hit ratio         -- |η_{resonator}| / M  (does the explicit construction find the max?)
and we SWEEP m at FIXED n to isolate the log m growth (the whole content of the lower bound).
"""
import math
import numpy as np
import sympy


def subgroup_indicator(p, n, g):
    """Return (mu list, generator h of mu_n) for the order-n subgroup."""
    h = pow(g, (p - 1) // n, p)
    mu = []
    x = 1
    for _ in range(n):
        mu.append(x)
        x = x * h % p
    assert len(set(mu)) == n, "mu_n not order n"
    return mu


def all_periods(p, n, mu):
    """Return |η_b|^2 for every b in 0..p-1 via one length-p FFT of the indicator."""
    f = np.zeros(p)
    for x in mu:
        f[x] = 1.0
    S = np.fft.fft(f)
    a2 = np.abs(S) ** 2
    a2[0] = 0.0  # drop the trivial frequency b=0 (η_0 = n)
    return S, a2


def resonator_hit(p, n, g, S):
    """
    Bondarenko–Seip-style multiplicative resonator (discrete analogue).
    The coset reduction: η_b depends only on coset of b in F_p*/μ_n.  Index cosets by j in
    0..m-1 via b = g^j.  Build a resonator as a short geometric progression of cosets
    R = {g^{j0 + i*step} : i=0..L-1} and choose the global phase / base coset that maximizes
    the *coherent* sum.  Return the best single-period magnitude obtained this way (a LOWER bound
    achieved by an explicit, structured choice) and the resonator length used.
    """
    m = (p - 1) // n
    # eta over cosets: period_j = S[g^j].  (S already complex.)
    gpow = np.empty(m, dtype=np.int64)
    x = 1
    for j in range(m):
        gpow[j] = x
        x = x * g % p
    periods = S[gpow]                 # complex η for each coset rep g^j
    mags = np.abs(periods)
    # R2: try short multiplicative progressions R (steps that are units mod m) and, for each base
    # coset b, sum the *aligned* contributions.  The resonator's job is to make many periods large
    # AND in-phase.  Discrete surrogate: for each candidate "frequency" we coherently add periods
    # whose phases we rotate into alignment using the resonator weights, then read the resulting
    # max single period.  Since the operative quantity is M = max single |η|, the honest resonance
    # surrogate is: how large is the largest period we can CERTIFY via a structured search that does
    # not look at all m of them?  We approximate by scanning multiplicative progressions of a fixed
    # short length L = ceil(log2 m) and reporting the max period magnitude found on those.
    L = max(2, math.ceil(math.log2(max(m, 2))))
    best = 0.0
    # steps coprime to m give progressions that are "spread" (resonance-structured)
    steps = [s for s in range(1, min(m, 64)) if math.gcd(s, m) == 1]
    if not steps:
        steps = [1]
    for step in steps[:16]:
        for j0 in range(0, m, max(1, m // 64)):
            idx = [(j0 + i * step) % m for i in range(L)]
            local = mags[idx].max()
            if local > best:
                best = local
    return float(best), L, float(mags.max())


def main():
    print("=== Floor resonance: is M(n) >= c*sqrt(n log m)? (#444) ===\n")
    print("Strategy: SWEEP m at FIXED n to isolate the sqrt(log m) growth of the max period.")
    print("If M/sqrt(n) grows like sqrt(log m) (i.e. M/sqrt(n log m) -> const), the wall floor")
    print("is real.  If M/sqrt(n) plateaus (M/sqrt(n log m) -> 0), the log m factor is ABSENT")
    print("and the max is only Parseval-size sqrt(n) -- the lower bound would FAIL.\n")

    # n fixed, m growing: pick primes p = 1 mod n with increasing m=(p-1)/n.
    configs = {
        16:  [97, 193, 257, 1153, 4129, 12289, 40961, 163841, 786433],
        32:  [97, 193, 257, 1217, 4129, 12289, 65537, 274177, 1179649],
        64:  [193, 257, 449, 1601, 8129, 65537, 786433, 5767169],
        128: [257, 769, 3329, 12289, 65537, 786433, 7340033],
        256: [257, 7681, 65537, 786433, 5767169, 13631489],
    }
    for n, plist in configs.items():
        print(f"--- n = {n} ---")
        print(f"{'p':>11} {'m=(p-1)/n':>11} {'M':>9} {'M/sqrt(n)':>10} "
              f"{'sqrt(logm)':>10} {'M/sqrt(nlogm)':>13} {'resR2/M':>8}")
        rows = []
        for p in plist:
            if not sympy.isprime(p) or (p - 1) % n != 0:
                # snap to nearest valid prime >= p with n | p-1
                q = p + (n - (p - 1) % n) % n
                while not (sympy.isprime(q) and (q - 1) % n == 0):
                    q += n
                p = q
            g = int(sympy.primitive_root(p))
            mu = subgroup_indicator(p, n, g)
            S, a2 = all_periods(p, n, mu)
            M = math.sqrt(float(a2.max()))
            m = (p - 1) // n
            if m < 2:
                continue
            sln = math.sqrt(math.log(m))
            res_best, L, true_max = resonator_hit(p, n, g, S)
            c = M / (math.sqrt(n) * sln)
            rows.append((math.log(m), M / math.sqrt(n)))
            print(f"{p:>11} {m:>11} {M:>9.3f} {M/math.sqrt(n):>10.4f} "
                  f"{sln:>10.4f} {c:>13.4f} {res_best/M:>8.4f}")
        # linear fit of M/sqrt(n) against sqrt(log m): slope = the resonance constant c.
        if len(rows) >= 3:
            xs = np.array([math.sqrt(lm) for (lm, _) in rows])
            ys = np.array([y for (_, y) in rows])
            A = np.vstack([xs, np.ones_like(xs)]).T
            slope, intercept = np.linalg.lstsq(A, ys, rcond=None)[0]
            # also fit M^2/n vs log m  (variance-extreme-value form: M^2 ~ 2 n log m => slope 2)
            xs2 = np.array([lm for (lm, _) in rows])
            ys2 = ys ** 2
            A2 = np.vstack([xs2, np.ones_like(xs2)]).T
            slope2, intercept2 = np.linalg.lstsq(A2, ys2, rcond=None)[0]
            print(f"   FIT  (M/sqrt n) ~ {slope:.4f}*sqrt(log m) + {intercept:.4f}"
                  f"   |   M^2/n ~ {slope2:.4f}*log m + {intercept2:.4f}")
            print(f"   => resonance constant c ~ {slope:.4f}  (extreme-value model predicts "
                  f"M^2/n ~ 2 log m, slope2~2)\n")
        else:
            print()


if __name__ == "__main__":
    main()
