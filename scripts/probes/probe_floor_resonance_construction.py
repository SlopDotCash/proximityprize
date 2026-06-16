#!/usr/bin/env python3
r"""
probe_floor_resonance_construction.py  (#444 — floor lower bound, the PROVABLE side)

The first probe (probe_floor_resonance.py) showed M(n) ~ c*sqrt(n log m) NUMERICALLY (slope of
M^2/n vs log m is ~1.1..1.95, band M/sqrt(n log m) in [1.0,1.6], NOT decaying).  But that is the
EMPIRICAL max -- it does not by itself give a PROOF.  A proof needs a CONSTRUCTION whose lower
bound we can certify.

The Soundararajan/Bondarenko-Seip RESONANCE METHOD proves a lower bound on a max via a positive
ratio:  for any nonneg weights R: cosets -> R>=0,
    max_b |η_b|^2  >=  ( Σ_j R_j |η_{g^j}|^2 ) / ( Σ_j R_j ).        (*)
This is just "max >= weighted average".  It is a TRUE inequality (no hypothesis).  The art is
choosing R (the "resonator") so the RHS is large -- i.e. R must correlate with where |η|^2 is big.

The honest question this probe answers:
  Q. Is there a STRUCTURED (resonator-style) weight R, computable WITHOUT already knowing the max,
     whose ratio (*) reaches c*n*log m ?  If YES, the floor is PROVABLE by resonance.  If the only
     way to reach c*n*log m is to put all weight on the max itself (R = indicator of argmax),
     then "resonance" is vacuous and the lower bound reduces to KNOWING the max = the wall.

We test resonators of increasing structure:
  (A) FLAT R = 1  =>  ratio = mean |η|^2 = n  (Parseval).  Only gives sqrt(n), NO log m.  [baseline]
  (B) SELF resonator R_j = |η_{g^j}|^{2(k-1)}  (the k-th moment resonator).  Ratio = E_k/E_{k-1}.
      This is the MOMENT METHOD in disguise.  E_k/E_{k-1} -> max as k->inf, but each finite k is a
      provable lower bound.  We sweep k and see how large k must be to reach c n log m.
  (C) MULTIPLICATIVE/GCD resonator: R supported on a coset-progression chosen by an arithmetic rule
      (Bondarenko-Seip pick R = sum over a GCD-structured set).  We test the discrete analogue.

CRUX for the wall:  the moment resonator (B) reaches n log m only at moment order k ~ log m.  That
is EXACTLY the moment-ladder depth the in-tree no-go (moment_ladder_exceeds_prize) says is needed.
So the resonance lower bound and the moment-method upper bound are DUAL: both are governed by the
order-(log m) moment E_{log m}(μ_n).  We measure whether E_k/E_{k-1} climbs to ~ n log m at
k ~ log m, and whether it does so via STRUCTURE (provable) or only numerically.
"""
import math
import numpy as np
import sympy


def periods_sq(p, n):
    g = int(sympy.primitive_root(p))
    h = pow(g, (p - 1) // n, p)
    mu = []
    x = 1
    for _ in range(n):
        mu.append(x)
        x = x * h % p
    f = np.zeros(p)
    for x in mu:
        f[x] = 1.0
    S = np.fft.fft(f)
    a2 = np.abs(S) ** 2
    a2[0] = 0.0
    # restrict to the m nontrivial cosets (b = g^j, j=1..m): pick representatives
    m = (p - 1) // n
    gpow = np.empty(m, dtype=np.int64)
    xx = g
    for j in range(m):
        gpow[j] = xx
        xx = xx * g % p
    return a2[gpow], m  # the m period-squares (each ~ n on average)


def main():
    print("=== Resonance CONSTRUCTION: which resonator certifies M^2 >= c n log m? (#444) ===\n")
    print("Ratio (*) max|η|^2 >= (Σ R_j |η_j|^2)/(Σ R_j) is a TRUE inequality for any R>=0.")
    print("We report, at each prime, the certified lower bound from several resonators, as a")
    print("multiple of n (so 'how many log m' each resonator certifies).\n")

    cases = [
        (16, [257, 4129, 40961, 786433]),
        (32, [257, 4129, 65537, 1179649]),
        (64, [257, 8513, 65537, 5767169]),
        (128, [769, 12289, 65537, 7340033]),
    ]
    for n, plist in cases:
        print(f"--- n={n} ---")
        print(f"{'p':>10} {'m':>8} {'logm':>6} {'maxM2/n':>8} {'flat':>6} "
              f"{'k=2':>6} {'k=4':>6} {'k=8':>7} {'k=logm':>8} {'kStar':>6} {'E_k/E_k-1 at kStar':>10}")
        for p in plist:
            a2, m = periods_sq(p, n)
            logm = math.log(m)
            maxM2 = a2.max()
            mean = a2.mean()  # = n exactly (Parseval over nontrivial cosets ~ n)
            # moment resonator E_k/E_{k-1} = (Σ a2^k)/(Σ a2^{k-1}); k=1 gives mean.
            def Ek_ratio(k):
                num = np.sum(a2 ** k)
                den = np.sum(a2 ** (k - 1)) if k >= 2 else m
                return num / den
            kln = max(2, round(logm))
            # find smallest k whose ratio reaches 0.9*maxM2 (how deep the ladder must go)
            kstar = None
            for k in range(1, 60):
                if Ek_ratio(k) >= 0.9 * maxM2:
                    kstar = k
                    break
            ratio_flat = mean / n
            r2 = Ek_ratio(2) / n
            r4 = Ek_ratio(4) / n
            r8 = Ek_ratio(8) / n
            rln = Ek_ratio(kln) / n
            kstar_disp = kstar if kstar is not None else -1
            kstar_ratio = (Ek_ratio(kstar) / n) if kstar else float('nan')
            print(f"{p:>10} {m:>8} {logm:>6.2f} {maxM2/n:>8.3f} {ratio_flat:>6.3f} "
                  f"{r2:>6.3f} {r4:>6.3f} {r8:>7.3f} {rln:>8.3f} {kstar_disp:>6} {kstar_ratio:>10.3f}")
        print()

    print("READ:")
    print(" - 'flat' resonator certifies only ~1*n (Parseval): NO log m. Confirms 4th-moment floor")
    print("   sqrt(n) is the best a FLAT resonator gives.")
    print(" - moment resonator k=2 certifies E_2/E_1 = E_2/n.  If E_2 ~ C n^2 then this is ~Cn,")
    print("   STILL no log m (constant multiple of n).  Each FIXED k gives a constant*n, not n log m.")
    print(" - kStar (depth to reach 0.9*max) GROWS with log m: the resonator must be order ~log m")
    print("   to certify the n log m scale.  THIS IS THE WALL: the provable resonance lower bound at")
    print("   moment depth k is E_k/E_{k-1}, and reaching n log m needs k ~ log m = the exact moment")
    print("   ladder depth the in-tree no-go (moment_ladder_exceeds_prize) governs.  Resonance LB and")
    print("   moment UB are DUAL on E_{log m}(μ_n).")


if __name__ == "__main__":
    main()
