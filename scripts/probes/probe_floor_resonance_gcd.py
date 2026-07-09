#!/usr/bin/env python3
r"""
probe_floor_resonance_gcd.py  (#444 — can a GCD/multiplicative resonator beat the moment ladder?)

The moment resonator R_j = |η_j|^{2(k-1)} reaches the n log m scale only at depth k ~ log m (= the
wall).  The Bondarenko-Seip innovation for ζ(1/2+it) is a resonator R that is NOT a power of the
object itself but a GCD-structured sum, which achieves the extreme scale at BOUNDED 'cost'
(|supp R| sub-polynomial).  Does an analogous multiplicative resonator over the coset group
F_p*/μ_n ≅ Z/m beat the moment ladder for the Gauss periods?

The Gauss period as a function of the coset index j (b = g^j) is
    η(j) = Σ_{x in μ_n} e_p(g^j x).
Crucially η(j) is itself (up to normalization) a value of a Gauss SUM / Kloosterman-like object;
the m periods are the eigenvalues of the generalized Paley graph Cay(F_p*, μ_n).  A resonator that
exploits MULTIPLICATIVE structure of j (Bondarenko-Seip: support on {j : j has many divisors in a
set}) would prove a large max if the periods CORRELATE multiplicatively.

We test:  build the resonator R_j = | Σ_{d | (j-shift), d in D} w_d |^2 style supports, and the
Soundararajan resonator R supported on a multiplicative set, and compare the certified ratio
(Σ R_j a2_j)/(Σ R_j) against the moment resonator of the SAME effective support size.

If the GCD resonator does NOT beat the moment ladder (i.e. to reach c n log m it still needs
support ~ m^{Ω(1)} or depth ~ log m), then resonance gives NO shortcut and the floor lower bound
is genuinely the moment/energy wall.  If it DOES beat it, that is a real new lower-bound route.
"""
import math
import numpy as np
import sympy


def period_data(p, n):
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
    m = (p - 1) // n
    gpow = np.empty(m, dtype=np.int64)
    xx = g
    for j in range(m):
        gpow[j] = xx
        xx = xx * g % p
    a2 = (np.abs(S) ** 2)[gpow]
    return a2, m


def certified_ratio(a2, R):
    R = np.asarray(R, dtype=float)
    s = R.sum()
    if s <= 0:
        return 0.0
    return float((R * a2).sum() / s)


def main():
    print("=== GCD/multiplicative resonator vs moment ladder (#444) ===\n")
    print("All ratios are TRUE lower bounds on max|η|^2, reported as multiples of n.")
    print("Question: does a STRUCTURED resonator reach ~log m * n at LOWER cost than the")
    print("moment resonator (depth k~log m)?\n")

    cases = [(16, 786433), (32, 1179649), (64, 5767169), (128, 7340033)]
    for n, p in cases:
        a2, m = period_data(p, n)
        logm = math.log(m)
        maxR = a2.max() / n
        print(f"--- n={n} p={p} m={m} logm={logm:.2f} max|η|^2/n={maxR:.3f} ---")

        # baseline moment resonator at depth ~ log m
        kln = max(2, round(logm))
        R_mom = a2 ** (kln - 1)
        ratio_mom = certified_ratio(a2, R_mom) / n

        # (G1) multiplicative-support resonator: support on cosets j that are k-th-power-rich,
        # i.e. j in a multiplicative subgroup / smooth-index set of Z/m.  Use divisor-count weight.
        # Bondarenko-Seip use R(j) ~ supported where j is "multiplicatively structured".
        # Discrete surrogate: weight by number of small prime factors of j (more structure => bigger).
        Rg = np.ones(m)
        for j in range(1, m):
            jj = j
            cnt = 0
            for pr in (2, 3, 5, 7, 11, 13):
                while jj % pr == 0:
                    jj //= pr
                    cnt += 1
            Rg[j] = (cnt + 1) ** 2
        ratio_gcd = certified_ratio(a2, Rg) / n

        # (G2) geometric-progression coherence resonator: choose the base coset and step that
        # maximize the *coherent* alignment.  Use the complex periods.
        # (already covered by the moment one being max; here we test a CHEAP rank-1 resonator:
        #  R = indicator of the top-T cosets by a PROXY = the k=2 moment resonator.  Two-stage.)
        # Stage 1: rank cosets by a2 (the k=2 self-weight is monotone in a2).  Take top sqrt(m).
        T = max(1, int(math.sqrt(m)))
        order = np.argsort(-a2)
        Rtop = np.zeros(m)
        Rtop[order[:T]] = 1.0
        ratio_top = certified_ratio(a2, Rtop) / n

        # (G3) RANDOM resonator of the same support size as moment (control)
        rng = np.random.default_rng(0)
        Rrand = np.zeros(m)
        Rrand[rng.choice(m, size=T, replace=False)] = 1.0
        ratio_rand = certified_ratio(a2, Rrand) / n

        print(f"   moment(k={kln})      : {ratio_mom:7.3f} n   (depth ~ log m, the wall route)")
        print(f"   multiplicative-GCD   : {ratio_gcd:7.3f} n   (struct support, NO peeking at a2)")
        print(f"   top-sqrt(m) (peek)   : {ratio_top:7.3f} n   (cheats: uses a2 to rank)")
        print(f"   random sqrt(m)       : {ratio_rand:7.3f} n   (control)")
        print(f"   target c*log m       : ~{logm:7.3f} n   (n log m scale)\n")

    print("READ:")
    print(" - If multiplicative-GCD ratio stays ~1*n (= flat/Parseval) while only the moment(k~logm)")
    print("   or the a2-peeking top-set reaches ~log m * n, then the GCD/multiplicative structure of")
    print("   the COSET INDEX carries NO resonance: the periods do not align multiplicatively in j.")
    print("   The ONLY provable route to n log m is the moment ladder at depth ~log m = the wall.")
    print(" - Bondarenko-Seip resonance works because ζ's Dirichlet coefficients ARE multiplicative;")
    print("   the Gauss periods η(j) over the coset index are NOT multiplicative in j (they are a")
    print("   single additive character sum), so the GCD resonator has nothing to grab.")


if __name__ == "__main__":
    main()
