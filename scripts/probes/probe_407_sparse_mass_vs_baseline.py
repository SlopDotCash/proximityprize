#!/usr/bin/env python3
"""
probe_407_sparse_mass_vs_baseline.py -- does the bounded-house sparse SVP-min orbit FLOOD the
energy, or stay o(E_r^(0))?  This decides whether the sparse-support angle yields a partial
sub-baseline bound or just RE-CONFIRMS the wall (and possibly strengthens it).

ESTABLISHED:
  - sparse-support SVP-min = lattice SVP-min of 𝔭 (sparsity does NOT lengthen the shortest vector);
  - its house h_lat is ~BOUNDED in n (4.5-5.7 at n=64,128), NOT growing like √n;
  - the defect set at onset = ONE automorphism orbit (Z/n × Galois) of this SVP-min, norm ~p.

CONSEQUENCE TO TEST: the defect mass at onset depth r0 = (orbit size)·(representations per orbit pt).
  orbit size ~ n·φ(n)/(symmetry) ; reps per pt R_{r0}(z) for a fixed sparse z.  Compare to
  E_{r0}^(0) = (2r0-1)!!·n^{r0} (the char-0 Gaussian baseline).

We measure exactly (small n), for the onset r0 and r0+1:
   mass = E_r - E_r^(0)   (the defect),
   E_r^(0)                (baseline),
   ratio mass/E_r^(0)     (the prize wants this -> 0; if it FLOODS -> 1, the wall is HARD here),
   B_emp = max_b|eta_b| and B/sqrt(n ln(p/n))  (the actual prize constant at this instance).

Cross-check: this is the SAME defect the energy/cumulant route sees; the value of this probe is to
state PRECISELY, in the sparse-support / SVP language, what the onset-orbit contributes.
"""
import sys, math, itertools
import numpy as np

sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, primitive_root


def prize_prime(n, beta, pmax=10**9):
    base = int(round(n ** beta)); base -= base % n; base += 1; p = base
    while p < pmax:
        if is_prime(p) and odd_part((p - 1) // n) > 1:
            return p
        p += n
    return None


def order_n_root(p, n):
    return pow(primitive_root(p), (p - 1) // n, p)


def Er_mod_p(p, z, n, r):
    ind = np.zeros(p)
    x = 1
    for _ in range(n):
        ind[x] += 1.0; x = x*z % p
    F = np.fft.rfft(ind)
    conv = np.fft.irfft(F**r, n=p)
    return float((np.round(conv)**2).sum())


def Er_char0_bessel(n, r):
    a = [1.0/math.factorial(k)**2 for k in range(r+1)]
    def pm(u,v):
        w=[0.0]*(r+1)
        for i in range(r+1):
            if u[i]==0: continue
            for j in range(r+1-i): w[i+j]+=u[i]*v[j]
        return w
    res=[0.0]*(r+1); res[0]=1.0; base=a[:]; e=n
    while e>0:
        if e&1: res=pm(res,base)
        e>>=1
        if e>0: base=pm(base,base)
    return math.factorial(2*r)*res[r]


def B_emp(p, z, n):
    ind = np.zeros(p)
    x=1
    for _ in range(n): ind[x]+=1.0; x=x*z%p
    F=np.fft.fft(ind)
    # eta_b = sum_{x in mu_n} e_p(b x) = conj? actually F[b] = sum_x e^{-2pi i b x/p}; |.| same
    mags=np.abs(F)
    mags[0]=0  # b=0 is trivial n
    return float(mags.max())


def main():
    print("="*100)
    print(" #407 SPARSE SVP-MIN ORBIT MASS vs BASELINE: does the onset orbit FLOOD or stay o(E^0)?")
    print("="*100)
    print(f"{'n':>4} {'beta':>5} {'p':>10} | {'r':>2} {'E_r mod p':>13} {'E_r^(0)':>13} "
          f"{'defect':>12} {'def/E0':>8} | {'B_emp':>8} {'B/√(nL)':>8}")
    for n in (8, 16, 32):
        for beta in (4.0, 5.0):
            p = prize_prime(n, beta)
            if p is None or p > 4_000_000:
                # still compute B if small enough
                if p is None: continue
            z = order_n_root(p, n)
            L = math.log(p/n)
            Bv = B_emp(p, z, n) if p <= 4_000_000 else float('nan')
            bn = Bv/math.sqrt(n*L) if not math.isnan(Bv) else float('nan')
            for r in range(2, 6):
                if p > 4_000_000:
                    print(f"{n:>4} {beta:>5.1f} {p:>10} | {r:>2}   (p too large to convolve)")
                    continue
                Er = Er_mod_p(p, z, n, r)
                E0 = Er_char0_bessel(n, r)
                defect = Er - E0
                print(f"{n:>4} {beta:>5.1f} {p:>10} | {r:>2} {Er:>13.0f} {E0:>13.0f} "
                      f"{defect:>12.0f} {defect/E0:>8.4f} | {Bv:>8.1f} {bn:>8.3f}")
            print()
    print("READING:")
    print(" - def/E0 = fraction by which the energy exceeds the char-0 Gaussian baseline. At the onset")
    print("   depth this is the contribution of the sparse SVP-min automorphism orbit. If def/E0 stays")
    print("   small at the onset r but the bounded house means the onset r is O(1) for ALL n, the prize")
    print("   regime (r up to log p >> O(1)) is in the FLOODED zone -> sparse-support REconfirms the wall.")
    print(" - B/√(nL): the prize constant. Stable ~1.1-1.5 = the proven measured law; the sparse-support")
    print("   analysis does not lower it.")


if __name__ == "__main__":
    main()
