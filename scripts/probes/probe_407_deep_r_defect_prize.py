#!/usr/bin/env python3
"""
probe_407_deep_r_defect_prize.py  --  #407: deep-r defect in a FIXED prize prime (the real wall).

The moment method gives B <= (p * E_r)^{1/2r}; at r ~ ln p it WOULD give sqrt(n log p) IF E_r ~
E_r^(0) (char-0). The route succeeds iff the defect E_r - E_r^(0) stays o(E_r^(0)) up to r ~ ln p.
The norm bound shows defect(r,p)=0 only for p > L2^{phi/2} (vacuous deep). The lattice-count route
hopes the CUMULATIVE defect from all short alpha in P is still small at deep r.

This probe FIXES a prize prime p ~ n^beta (n<=sqrt(p)) and computes E_r mod p AND E_r^(0) (char-0)
EXACTLY for r = 2..R, tracking:
   ratio(r) = E_r / E_r^(0)        (1.0 = no defect; the route needs this ~1 up to r~ln p)
   and the implied B-bound  (p E_r)^{1/2r}  vs the target C sqrt(n log(p/n)) and vs sqrt(n) (RMS).
We watch WHERE ratio(r) departs from 1 and by how much, in-regime.

To reach deep r exactly we use n=8 (small) and the largest prize prime we can convolve (p up to ~3M).
We also do the char-0 value by exact integer coeff enumeration (the reduced power-basis hash).

Run:  python scripts/probes/probe_407_deep_r_defect_prize.py
"""
import sys, math, itertools
from collections import Counter
import numpy as np

sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, primitive_root
import sympy


def reduction_table(n):
    x = sympy.symbols('x')
    Phi = sympy.Poly(sympy.cyclotomic_poly(n, x), x)
    phi_n = Phi.degree()
    Phi_coeffs = [int(c) for c in Phi.all_coeffs()][::-1]
    redtab = [[0] * phi_n for _ in range(n)]
    for k in range(phi_n): redtab[k][k] = 1
    for k in range(phi_n, n):
        prev = redtab[k - 1]
        shifted = [0] * (phi_n + 1)
        for i in range(phi_n): shifted[i + 1] += prev[i]
        top = shifted[phi_n]
        for i in range(phi_n): shifted[i] -= top * Phi_coeffs[i]
        redtab[k] = shifted[:phi_n]
    return redtab, phi_n


def Er_char0(n, r, redtab, phi_n):
    cnt = Counter()
    for tup in itertools.product(range(n), repeat=r):
        v = [0] * phi_n
        for t in tup:
            rk = redtab[t]
            for i in range(phi_n): v[i] += rk[i]
        cnt[tuple(v)] += 1
    return sum(c * c for c in cnt.values())


def Er_mod_p_fft(p, z, n, r):
    ind = np.zeros(p, dtype=np.float64)
    x = 1
    for _ in range(n):
        ind[x] += 1.0; x = x * z % p
    F = np.fft.rfft(ind)
    conv = np.round(np.fft.irfft(F ** r, n=p))
    return float((conv * conv).sum())


def prize_prime(n, beta, pmax):
    base = int(round(n ** beta)); base -= base % n; base += 1; p = base
    while p < pmax:
        if is_prime(p) and odd_part((p - 1) // n) > 1:
            return p
        p += n
    return None


def main():
    print("=" * 84)
    print(" #407 DEEP-r DEFECT IN A FIXED PRIZE PRIME:  ratio(r)=E_r/E_r^(0) up to r~ln p")
    print("=" * 84)
    n = 8
    redtab, phi_n = reduction_table(n)
    print(f" n={n} (phi={phi_n}=deg). prize: n<=sqrt(p) i.e. beta>=2; di Benedetto regime beta in [4,5].")
    # several prize primes at increasing beta (p must stay <~3.5M to FFT-convolve)
    targets = [(3.5, 2_000_000), (3.8, 2_900_000), (4.0, 3_300_000)]
    for beta, pmax in targets:
        p = prize_prime(n, beta, pmax)
        if p is None:
            print(f"  (no prize prime for beta={beta} under {pmax})"); continue
        g = primitive_root(p); z = pow(g, (p - 1) // n, p)
        lnp = math.log(p)
        ropt = max(2, int(round(lnp)))    # the moment depth the method wants
        target_log = 0.5 * math.log2(n * math.log(p / n))   # log2 of sqrt(n log(p/n))
        print(f"\n  p={p} (2^{math.log2(p):.2f}, beta=log_n p={math.log(p)/math.log(n):.2f}); "
              f"r_opt~ln p={ropt}; target sqrt(n log(p/n))=2^{target_log:.2f}; sqrt(n)=2^{0.5*math.log2(n):.2f}")
        print(f"   {'r':>3} {'E_r mod p':>16} {'E_r^(0)':>16} {'ratio':>8} "
              f"{'(pE_r)^(1/2r)':>14} {'log2':>7} {'vs target':>10}")
        for r in range(2, min(ropt + 3, 11)):
            Er = Er_mod_p_fft(p, z, n, r)
            E0 = Er_char0(n, r, redtab, phi_n) if n ** r <= 17_000_000 else None
            ratio = (Er / E0) if E0 else float('nan')
            Bbound = (p * Er) ** (1.0 / (2 * r))
            note = ""
            if r == ropt: note = "<-- r_opt"
            print(f"   {r:>3} {Er:>16.0f} {str(int(E0)) if E0 else '   (too big)':>16} "
                  f"{ratio:>8.4f} {Bbound:>14.1f} {math.log2(Bbound):>7.2f} "
                  f"{math.log2(Bbound)-target_log:>+10.2f} {note}")
    print("\nKEY READING:")
    print(" - ratio(r) ~ 1.000 up to r_opt  => char-0 holds deep, moment method DELIVERS sqrt(n log).")
    print(" - ratio(r) inflates before r_opt => p-defect bites; (pE_r)^(1/2r) overshoots target by")
    print("   the inflation; THAT gap (in log2) is exactly what the short-vector count must kill.")
    print(" - Compare (pE_r)^(1/2r) at r_opt to target: if it sits AT target, the law holds and only")
    print("   a PROOF that ratio~1 is missing; if it sits ABOVE, the defect genuinely inflates B.")


if __name__ == "__main__":
    main()
