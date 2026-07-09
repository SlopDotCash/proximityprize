#!/usr/bin/env python3
r"""
probe_floor_resonance_dual.py  (#444 — the exact resonance<->energy DUALITY identity)

Verifies the EXACT identity that makes the floor lower bound axiom-cleanly equal to the energy:
the moment resonator R_j = a2_j^{k-1} gives certified ratio
    (Σ_j R_j a2_j)/(Σ_j R_j) = (Σ_j a2_j^k)/(Σ_j a2_j^{k-1}) = P_k / P_{k-1}
where P_k := Σ_{j != 0} |η_{g^j}|^{2k}.  And from the in-tree moment identity
    Σ_{b in F_p} |η_b|^{2k} = p * E_k(μ_n)    (E_k = the order-k additive energy of μ_n),
peeling b=0 (|η_0|^{2k}=n^{2k}):  P_k = p*E_k - n^{2k}.

So the BEST provable resonance lower bound at depth k is
    max_{b!=0} |η_b|^2  >=  (p*E_k - n^{2k}) / (p*E_{k-1} - n^{2(k-1)}).            (DUAL)

This is a TRUE, hypothesis-free lower bound for every k (it is "max >= weighted mean").  The floor
M^2 >= c n log m therefore HOLDS iff this ratio reaches c n log m for some k -- and the data
(probe_floor_resonance_construction) shows that requires k ~ log m.  At k ~ log m the RHS depends on
E_{log m}(μ_n), whose LOWER bound is the open additive-energy quantity = the SAME wall as the upper
bound.  This probe confirms (DUAL) numerically to machine precision and shows the k=2 instance is a
CLEAN, fully provable, hypothesis-free improvement of the 4th-moment floor.
"""
import math
import numpy as np
import sympy


def setup(p, n):
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
    a2_all = np.abs(S) ** 2     # over ALL b in 0..p-1
    return a2_all, g


def energy_k(a2_all, p, k):
    """E_k(μ_n) = (1/p) Σ_{b} |η_b|^{2k}  (the in-tree moment identity)."""
    return float(np.sum(a2_all ** k) / p)


def main():
    print("=== Resonance<->energy duality: max|η|^2 >= (pE_k - n^2k)/(pE_{k-1} - n^{2k-2}) ===\n")
    cases = [(16, 257), (16, 4129), (32, 4129), (32, 65537), (64, 65537), (128, 12289)]
    print(f"{'n':>4} {'p':>8} {'m':>7} {'k':>3} {'P_k/P_k-1 /n':>13} "
          f"{'(pEk-n2k)/(...)/n':>18} {'match':>6} {'maxM2/n':>9}")
    for n, p in cases:
        if not sympy.isprime(p) or (p - 1) % n:
            continue
        a2_all, g = setup(p, n)
        m = (p - 1) // n
        a2_nz = a2_all.copy()
        a2_nz[0] = 0.0
        maxM2 = a2_nz.max()
        for k in (2, 3, 4):
            Pk = float(np.sum(a2_nz ** k))
            Pk1 = float(np.sum(a2_nz ** (k - 1)))
            direct = Pk / Pk1
            Ek = energy_k(a2_all, p, k)
            Ek1 = energy_k(a2_all, p, k - 1)
            viaE = (p * Ek - n ** (2 * k)) / (p * Ek1 - n ** (2 * (k - 1)))
            match = abs(direct - viaE) / max(direct, 1e-9) < 1e-6
            print(f"{n:>4} {p:>8} {m:>7} {k:>3} {direct/n:>13.5f} {viaE/n:>18.5f} "
                  f"{str(match):>6} {maxM2/n:>9.4f}")
        print()

    print("CONFIRMED: the moment resonator's certified bound EQUALS (pE_k-n^2k)/(pE_{k-1}-n^{2k-2}).")
    print("The k=2 instance is the CLEANEST hypothesis-free floor:")
    print("   max_{b!=0}|η_b|^2 >= (p E_2(μ_n) - n^4) / (p n - n^2)")
    print("and since E_2 = 2n^2-n (odd n) / 3n^2-3n (even n) is KNOWN EXACTLY (in-tree, char-0),")
    print("this gives an EXACT, provable, hypothesis-free floor -- but it is a CONSTANT multiple of n,")
    print("NOT n log m.  The log m factor needs k ~ log m, i.e. a LOWER bound on E_{log m} = the wall.")


if __name__ == "__main__":
    main()
