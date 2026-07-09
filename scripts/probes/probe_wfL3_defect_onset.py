#!/usr/bin/env python3
"""
probe_wfL3_defect_onset.py  --  #444 [moment] DC-subtracted-energy OVERSHOOT onset.

THE QUESTION (task wfL3): does the DC-subtracted additive energy
    A_r(mu_n) := E_r(mu_n) - n^{2r}/p
EVER strictly exceed the char-0 Wick bound  Wick(n,r) := (2r-1)!! * n^r  ?
If yes, the moment method's energy INPUT is FALSE (not merely unprovable-by-height)
at the depth where A_r > Wick, killing the moment route by ALL routes.

EXACT spectral identities (proper subgroup mu_n <= F_p^*, n | p-1, n=2^mu):
    E_r(mu_n) = (1/p) * sum_{t in F_p} |eta_t|^{2r},   eta_t = sum_{x in mu_n} e_p(t x).
    |eta_0| = n  =>  DC term = n^{2r}/p.
    A_r = E_r - n^{2r}/p = (1/p) * sum_{t != 0} |eta_t|^{2r}   (the NON-trivial spectral moment).
So A_r is computed EXACTLY two ways and cross-checked:
   (a) char-sum:  A_r = (1/p) sum_{t!=0} |eta_t|^{2r}    [from the p eigenvalues eta_t]
   (b) combinatorial:  E_r exact integer count via FFT convolution of the indicator, minus n^{2r}/p.

Wick = (2r-1)!! * n^r is the Lam-Leung char-0 ceiling for the DC-subtracted energy.
A_r^{c0} := E_r^{(0)} (char-0 EXACT, cyclotomic reduced-power-basis hash) - 0  is reported
for reference: in char 0 there is no DC term (the sum-of-roots lives in Z[zeta], the value
n^{2r}/p has no char-0 meaning), and A_r^{c0} = E_r^{(0)} <= Wick ALWAYS (Lam-Leung).

We sweep proper subgroups n in {8,16,32} at primes p with n|p-1 and beta=log_n p ~ 4,
NEVER the full group (require odd_part((p-1)//n) > 1 so mu_n is a PROPER subgroup with a
nontrivial multiplicative complement -- the prize regime). For each we report:
   r ; E_r ; A_r ; Wick ; A_r/Wick ; flag onset (first r with A_r > Wick).

Run:  python scripts/probes/probe_wfL3_defect_onset.py
"""
import sys, math, itertools
from collections import Counter
import numpy as np
import sympy


def is_prime(n):
    return sympy.isprime(n)


def odd_part(x):
    while x % 2 == 0 and x > 0:
        x //= 2
    return x


def primitive_root(p):
    return int(sympy.primitive_root(p))


def double_fact_odd(r):
    """(2r-1)!! = product of odd numbers 1*3*...*(2r-1); (2*0-1)!! = 1."""
    v = 1
    for j in range(r):
        v *= (2 * j + 1)
    return v


def reduction_table(n):
    """Reduce X^k mod Phi_n(X) into the phi(n)-dim power basis, integer coeffs."""
    x = sympy.symbols('x')
    Phi = sympy.Poly(sympy.cyclotomic_poly(n, x), x)
    phi_n = Phi.degree()
    Phi_coeffs = [int(c) for c in Phi.all_coeffs()][::-1]  # ascending
    redtab = [[0] * phi_n for _ in range(n)]
    for k in range(phi_n):
        redtab[k][k] = 1
    for k in range(phi_n, n):
        prev = redtab[k - 1]
        shifted = [0] * (phi_n + 1)
        for i in range(phi_n):
            shifted[i + 1] += prev[i]
        top = shifted[phi_n]
        for i in range(phi_n):
            shifted[i] -= top * Phi_coeffs[i]
        redtab[k] = shifted[:phi_n]
    return redtab, phi_n


def Er_char0(n, r, redtab, phi_n):
    """EXACT char-0 additive energy E_r^{(0)} = #{a,b in mu_n^r : sum a = sum b}
       via reduced-power-basis hash of the multiset sums (integer-exact)."""
    cnt = Counter()
    for tup in itertools.product(range(n), repeat=r):
        v = [0] * phi_n
        for t in tup:
            rk = redtab[t]
            for i in range(phi_n):
                v[i] += rk[i]
        cnt[tuple(v)] += 1
    return sum(c * c for c in cnt.values())


def Er_mod_p_fft(p, z, n, r):
    """EXACT E_r mod p via integer FFT convolution of the mu_n indicator (r-fold),
       then sum of squares of the (integer) coincidence counts. Returns int."""
    ind = np.zeros(p, dtype=np.float64)
    x = 1
    for _ in range(n):
        ind[int(x)] += 1.0
        x = x * z % p
    F = np.fft.rfft(ind)
    conv = np.round(np.fft.irfft(F ** r, n=p)).astype(np.int64)
    return int((conv.astype(object) * conv.astype(object)).sum())


def eta_eigenvalues_sqabs(p, z, n):
    """|eta_t|^2 for all t in F_p, where eta_t = sum_{x in mu_n} e_p(t x).
       Returns a float64 array of length p (|eta_0|^2 = n^2 exactly)."""
    ind = np.zeros(p, dtype=np.float64)
    x = 1
    for _ in range(n):
        ind[int(x)] += 1.0
        x = x * z % p
    eta = np.fft.fft(ind)          # eta[t] = sum_x ind[x] e^{-2pi i t x / p} = sum_{x in mu_n} e_p(-t x)
    return (eta.real ** 2 + eta.imag ** 2)


def Ar_from_spectrum(sqabs, p, n, r):
    """A_r = (1/p) sum_{t != 0} |eta_t|^{2r}  (exact spectral form, t=0 excluded)."""
    # exclude t=0
    s = float(np.sum(sqabs[1:] ** r))
    return s / p


def prize_prime(n, beta, pmax, idx_min=2):
    """Smallest prime p ~ n^beta with n | p-1, mu_n a PROPER subgroup
       (odd_part((p-1)//n) > 1 so there is a nontrivial multiplicative complement)."""
    base = int(round(n ** beta))
    base -= base % n
    base += 1
    p = base
    while p < pmax:
        if is_prime(p) and (p - 1) % n == 0 and odd_part((p - 1) // n) > 1 and (p - 1) // n >= idx_min:
            return p
        p += n
    return None


def main():
    print("=" * 96)
    print(" #444 wfL3:  DC-SUBTRACTED ENERGY OVERSHOOT  A_r = E_r - n^{2r}/p   vs   Wick = (2r-1)!! n^r")
    print("           (proper subgroups mu_n <= F_p^*, n=2^mu, n|p-1, beta=log_n p ~ 4, NEVER full group)")
    print("=" * 96)
    print(" Claim under test: 'onset at r ~ rMax = 2 beta' where A_r first exceeds Wick.")
    print(" A_r computed 2 ways (combinatorial E_r - n^{2r}/p  AND  spectral (1/p) sum_{t!=0} |eta_t|^{2r});")
    print(" they must agree. Char-0 E_r^{(0)} <= Wick always (Lam-Leung) -- reported as the clean baseline.\n")

    configs = [
        (8,  [3.5, 3.8, 4.0],  3_300_000),
        (16, [3.8, 4.0],        9_000_000),
        (32, [3.8, 4.0],       40_000_000),
    ]

    for n, betas, pmax in configs:
        redtab, phi_n = reduction_table(n)
        for beta in betas:
            p = prize_prime(n, beta, pmax)
            if p is None:
                print(f"  n={n} beta={beta}: no proper-subgroup prize prime under {pmax}\n")
                continue
            g = primitive_root(p)
            z = pow(g, (p - 1) // n, p)
            sqabs = eta_eigenvalues_sqabs(p, z, n)
            Mn = math.sqrt(float(np.max(sqabs[1:])))   # house M(n) = max_{t!=0} |eta_t|
            actual_beta = math.log(p) / math.log(n)
            rMax = int(2 * actual_beta)
            lnp = math.log(p)
            ropt = max(2, int(round(lnp)))
            # how deep can we exactly compute char-0?  n^r <= ~2e7
            r_c0_max = int(math.log(2.0e7) / math.log(n))
            print(f"--- n={n}  p={p} (2^{math.log2(p):.2f})  beta={actual_beta:.3f}  m=(p-1)/n=2^{math.log2((p-1)/n):.1f} ---")
            print(f"    house M(n)=max_{{t!=0}}|eta_t|={Mn:.2f}=2^{math.log2(Mn):.2f} (sqrt n=2^{0.5*math.log2(n):.2f}, sqrt(n*ln m)=2^{0.5*math.log2(n*math.log((p-1)/n)):.2f})")
            print(f"    rMax=floor(2 beta)={rMax}   r_opt~ln p={ropt}   (char-0 exact reachable to r={r_c0_max})")
            print(f"    {'r':>3} {'E_r (mod p)':>20} {'A_r=E_r-DC':>20} {'Wick=(2r-1)!!n^r':>22} {'A_r/Wick':>10} {'spec-chk':>9} {'E_r^(0)/Wick':>13}")
            onset = None
            rmax_feasible = min(ropt + 4, 13)
            for r in range(1, rmax_feasible + 1):
                Er = Er_mod_p_fft(p, z, n, r)
                dc = (n ** (2 * r)) / p
                Ar = Er - dc
                Ar_spec = Ar_from_spectrum(sqabs, p, n, r)
                wick = double_fact_odd(r) * (n ** r)
                ratio = Ar / wick
                spec_ok = "ok" if abs(Ar_spec - Ar) / max(1.0, abs(Ar)) < 1e-6 else f"MISMATCH({Ar_spec:.3e})"
                if r <= r_c0_max:
                    E0 = Er_char0(n, r, redtab, phi_n)
                    e0r = f"{E0 / wick:.4f}"
                else:
                    e0r = "  (too big)"
                tag = ""
                if ratio > 1.0 and onset is None:
                    onset = r
                    tag = "  <== A_r > Wick ONSET"
                if r == rMax:
                    tag += "  [rMax]"
                if r == ropt:
                    tag += "  [r_opt]"
                print(f"    {r:>3} {Er:>20d} {Ar:>20.2f} {wick:>22d} {ratio:>10.4f} {spec_ok:>9} {e0r:>13}{tag}")
            if onset is None:
                print(f"    >>> NO onset up to r={rmax_feasible}: A_r STAYS BELOW Wick (DC-subtraction keeps it clean).")
            else:
                print(f"    >>> ONSET at r={onset}.  (rMax=floor(2 beta)={rMax}, r_opt={ropt}.)  onset vs rMax: {'<' if onset<rMax else ('=' if onset==rMax else '>')}")
            print()

    print("KEY READING:")
    print(" - If A_r/Wick stays <= 1 up to r_opt: A_r NEVER overshoots Wick => the energy INPUT is")
    print("   TRUE (just unproven in char-p) at every reachable depth => NO 'A_r > Wick' overshoot;")
    print("   the no-go is a transfer/proof obstruction, NOT an energy-falsity obstruction.")
    print(" - If A_r/Wick > 1 at some onset r0: the DC-subtracted energy GENUINELY exceeds the char-0")
    print("   ceiling there; the moment method's hypothesis is FALSE (not just unprovable) at r0.")
    print(" - Compare onset r0 to rMax=2 beta and r_opt: onset BELOW r_opt would close the scoping gap.")


if __name__ == "__main__":
    main()
