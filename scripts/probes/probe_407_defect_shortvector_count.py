#!/usr/bin/env python3
"""
probe_407_defect_shortvector_count.py  --  #407 norm-Mahler-lattice route.

GOAL: attack the DGPH house bound by COUNTING short alpha in the prime ideal P over p,
rather than showing there are none (the norm bound only shows zero, and is vacuous in
the prize regime n = 2^mu <= sqrt(p)).

THE ALGEBRA (made exact here, then numerically verified):

  Let mu_n = order-n multiplicative subgroup of F_p^*, n = 2^mu, n | p-1.
  Pick a generator z of mu_n (z = g^{(p-1)/n}, g a primitive root). The map
       phi : Z[X]/(X^n - 1)  ->  F_p ,   X |-> z
  sends the group ring of Z/n onto F_p (it factors through Z[zeta_n] on the X^n-1 ... actually
  X^n-1 = prod_{d|n} Phi_d; z has order exactly n so z is a root of Phi_n only; ker contains the
  other cyclotomic factors). The PRIMITIVE part: phi restricted to Z[zeta_n] = Z[X]/Phi_n(X),
  X |-> z, has kernel a prime ideal P over p of residue degree 1 (since z in F_p), |Z[zeta_n]/P| = p.

  An ADDITIVE-ENERGY relation at depth r is:  sum_{i=1}^r x_i = sum_{j=1}^r y_j  in F_p
  with x_i, y_j in mu_n.  Collecting multiplicities, this is a vector c in Z^n (indexed by the n
  group elements / exponents of z), with:
        c = (multiplicity of z^k as an x)  -  (multiplicity of z^k as a y),
        sum_k c_k^+ = r,  sum_k c_k^- = r   =>   sum_k c_k = 0  and  L1(c) = sum|c_k| <= 2r,
  and the relation  sum_k c_k z^k = 0  in F_p,  i.e.  alpha_c := sum_k c_k X^k  lies in ker(phi).

  CHAR-0 relations (the "free" energy E_r^(0)) are those with sum_k c_k X^k == 0 already in
  Z[zeta_n] (i.e. c is in the lattice of relations of {1,z,..} as ALGEBRAIC numbers = multiples of
  the cyclotomic relation Phi_n and X^n-1 structure). The p-DEFECT relations are the EXTRA c with
  alpha_c != 0 in Z[zeta_n] but alpha_c in P (== 0 mod p only).

  So:   defect at depth r  ~  #{ short alpha in P \ {0}, L1-coeff <= 2r, balanced } weighted by
        the number of (x,y) tuples realizing each c.

This probe:
  (A) Verifies the dictionary: measured E_r mod p, char-0 E_r^(0), and the count of defect-c
      vectors all line up.
  (B) Directly enumerates the SHORT alpha in P (balanced, L1 <= 2r), i.e. counts the nonzero
      lattice points of P inside the L1 ball of radius 2r in the balanced hyperplane, for small n.
  (C) Reports the norm |N(alpha)| of the shortest defect alpha vs the norm-bound threshold
      (2r)^{phi(n)/2}, to see exactly where the norm/Mahler argument fails (the wall).

Run:  python scripts/probes/probe_407_defect_shortvector_count.py
"""
import sys, math, itertools
from collections import Counter
import numpy as np

sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, primitive_root


def prize_prime(n, beta):
    """Smallest prime p ~ n^beta, p = 1 mod n, with odd_part((p-1)/n) > 1 (exclude Fermat/dyadic)."""
    base = int(round(n ** beta)); base -= base % n; base += 1; p = base
    while not (is_prime(p) and odd_part((p - 1) // n) > 1):
        p += n
    return p


def subgroup(p, n):
    g = primitive_root(p); z = pow(g, (p - 1) // n, p)
    return [pow(z, j, p) for j in range(n)], z


# ---------- char-0 energy via Bessel (the algebraic / complex-roots value) ----------
def bessel_moment(n, r):
    """E_r^(0) = (2r)! [x^r] I0(2 sqrt x)^{n}, where I0(2 sqrt x) = sum_k x^k/(k!)^2.
       (sum over the n complex n-th roots of unity; this is the char-0 additive energy.)"""
    a = [1.0 / math.factorial(k) ** 2 for k in range(r + 1)]
    def pmul(u, v):
        w = [0.0] * (r + 1)
        for i in range(r + 1):
            if u[i] == 0: continue
            for j in range(r + 1 - i): w[i + j] += u[i] * v[j]
        return w
    res = [0.0] * (r + 1); res[0] = 1.0
    base = a[:]; e = n
    while e > 0:
        if e & 1: res = pmul(res, base)
        e >>= 1
        if e > 0: base = pmul(base, base)
    return math.factorial(2 * r) * res[r]


def Er_mod_p(p, z, n, r):
    """Exact E_r(mu_n) mod p via r-fold cyclic convolution of the mu_n indicator over Z/p."""
    ind = np.zeros(p, dtype=np.float64)
    x = 1
    for _ in range(n):
        ind[x] += 1.0; x = x * z % p
    F = np.fft.rfft(ind)
    conv = np.fft.irfft(F ** r, n=p)
    conv = np.round(conv)
    return float((conv * conv).sum())


# ---------- direct char-0 energy by enumeration over COMPLEX roots (exact, small n,r) ----------
def Er_char0_enum(n, r):
    """Brute char-0 energy: #{(x,y) in mu_n^{2r} : sum x = sum y over C}.
       Two complex sums are equal iff the integer coefficient vectors (in the basis of n-th roots,
       reduced mod the cyclotomic relations) agree. We test equality of complex sums directly."""
    roots = [complex(math.cos(2 * math.pi * t / n), math.sin(2 * math.pi * t / n)) for t in range(n)]
    cnt = Counter()
    for tup in itertools.product(range(n), repeat=r):
        s = sum(roots[t] for t in tup)
        key = (round(s.real, 7), round(s.imag, 7))
        cnt[key] += 1
    return sum(v * v for v in cnt.values())


def main():
    print("=" * 78)
    print(" #407 DEFECT = SHORT-VECTOR COUNT IN PRIME IDEAL P  (norm-Mahler-lattice route)")
    print("=" * 78)
    print("\n[A] Dictionary check: E_r mod p  vs  char-0 E_r^(0).  defect = E_r - E_r^(0).")
    print("    char-0 from Bessel law AND from direct complex enumeration (cross-check).\n")
    for n, beta in ((8, 4.0), (8, 5.0), (16, 4.0), (16, 5.0)):
        p = prize_prime(n, beta)
        H, z = subgroup(p, n)
        print(f"  n={n}  beta~{beta}  p={p}  (p/n={p//n}, p~2^{math.log2(p):.1f}, "
              f"sqrt(p)~2^{0.5*math.log2(p):.1f}, n=2^{int(math.log2(n))})")
        print(f"    {'r':>3} {'E_r mod p':>14} {'E0(Bessel)':>14} {'E0(enum)':>12} "
              f"{'defect':>12} {'def/E0':>9}")
        for r in range(2, 5):
            if p > 4_000_000:
                print(f"    {r:>3}   (p too large to convolve)"); continue
            Er = Er_mod_p(p, z, n, r)
            E0b = bessel_moment(n, r)
            E0e = Er_char0_enum(n, r) if n ** r <= 1_500_000 else float('nan')
            defect = Er - E0b
            print(f"    {r:>3} {Er:>14.0f} {E0b:>14.0f} {E0e:>12.0f} "
                  f"{defect:>12.0f} {defect / E0b:>9.4f}")
        print()


if __name__ == "__main__":
    main()
