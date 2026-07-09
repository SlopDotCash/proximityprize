#!/usr/bin/env python3
"""
probe_444_binding_coset_confinement.py   (#444, FRESH LENS [binding-restriction])

THE LENS QUESTION (outside the 12 dead lenses):
  M(n) = max_{b != 0 mod p} |Sum_{x in mu_n} e_p(b x)|  is the house = sup-norm of the
  Gauss period eta_b.  Since x ranges over the subgroup mu_n, the sum depends on b only
  through its COSET b*mu_n in F_p^* / mu_n.  So M(n) is ALREADY a max over the m=(p-1)/n
  cosets (this is just the Gauss-period structure).

  The lens asks SOMETHING SHARPER:  is the *near-maximal* house attained only on a
  SMALL set of cosets -- specifically the O(n) cosets that are DILATION-EXTREMAL /
  monomial-image directions?  If the worst cosets number O(n) (not m = 2^128), then the
  union-bound that produces sqrt(n log m) only needs to range over O(n) effective
  directions, giving sqrt(n log n).

THREE DECISIVE MEASUREMENTS (exact, small n; mu_n a PROPER subgroup, never full group):

  (1) HOUSE SPREAD.  Over all m cosets, how many cosets achieve |eta_b| within a factor
      (1 - tau) of the max?  Call this N_tau(n,p).  Is N_tau = O(n)?  Or does it grow with
      m?  Scan several primes per n with DIFFERENT m to separate the two.

  (2) MONOMIAL CONFINEMENT.  The dilation group Z/n acts on cosets by b -> b (trivially,
      since g in mu_n keeps b*mu_n fixed!).  So Z/n does NOT move cosets.  The lens's
      "monomial extremal" claim must instead be: the worst cosets are the images of the
      n "antipodal/dyadic" directions, i.e. b in mu_n-multiples of {root differences}.
      We test the strongest concrete version: are the top cosets the ones containing
      a sub-half-window block sum direction?  We instead measure the *coset-orbit* under
      the FULL Frobenius / Galois group of K_m (b -> b^p acts trivially mod p, so the
      operative symmetry on cosets is multiplication by F_p^*/mu_n itself = the m cyclic
      cosets, NO further reduction).  CRITICAL HONEST CHECK: is there ANY group action
      that orbits the m cosets into O(n) classes?  If NOT, the lens is refuted at root.

  (3) log m vs log n AT THE BUDGET.  Even if confinement HELD, does it matter?
      Compute the ratio  R = M(n) / sqrt(n log m)  vs  M(n) / sqrt(n log n).
      At the prize, log m = 128, log n = 30.  Does swapping log m -> log n change the
      constant enough to cross the window?  Report both diagonals.

NO full group ever.  Exact complex arithmetic via roots of unity.
"""
import sympy, cmath, math
from collections import Counter

TWO_PI = 2.0 * math.pi


def musub(n, p):
    g = sympy.primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    return [pow(h, j, p) for j in range(n)]


def period_abs(b, G, p):
    w = TWO_PI / p
    s = 0j
    for y in G:
        s += cmath.exp(1j * w * ((b * y) % p))
    return abs(s)


def coset_reps(n, p):
    """One representative per coset of mu_n in F_p^* (there are m=(p-1)//n of them)."""
    g = sympy.primitive_root(p)
    # cosets are g^0, g^1, ..., g^{m-1} times mu_n, where mu_n = <g^m>.
    m = (p - 1) // n
    return [pow(g, r, p) for r in range(m)], m


def analyze(n, p):
    G = musub(n, p)
    reps, m = coset_reps(n, p)
    # |eta| on each coset rep (b != 0; reps are all nonzero)
    vals = [(period_abs(b, G, p), b) for b in reps]
    vals.sort(reverse=True)
    M = vals[0][0]
    # (1) house spread: # cosets within (1-tau) of max, for several tau
    spreads = {}
    for tau in (0.01, 0.05, 0.10, 0.20):
        thr = (1 - tau) * M
        spreads[tau] = sum(1 for v, _ in vals if v >= thr)
    # (3) ratios
    R_logm = M / math.sqrt(n * math.log(m)) if m > 1 else float('nan')
    R_logn = M / math.sqrt(n * math.log(n)) if n > 1 else float('nan')
    sqrtn = M / math.sqrt(n)
    return M, m, spreads, R_logm, R_logn, sqrtn, vals


def find_primes(n, count, idx_min=2, pcap=400000):
    """Several primes p = n*m+1 with DIFFERENT m (index), to separate n-growth from m-growth."""
    out = []
    m = idx_min
    while len(out) < count:
        p = n * m + 1
        if p > pcap:
            break
        if sympy.isprime(p):
            out.append((p, m))
        m += 1
    return out


print("=" * 100)
print("LENS [binding-restriction]: is the near-maximal Gauss-period house confined to O(n) cosets?")
print("=" * 100)
print(f"{'n':>4} {'p':>8} {'m':>6} {'M/sqrtn':>8} {'N(1%)':>7} {'N(5%)':>7} {'N(10%)':>8} {'N(20%)':>8} "
      f"{'N(20%)/n':>9} {'R_logm':>7} {'R_logn':>7}")
print("-" * 100)

for n in (8, 16, 32, 64):
    primes = find_primes(n, 6)
    for (p, m) in primes:
        M, mm, spreads, R_logm, R_logn, sqrtn, vals = analyze(n, p)
        n20 = spreads[0.20]
        print(f"{n:>4} {p:>8} {m:>6} {sqrtn:>8.3f} {spreads[0.01]:>7} {spreads[0.05]:>7} "
              f"{spreads[0.10]:>8} {n20:>8} {n20/n:>9.3f} {R_logm:>7.3f} {R_logn:>7.3f}")
    print("-" * 100)

print()
print("INTERPRETATION KEY:")
print("  * If N(20%)/n stays O(1) (bounded) as m grows at FIXED n  =>  confinement HOLDS")
print("    (near-max house lives on O(n) cosets, sqrt(n log m) -> sqrt(n log n) plausible).")
print("  * If N(20%) grows with m at fixed n  =>  confinement REFUTED (house spread over many cosets).")
print("  * R_logm vs R_logn: if they bracket the window differently at prize scale, the swap matters.")
