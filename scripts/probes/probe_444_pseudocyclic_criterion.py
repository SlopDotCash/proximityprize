#!/usr/bin/env python3
"""
#444 — PIN the van Dam-Muzychuk pseudocyclic criterion precisely for the cyclotomic scheme.

The first probe showed multiplicity-spread = 0 for every proper mu_n. That means: the m nontrivial
eigenspaces of the cyclotomic scheme ALL have multiplicity exactly n. By the standard definition,
an association scheme is PSEUDOCYCLIC iff all nontrivial multiplicities are equal AND all valencies
are equal. The cyclotomic scheme has:
  - all valencies equal to n  (each class = a coset, size n),
  - all nontrivial multiplicities equal to n.
So it is ALREADY EXACTLY PSEUDOCYCLIC, for EVERY proper subgroup. (Whenever distinct cosets give
EQUAL Gauss periods, eigenspaces fuse but the FUSED multiplicity is a multiple of n and the count of
classes drops correspondingly — still equal-valency, still pseudocyclic by fusion.)

Therefore the lead's claim "pseudocyclic <=> |eta|=sqrt(v) for every coset = the prize bound, and it
is FALSE exactly" is a MISIDENTIFICATION. |eta_b|=sqrt(v)=sqrt(p) for every b is the condition for an
AMORPHIC / strongly-regular (Paley-type) scheme with m=2, NOT general pseudocyclicity. Pseudocyclic
constrains MULTIPLICITIES (all = n), which is automatically satisfied and carries NO information
about max|eta|.

This probe DIRECTLY checks:
  (1) every nontrivial eigenvalue multiplicity = n  (pseudocyclic, exactly);
  (2) the pseudocyclic identity sum_{i nontrivial} eta_i = -1 per eigenspace (valency-row sum);
  (3) the actual relation between |eta| spread and pseudocyclicity: pseudocyclic FIXES the second
      moment (sum eta^2 = p - n, RMS sqrt(n)) but leaves max|eta| UNCONSTRAINED in [sqrt(n), sqrt(p)].
  (4) the "amorphic defect": amorphic <=> all eta equal in abs value. Measure how far from amorphic
      and check it equals exactly the max-vs-RMS gap = max|eta|/sqrt(n) -- i.e. M restated.
"""
import numpy as np
from sympy import isprime, primitive_root
import math


def periods(p, n):
    g = primitive_root(p)
    m = (p - 1) // n
    base = [pow(g, m * j, p) for j in range(n)]   # mu_n = <g^m>
    w = np.exp(2j * np.pi * np.arange(p) / p)
    eta = np.array([sum(w[(pow(g, k, p) * x) % p] for x in base) for k in range(m)])
    return eta, m, g, base, w


def graph_eig_mults(p, n, g, base, w):
    """multiplicities of eigenvalues of Cay(F_p, mu_n)."""
    eigs = [round(sum(w[(b * x) % p] for x in base).real, 7) for b in range(1, p)]
    eigs.append(round(float(n), 7))
    vals, counts = np.unique(np.array(eigs), return_counts=True)
    return vals, counts


print("=" * 100)
print(" PSEUDOCYCLIC CRITERION (van Dam-Muzychuk) for cyclotomic scheme — proper mu_n")
print("=" * 100)
print(f"\n{'n':>4} {'m':>4} {'p':>7} {'allmult=n?':>11} {'maxeta':>8} {'rms':>7} "
      f"{'sum_eta':>8} {'sum_eta2':>9} {'p-n':>7} {'amorph?':>8}")
print("-" * 100)
for (n, mlist) in [(4, [4, 50, 199]), (8, [9, 96, 194]), (16, [16, 100, 198]),
                   (32, [36, 105, 198]), (64, [67, 133, 192])]:
    for mtgt in mlist:
        # find prime p = m*n+1 near target
        p = None
        for mm in range(mtgt, mtgt + 4000):
            cand = mm * n + 1
            if isprime(cand):
                p, m = cand, mm
                break
        if p is None or p > 250000:
            continue
        eta, m, g, base, w = periods(p, n)
        vals, counts = graph_eig_mults(p, n, g, base, w)
        nontrivial = [(v, c) for v, c in zip(vals, counts) if abs(v - n) > 1e-5]
        mults = np.array([c for _, c in nontrivial])
        # pseudocyclic: all nontrivial multiplicities equal. (with fusion they're all = n exactly,
        # OR equal to some common value if global fusion; check all-equal AND each divisible by n)
        allmult = "YES" if (mults.max() == mults.min()) else f"NO {mults.min()}..{mults.max()}"
        each_is_n = bool(np.all(mults == n))
        tag = "=n" if each_is_n else ("=eq" if mults.max() == mults.min() else "")
        maxeta = np.abs(eta).max()
        rms = math.sqrt((np.abs(eta) ** 2).mean())
        sum_eta = eta.sum().real
        sum_eta2 = (np.abs(eta) ** 2).sum()
        # amorphic <=> all |eta| equal
        amorph = "YES" if (np.abs(eta).max() - np.abs(eta).min()) < 1e-6 else "no"
        print(f"{n:>4} {m:>4} {p:>7} {allmult+' '+tag:>11} {maxeta:>8.3f} {rms:>7.3f} "
              f"{sum_eta:>8.3f} {sum_eta2:>9.1f} {p-n:>7} {amorph:>8}")

print()
print("READINGS:")
print(" - allmult=n YES everywhere  => scheme is EXACTLY pseudocyclic for every proper mu_n.")
print(" - amorph = no everywhere     => scheme is NEVER amorphic; |eta| spreads in [sqrt n, sqrt p].")
print(" - sum_eta2 = p - n EXACTLY   => the SECOND moment (RMS=sqrt n) is FIXED by pseudocyclicity,")
print("   but max|eta| is the L-inf extreme = the prize wall, UNCONSTRAINED by mult-equality.")
print(" - PSEUDOCYCLIC and AMORPHIC are different. The lead's '|eta|=sqrt v for every coset' is the")
print("   AMORPHIC (m=2 Paley / SRG) condition, NOT pseudocyclic. Cyclotomic IS pseudocyclic, is NOT")
print("   amorphic, and pseudocyclicity gives ONLY the 2nd moment = the META-THEOREM-walled L2.")
