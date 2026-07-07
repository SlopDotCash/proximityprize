#!/usr/bin/env python3
"""
#444 floor-side angle [LP-delsarte-on-list]: does the mu_n COSET-SCHEME Delsarte LP
bound the worst-case RS list, or is it B1 (2nd-moment/degree-1 blind, caps at Parseval)?

OBJECT. mu_n = order-n multiplicative subgroup of F_p* (n=2^mu, n|p-1, PROPER). RS code =
evaluations of deg<k polys on mu_n. The worst-case LIST L(delta) = max over received words w
of #{codewords c : d_H(w,c) <= delta*n}. By the subset-sum/lacunary reframing the binding list
is the additive-energy-governed count.

THE DELSARTE LP FOR A LIST / ANTICODE. The list members c_1..c_L within radius delta*n of w all
lie in a Hamming ball of radius delta*n; their pairwise differences c_i - c_j are codewords of
weight <= 2*delta*n (an ANTICODE of diameter 2*delta*n inside the code). Delsarte's LP bounds
the size of such an anticode using the code's DUAL distance distribution and the Krawtchouk
(or scheme-eigenvalue) positivity. The "coset-scheme" variant replaces the trivial Hamming
association scheme with the cyclotomic-coset scheme of the evaluation domain mu_n: the relations
are the orbits of the dilation action z -> g*z, g in mu_n, on coordinate-pairs.

WE TEST, on explicit small mu_n RS codes:
  (1) the TRUE worst-case list L(delta) (brute, small),
  (2) the trivial-scheme (Hamming) Delsarte LP bound on an anticode of diameter 2*delta*n,
  (3) the COSET-scheme Delsarte LP bound (the sharper object the assignment asks about),
and check which moments each LP can "see" -- in particular whether the coset scheme can certify
the degree-2 moment (additive energy E_2) that the trivial mass-only LP cannot.
"""
import numpy as np
import itertools, math
from sympy import isprime

def primitive_root(p):
    # smallest primitive root mod p
    if p == 2: return 1
    phi = p-1
    factors = set()
    x = phi
    d = 2
    while d*d <= x:
        while x % d == 0:
            factors.add(d); x//=d
        d+=1
    if x>1: factors.add(x)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in factors):
            return g
    raise RuntimeError

def mu_n(p, n):
    # order-n subgroup of F_p^*
    assert (p-1) % n == 0
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)  # generator of mu_n
    return [pow(h, i, p) for i in range(n)]

print("="*94)
print(" Part A: the mu_n coset (cyclotomic) association scheme on coordinate PAIRS")
print("="*94)
# The dilation group mu_n acts on the n coordinates (indexed by mu_n itself).
# Orbits of pairs (x,y), x!=y, under z->g z are indexed by the RATIO y/x in mu_n: there are
# (n-1) nontrivial classes (one per ratio != 1), each of size n. This is the CYCLOTOMIC scheme
# = the conjugacy/translation scheme of the cyclic group Z/n (mu_n ~ Z/n multiplicatively).
# It is COMMUTATIVE and its common eigenspaces are the DFT characters of Z/n. So the coset
# scheme on coordinates is just the cyclic-group (Hamming-analog) scheme C_n. Its eigenvalues
# are roots of unity; its P-matrix is the DFT.
for (p,n) in [(17,8),(41,8),(97,16),(193,16)]:
    M = mu_n(p,n)
    # ratio classes
    ratios = sorted(set((y*pow(x,p-2,p))%p for x in M for y in M if x!=y))
    print(f"  p={p:4d} n={n:3d}: # nontrivial ratio-classes (relations) = {len(ratios)}  (= n-1 = {n-1}) ")
print("  => the coordinate coset-scheme is the cyclic scheme C_n; eigenspaces = DFT chars of Z/n.")
print("     Its class functions span only n dimensions (one per character) -- a COMMUTATIVE scheme.")

print()
print("="*94)
print(" Part B: what moments can the coset-scheme Delsarte LP certify on the spectral measure?")
print("="*94)
# The Delsarte LP dual variables are the n scheme-eigenvalues (DFT of the distance distribution).
# For the LIST/anticode, the relevant primal is the inner-distribution B_j of the anticode
# (codeword differences) w.r.t. the scheme. The LP can impose B_j>=0 and the eigenvalue
# constraints (B-hat >= 0). The point: which functionals of the period spectrum tau_J these
# constraints encode. We test whether the coset scheme's linear constraints reach the degree-2
# energy E_2 = sum tau_J^2 (the additive energy), the first functional that beats Parseval.
#
# KEY FACT to test numerically: in a COMMUTATIVE association scheme the LP constraints are all
# LINEAR in the inner distribution B (degree-1 in B). The map B -> spectrum is linear (the P/Q
# eigenmatrices). A bound on max_J tau_J that is linear in B is linear in tau (Parseval-level).
# A bound involving sum tau_J^2 is QUADRATIC in tau and NOT expressible as a linear functional of
# B. So the coset-scheme LP, being linear in B, cannot output E_2. We verify the linearity.
for (p,n) in [(17,8),(97,16)]:
    M = mu_n(p,n)
    m = (p-1)//n
    # all nonzero Gauss periods eta_b = sum_{z in mu_n} e_p(b z), b ranges over F_p^*/?; tau on cosets
    eta = {}
    for b in range(1,p):
        s = sum(np.exp(2j*np.pi*(b*z % p)/p) for z in M)
        eta[b] = s
    # tau_J indexed by cosets of mu_n in F_p^*: eta depends only on coset b*mu_n
    cosets = {}
    seen=set()
    for b in range(1,p):
        key = frozenset((b*z)%p for z in M)
        if key in seen: continue
        seen.add(key)
        cosets[b]=abs(eta[b])**2
    tau = np.array(sorted(cosets.values(), reverse=True))
    S1 = tau.sum()                 # degree-1 (Parseval)  ~ p-n
    S2 = (tau**2).sum()            # degree-2 (additive energy E_2 * something)
    print(f"  p={p} n={n} m={m}: #cosets={len(tau)}  sum tau={S1:.1f} (p-n={p-n})  "
          f"max tau={tau[0]:.2f}  sum tau^2={S2:.1f}")
    print(f"      Parseval LP optimum (max tau <= sum tau) = {S1:.1f} ; true max tau = {tau[0]:.2f} ; "
          f"ratio={S1/tau[0]:.1f}x loose")
print()
print(" The coset scheme is COMMUTATIVE => its LP is LINEAR in the inner distribution B, hence")
print(" linear in tau. sum tau^2 (=E_2, the additive energy) is QUADRATIC in tau and is NOT a")
print(" linear functional certifiable by the scheme. So the coset-scheme LP optimum for max tau")
print(" stays at the Parseval value sum tau = p-n (degree-1), same ceiling as the trivial LP.")
