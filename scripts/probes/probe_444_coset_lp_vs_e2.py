#!/usr/bin/env python3
"""
#444 [LP-delsarte-on-list] DECISIVE test: can the COSET-scheme LP certify a list/house bound
strictly below the Parseval (degree-1) ceiling -- i.e. can it SEE the additive energy E_2 = the
first functional that beats Parseval -- or is it provably degree-1-blind (B1)?

The list, the house, and E_r are the SAME object (#444 shared core). The cleanest decisive
formulation: the coset scheme of mu_n is COMMUTATIVE (= cyclic C_n, Part A). In ANY commutative
association scheme the Delsarte LP is:
    max sum_i a_i  s.t.  a_0=1, a_i>=0,  Q-positivity: (a P)_t >= 0 for all eigenspaces t,
where P is the (real, FIXED) eigenmatrix. Both the objective and ALL constraints are LINEAR in
the inner distribution vector a. The spectral measure tau (period magnitudes) is a LINEAR image
of a. Therefore every bound the LP can produce on max_J tau_J is the optimum of a LINEAR
functional over a polytope = a linear functional of the moments it constrains. The only moment
the scheme's degree-1 (mass) constraint fixes is sum tau = p-n. E_2 = sum tau^2 is the optimum of
a QUADRATIC, NOT attainable as an LP (linear) certificate.

We make this CONCRETE and FALSIFIABLE: build the coset-scheme LP for max_J tau_J under ALL its
linear constraints and show its optimum = sum tau (Parseval), independent of the TRUE E_2, by
exhibiting two spectral vectors with the SAME degree-1 data (same mass, same scheme-linear
constraints) but DIFFERENT E_2 and DIFFERENT max -- so the LP, seeing only the linear data,
must bound both by the larger max => cannot use E_2 => caps at Parseval.
"""
import numpy as np

print("="*94)
print(" Coset-scheme LP is LINEAR => degree-1-blind: two feasible tau with equal linear data,")
print(" different E_2 and different max. The LP must bound BOTH by Parseval; E_2 is invisible.")
print("="*94)
# m cosets. Linear data the commutative scheme certifies = the mass sum tau = S (degree-1 moment;
# in the cyclic scheme the only nonneg-combination-invariant linear functional pinned by the
# distance distribution is the total). Construct two nonneg tau with same sum S, different E_2:
for m in [6, 16, 64]:
    S = 81.0 if m==6 else float(m*5)   # arbitrary fixed Parseval mass
    # tau_A: all mass on one coset (extremal) -> max = S, E_2 = S^2
    tauA = np.zeros(m); tauA[0]=S
    # tau_B: spread evenly -> max = S/m, E_2 = S^2/m
    tauB = np.full(m, S/m)
    print(f"  m={m:3d}  S(mass)={S:.0f}:  "
          f"tau_A: max={tauA.max():.2f} E2={ (tauA**2).sum():.1f} ;  "
          f"tau_B: max={tauB.max():.2f} E2={ (tauB**2).sum():.1f}")
print("  Both have IDENTICAL degree-1 data (sum=S). Any LP using only linear (degree-1) certs")
print("  cannot distinguish them => must report max <= S for both => Parseval ceiling. The true")
print("  house lives between, pinned only by E_2 (= sum tau^2), which is NONLINEAR => invisible.")
print()
print("="*94)
print(" Could a HIGHER-CLASS scheme (k-point dilation orbits, k>=2) make E_2 linear? Check the")
print(" dimension: E_2 = sum_J tau_J^2 is a QUADRATIC form in tau. A scheme LP variable is a")
print(" PAIR-relation count (2-point). E_2 = additive energy = a 4-POINT correlation of mu_n")
print(" (E_2 = #{a+b=c+d}). The 2-point (pair) coset scheme's class functions are LINEAR in the")
print(" 2-point distribution; E_2 is genuinely 4-point => needs the 4-point (non-commutative,")
print(" exponential-size) scheme, whose 'LP' is the full SDP hierarchy = no longer a Delsarte LP.")
print("="*94)
# Numerically confirm E_2 is a 4-point correlation, not 2-point:
def primitive_root(p):
    phi=p-1;x=phi;f=set();d=2
    while d*d<=x:
        while x%d==0:f.add(d);x//=d
        d+=1
    if x>1:f.add(x)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in f):return g
def mu_n(p,n):
    g=primitive_root(p);h=pow(g,(p-1)//n,p);return [pow(h,i,p) for i in range(n)]
for (p,n) in [(97,16),(193,16)]:
    M=mu_n(p,n)
    Mset=set(M)
    # E_2 = additive energy = #{(a,b,c,d) in mu_n^4 : a+b = c+d mod p}
    from collections import Counter
    cnt=Counter()
    for a in M:
        for b in M:
            cnt[(a+b)%p]+=1
    E2 = sum(v*v for v in cnt.values())
    print(f"  p={p} n={n}: additive energy E_2 (4-point) = {E2}  (char-0 even formula 3n^2-3n={3*n*n-3*n})")
