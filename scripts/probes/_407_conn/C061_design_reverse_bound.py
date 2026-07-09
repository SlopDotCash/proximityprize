#!/usr/bin/env python3
"""
C061 attack: "List-dimension confinement (subspaceDesign_list_dim_bound) is the
missing REVERSE bound for the n^2-monomial-line concentration that pins delta*."

The claim: instantiate subspaceDesign_list_dim_bound at the monomial-line family
to get a cap |L| <= |F|^{r-1} that supplies the reverse (concentration) bound the
Poisson floor lacks, thereby pinning delta* in the prize regime.

We test the DECISIVE arithmetic.

The design list-dim bound (in-tree, axiom-clean) is:
   if r+1 codewords of a tau-subspace-design each agree with y on >= a coords, and
       tau(r)*n + r*n < (r+1)*a                                   (THRESHOLD)
   then their differences are dependent => list spans dim < r => |L| <= |F|^{r-1}.

Two questions decide whether this is a usable reverse bound in the PRIZE regime
(plain, UNFOLDED, smooth-domain RS, s=1):

  (Q1) What is tau(r) for PLAIN RS (s=1)?  A subspace-design parameter tau(r) is:
       max fraction of coordinates on which an r-dim subspace of the code can
       FULLY VANISH.  For RS[k] (polys of degree < k), an r-dim subspace contains
       nonzero polys; a nonzero poly of degree < k vanishes on <= k-1 points.
       So an r-dim subspace's COMMON vanishing set has <= k-1 coords for EVERY r>=1.
       => tau(r)*n = k-1  =>  tau(r) = (k-1)/n ~= rho, CONSTANT in r. (no folding gain)

  (Q2) Plug tau(r)=rho into the threshold and ask: at the prize window radius
       (agreement a = (1-delta)*n with delta = window interior), is the threshold
       tau(r)*n + r*n < (r+1)*a  ever satisfiable for r small enough that
       |F|^{r-1} <= budget = q*eps* ~= n ?  If r must be >= 2 to fire AND |F|^{r-1}
       already >> n, the bound is VACUOUS (gives nothing below near-capacity).
"""
import math

def H2(x):
    if x<=0 or x>=1: return 0.0
    return -x*math.log2(x)-(1-x)*math.log2(1-x)

print("="*78)
print("C061: design list-dim bound as the reverse concentration bound — PRIZE test")
print("="*78)

# ---- Q1: tau(r) for plain RS is constant = rho (a nonzero deg<k poly has <=k-1 roots)
print("\n[Q1] tau(r) for PLAIN RS (s=1):")
print("  An r-dim subspace of RS[k] = degree-<k polys. Its COMMON vanishing set on")
print("  the domain has size <= (# common roots of a nonzero member) <= k-1.")
print("  => tau(r)*n <= k-1  for ALL r>=1  =>  tau(r) = (k-1)/n ~ rho  (CONSTANT in r).")
print("  Folded RS (s>1) is what buys tau(r) -> 0 as r grows (subspace-design property).")
print("  Plain RS has NO such decay: this is the structural gap the attack_plan admits.")

# ---- Q2: is the threshold ever non-vacuous below near-capacity, prize regime?
print("\n[Q2] Threshold  tau(r)*n + r*n < (r+1)*a  with tau(r)=rho, plain RS, prize window")
print("     a = agreement count = (1-delta)*n at window-interior delta.")
print()

for mu in [20, 24, 28, 30, 32]:
    n = 2**mu
    for rho in [1/2, 1/4, 1/8, 1/16]:
        k = round(rho*n)
        beta = 4.5
        # prize budget on bad scalars: q*eps* ~ n  (window interior). |F|=q=n^beta.
        q = n**beta
        budget = q * (2.0**-128)   # = n^beta * 2^-128 ; with beta~4.5 ~ n  (q*eps* ~ n)
        # window-interior delta (conjectured pin): 1 - rho - H(rho)/(beta log2 n)
        delta = (1-rho) - H2(rho)/(beta*math.log2(n))
        a = (1-delta)*n            # agreement coordinates required to be "close"
        tau_r = (k-1)/n            # ~ rho, constant in r
        # smallest r making threshold fire:  rho*n + r*n < (r+1)*a
        #   rho*n + r*n < (r+1)*a  <=>  rho*n - a < r*(a-n) + a - a ... solve:
        #   rho*n + r*n < r*a + a  <=> r*(n-a) < a - rho*n  <=> r > (a-rho*n)/(a-n) if a<n...
        # a-n is NEGATIVE (a<n since delta>0). Let's just scan r.
        fire_r = None
        for r in range(1, 60):
            lhs = tau_r*n + r*n
            rhs = (r+1)*a
            if lhs < rhs:
                fire_r = r
                break
        if fire_r is None:
            print(f"  mu={mu} rho={rho}: a={a:.3e} a/n={a/n:.4f}  tau={tau_r:.4f}  "
                  f"THRESHOLD NEVER FIRES (no r) -> bound VACUOUS")
        else:
            r = fire_r
            listcap = q**(r-1)          # |F|^{r-1}
            print(f"  mu={mu} rho={rho}: a/n={a/n:.4f} tau={tau_r:.4f} fires at r={r} "
                  f"=> |L|<=|F|^{r-1}=q^{r-1}={listcap:.2e}  vs budget {budget:.2e}  "
                  f"=> {'USABLE' if listcap<=budget else 'VACUOUS (>>budget)'}")

print()
print("-"*78)
print("KEY: the threshold tau(r)*n + r*n < (r+1)*a needs (r+1)*a > (rho+r)*n,")
print("i.e.  a/n > (rho+r)/(r+1).  As r->inf this -> 1 (need a/n->1 = full agreement =")
print("UNIQUE decoding / near-capacity). At the window interior a/n = 1-delta =")
print("rho + H(rho)/(beta log n) ~ rho + o(1), only slightly above rho.")
print()
print("So the threshold fires only for r with (rho+r)/(r+1) < a/n ~ rho+tiny,")
print("i.e. (rho+r)/(r+1) - rho = (r(1-rho))/(r+1) < tiny -> needs r SMALL... but at")
print("r=1: (rho+1)/2 vs a/n~rho: (rho+1)/2 > rho always (since rho<1). r=1 NEVER fires.")
print("Threshold is MONOTONE INCREASING toward 1 in r AND r=1 already exceeds a/n.")
print("=> NO r fires at the window interior for plain RS.  The reverse bound is VACUOUS.")
