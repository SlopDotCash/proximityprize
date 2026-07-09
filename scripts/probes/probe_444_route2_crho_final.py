#!/usr/bin/env python3
"""
probe_444_route2_crho_final.py  (#444 Route 2 — the FULL crossover derivation of c(rho))

We now derive c(rho) end-to-end from the in-tree KKH26 crossover (KKH26WitnessSpread +
KKH26AsymptoticCeiling), being scrupulous about every quantity.

SETUP (prize regime, in-tree):
  n = 2^mu * m  (smooth domain, n the code length, m=(p-1)/n the index)
  Code = evalCode of degree (r-2)m, dimension (r-2)m+1, rate rho = ((r-2)m+1)/n.
  Ceiling radius: delta = 1 - r/2^mu.       Capacity: 1 - rho.
  Gap below capacity: eta := (1-rho) - delta = (2m-1)/n  (kkh26_gap_identity, EXACT).
  Bad-scalar count at this radius:  N = 2^r * C(2^{mu-1}, r)   (kkh26_epsMCA_lower_bound).
  The crossover (delta* pinned): N must EXCEED the budget  eps* * |F| = eps* * p.

The PRIZE budget:  eps* = 2^{-128},  p ~ n * 2^128,  so eps* * p ~ n.   Budget B = n.

So delta* is pinned at the LARGEST r (smallest eta) for which the count still beats the
budget:  2^r * C(2^{mu-1}, r)  >=  n  ... but ALSO the prime-existence constraint
p > (2^mu)^{2^{mu-1}} OR the Thorner-Zaman polynomial-field regime  2^mu <= C log2 n.

** THE crossover that sets c(rho): the field-size constraint, NOT the count magnitude. **

KKH26's own analysis (Appendix A, ledger c=H2(rho)) does NOT use "N >= budget" (the count is
2^{Theta(n)}, astronomically above n -- so the count NEVER binds). What binds is:

   For the bad line to EXIST over a field of size p ~ n*2^128, the resultant non-vanishing
   needs the prime large vs the collision resultant, OR (TZ route) the smooth modulus n must
   satisfy  n = 2^mu  with  2^mu = Theta(log p) = Theta(log n + 128) = Theta(mu + 128).
   At fixed prize budget 128, mu ~ log2(n), giving 2^mu ~ n ... that's circular for the
   constant. The HONEST extraction is from the gap identity + the dimension/rate bookkeeping.

We instead pin c(rho) by the DIMENSION-COUNTING crossover (the per-window list at budget):

   r = (rho + eta) * n     [radius delta = 1 - r/n in length units; with m=1, 2^mu=n]
   The worst-window list is the marginal count of NEW codewords at radius delta vs delta+1/n,
   = the dyadic lower bound restricted to the window. Its log2 per the entropy form is the
   SECOND-order (window-localized) term. KKH26 Appendix-A pull H2(rho) out of  C(n/2, r) at
   r = rho * (n/2) ... let's compute which evaluation of H2 yields the ledger c=H2(rho).
"""
import math
from math import comb, log2

def H2(p):
    if p<=0 or p>=1: return 0.0
    return -p*log2(p)-(1-p)*log2(1-p)

print("="*80)
print("THE H2(rho) EXTRACTION: which argument of H2 gives the ledger constant?")
print("="*80)
print("""
KKH26 Thm 1 / Appendix-A: code length n=2^mu (taking m=1, the cleanest case), rate rho,
dimension k = rho*n. The bad word's window list at radius capacity-eta uses r-subsets of the
HALF domain 2^{mu-1}=n/2 with r chosen so the agreement reaches s=(rho+eta)n. The count
2^r C(n/2,r) is maximized / the relevant r at the capacity EDGE is r ~ rho*n (NOT eta*n):
the deep-hole word forces r = k = rho*n coordinates of freedom (degree k). Then:

   log2 [2^r C(n/2,r)] / n   at r=rho*n
      = rho + (1/2) H2( (rho*n)/(n/2) ) = rho + (1/2) H2(2 rho) = Phi(rho).

That is Phi(rho), NOT H2(rho). For the ledger's H2(rho) we need r/(n/2)=rho i.e. r=rho*n/2,
or the count read on the FULL domain C(n, rho*n):
   log2 C(n, rho*n)/n = H2(rho).
""")
print(f"{'rho':>8} {'Phi(rho)=rho+H2(2rho)/2':>24} {'H2(rho)=log2 C(n,rho n)/n':>26}")
for rho in [0.5,0.25,0.125,0.0625]:
    phi = rho + 0.5*H2(2*rho) if 2*rho<1 else float('nan')
    print(f"{rho:8.4f} {phi:24.5f} {H2(rho):26.5f}")

print("""
=> TWO defensible closed constants depending on which combinatorial object is "the list":
   (i)  c(rho) = H2(rho)        [list = # agreement PATTERNS = subsets of FULL domain mu_n
                                  of size k=rho*n  ->  C(n, k) = 2^{n H2(rho)} per UNIT n,
                                  i.e. log over the WHOLE window scaled by 1/eta gives H2(rho).]
        This is the KKH26 Appendix-A / ledger reading. delta*=(1-rho)-H2(rho)/log2 n.
   (ii) c(rho) = Phi(rho) = rho + (1/2)H2(2 rho) = -rho log2 rho - (1/2)(1-2rho)log2(1-2rho)
        [list = the DYADIC sign-free count 2^r C(n/2,r) at r=rho n, the in-tree
        KKH26WitnessSpread surface]. delta*=(1-rho)-Phi(rho)/log2 n.

These AGREE at rho=1/2 boundary? Phi(1/2) undefined (2rho=1). H2(1/2)=1. Near rho=1/2,
Phi-> 1/2 + (1/2)H2(2rho)->1/2. So they DIFFER. At rho=1/4: 0.750 vs 0.811.
""")

print("="*80)
print("DECISION: the governing law in the prompt + symmetric-tower file says the worst-case")
print("WINDOW list is L*(delta)=2^{c/eta} and crosses budget eps*|F|=n.  The window-localized")
print("object is the # of agreement PATTERNS through one window. Per docs/kb (memory")
print("arklib-389-energy-unification, delta* = 1 - rho*N_fib(n,r)/N_fib(n,r-1)) and the KKH26")
print("ledger, the per-window pattern count's exponential rate is H2(rho).  => c(rho)=H2(rho).")
print("="*80)

print("\nFINAL CLOSED-FORM CONJECTURE (Route 2):")
print("   delta*(rho, n) = (1 - rho) - H2(rho)/log2(n),   H2(rho)=-rho log2 rho-(1-rho)log2(1-rho)")
print()
print(f"{'rho':>8} {'1-rho':>8} {'H2(rho)':>10} {'delta* @ n=2^256':>18} {'delta* @ n=2^30':>16}")
for rho in [0.5,0.25,0.125,0.0625]:
    cap=1-rho; c=H2(rho)
    d256=cap - c/256; d30=cap - c/30
    print(f"{rho:8.4f} {cap:8.4f} {c:10.5f} {d256:18.6f} {d30:16.6f}")

print("\nSanity vs window interior (1-sqrt rho, 1-rho):")
print(f"{'rho':>8} {'1-sqrt(rho)':>12} {'delta*@2^256':>14} {'1-rho':>8} {'in interior?':>14}")
for rho in [0.5,0.25,0.125,0.0625]:
    lo=1-math.sqrt(rho); cap=1-rho; d=cap-H2(rho)/256
    inint = lo < d < cap
    print(f"{rho:8.4f} {lo:12.5f} {d:14.6f} {cap:8.4f} {str(inint):>14}")
