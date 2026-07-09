#!/usr/bin/env python3
"""
C030 attack: "delta* gap = entropy-rate of the census numerator".

The connection asserts a CHAIN:
  (1) PROVEN in-tree (kkh26_gap_identity / kkh26_gap_bracket):
      ceiling sits EXACTLY gap = (2m-1)/n below capacity, and (2m-1)/n = Theta(1/2^mu).
  (2) PROVEN in-tree (KKH26EntropyForm.choose_ge_two_rpow_entropy_div):
      census numerator C(s, r) >= 2^{s*H2(r/s)} / (s+1), i.e. log2 I_inf ~ s*H2(rho).
  (3) THE NEW CLAIM (the connection's substance):
      "pin fires (F1) when I_inf = q*eps* ~ n, i.e. s*H2(rho) ~ log2 n + gap*(beta log2 n);
       solving gives  gap = H(rho)/(beta log n)."

We test whether the PROVEN gap (2m-1)/n equals the CLAIMED gap H(rho)/(beta log2 n),
in the PRIZE regime: dyadic mu_n, s = 2^mu the PROPER subgroup, q ~ n^beta, beta in [4,5].

CRITICAL regime discipline (from MEMORY / the #400 trap):
  - the dyadic subgroup has order  s = 2^mu  (the BGK object)
  - the evaluation domain length is n = 2^mu * m
  - q prime ~ n^beta is the field size; "log n" in the headline must be pinned.

We compare three readings of the headline gap H(rho)/(beta log2 n) against the proven (2m-1)/n.
"""
import math
from math import comb, log2

def H2(p):
    if p <= 0 or p >= 1:
        return 0.0
    return -p*log2(p) - (1-p)*log2(1-p)

print("="*100)
print("C030: proven gap (2m-1)/n  vs  claimed gap H(rho)/(beta log2 n)")
print("="*100)

# KKH26 family parametrization (from KKH26AsymptoticCeiling.lean):
#   n = 2^mu * m ; degree d=(r-2)*m ; dim = d+1 ; rate rho = ((r-2)m+1)/n
#   ceiling delta* <= 1 - r/2^mu ; capacity 1-rho ; gap = (2m-1)/n
# census numerator (the bad-scalar count) = 2^r * C(2^{mu-1}, r)  [kkh26_witness_count_ge]
#   so the entropy object is s' = 2^{mu-1}, with log2(count) ~ r + s'*H2(r/s')
# In the headline "rho" = code rate; "n" is the LENGTH; beta from q ~ n^beta.

# Prize regime sweep: choose mu so s=2^mu is a *proper* subgroup, q~n^beta large prime.
rows = []
for mu in [3, 4, 5, 6]:        # s = 8,16,32,64  (toy proper subgroups)
    s = 2**mu
    for m in [1, 2, 4, 8]:      # n = s*m
        n = s*m
        # pick r near the rate; use r ~ rho*s style. For the ceiling, r in [2, 2^{mu-1}].
        for r in range(2, max(3, 2**(mu-1)+1)):
            if r >= 2**(mu-1)+1:
                continue
            rho = ((r-2)*m + 1)/n
            if not (0 < rho < 1):
                continue
            proven_gap = (2*m - 1)/n                     # EXACT proven in-tree gap
            # census-numerator entropy rate (per kkh26_witness_count_ge): half-domain s' = 2^{mu-1}
            sp = 2**(mu-1)
            if not (0 < r < sp):
                continue
            log2_count = r + sp*H2(r/sp)                 # log2 I_inf (ignoring poly loss s'+1)
            # claimed headline gap: H(rho)/(beta log2 n), beta in [4,5]
            for beta in [4.0, 5.0]:
                claimed_gap = H2(rho)/(beta*log2(n)) if n > 1 else float('nan')
                ratio = claimed_gap/proven_gap if proven_gap>0 else float('nan')
                rows.append((mu,m,n,r,round(rho,4),round(proven_gap,5),
                             round(log2_count,3),beta,round(claimed_gap,5),round(ratio,3)))

print(f"{'mu':>3}{'m':>3}{'n':>5}{'r':>3}{'rho':>8}{'proven_gap':>12}"
      f"{'log2I':>9}{'beta':>5}{'claimGap':>10}{'claim/proven':>13}")
for row in rows:
    mu,m,n,r,rho,pg,lc,beta,cg,ratio = row
    print(f"{mu:>3}{m:>3}{n:>5}{r:>3}{rho:>8}{pg:>12}{lc:>9}{beta:>5.1f}{cg:>10}{ratio:>13}")

print()
print("="*100)
print("KEY QUESTION 1: is proven gap (2m-1)/n  ==  H(rho)/(beta log2 n) ?")
print("="*100)
# proven gap = (2m-1)/n ~ 2/(2^mu) = 2/s  (independent of beta, independent of H(rho)!)
# claimed gap = H(rho)/(beta log2 n).  These have DIFFERENT dependence on parameters.
# Check: proven gap scales as 1/s = 1/2^mu (subgroup size).
#        claimed gap scales as 1/log2 n = 1/(mu + log2 m) (LOG of length).
# For dyadic n=2^mu*m with m=1: log2 n = mu, so claimed ~ H(rho)/(beta*mu),
#   proven ~ 2/2^mu.  2/2^mu  vs  H/(beta mu): EXPONENTIALLY different in mu.
print("proven gap (m=1) = (2*1-1)/2^mu = 1/2^mu  (EXPONENTIALLY small in mu)")
print("claimed gap (m=1)= H(rho)/(beta*mu)        (only POLYNOMIALLY small in mu)")
for mu in [3,5,10,20,30]:
    s=2**mu; n=s
    pg=1/s
    rho=0.25
    cg=H2(rho)/(5.0*log2(n))
    print(f"  mu={mu:>3} s=2^mu={s:>12}  proven={pg:.3e}  claimed(rho=.25,beta=5)={cg:.3e}  "
          f"ratio claim/proven = {cg/pg:.3e}")
print()
print("VERDICT SIGNAL: the two 'gaps' scale DIFFERENTLY in mu.")
print("  proven (2m-1)/n = Theta(1/2^mu)  [subgroup-SIZE small]")
print("  claimed H(rho)/(beta log n) = Theta(1/mu) at m=1  [LOG-of-length small]")
print("  At prize mu=30 they differ by a factor ~2^30/mu ~ 3.6e7.")
print("  => the proven ceiling is MUCH closer to capacity than the headline 1/log n,")
print("     UNLESS m is taken EXPONENTIALLY large so that 1/2^mu ~ 1/log n, i.e.")
print("     n = 2^mu * m with m ~ 2^mu/(mu) so log2 n ~ 2mu and (2m-1)/n ~ 1/2^mu... still 1/2^mu.")
print()
print("Reconciliation (KKH26AsymptoticCeiling 'kkh26_gap_ge_of_mu_le_log'):")
print("  the 1/log n phrasing requires the SEPARATE regime hypothesis  2^mu <= C*log2 n,")
print("  i.e. the SUBGROUP is only LOGARITHMIC in the length. That is the OPPOSITE of the")
print("  prize regime (thin proper subgroup s=2^mu with q~n^beta and s a real subgroup,")
print("  s can be 2^30 while log2 n ~ small). The entropy-rate identity is REAL but the")
print("  'gap = H(rho)/(beta log n)' step holds ONLY in the 2^mu <= C log n regime, NOT")
print("  the prize regime where 2^mu is the thin BGK subgroup.")
