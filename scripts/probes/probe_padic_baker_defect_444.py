import math
log2 = math.log(2)

# Everything in log2-scale to avoid overflow. The ONLY question that matters:
# Does the p-adic Baker/Yu bound BEAT the archimedean (2r)^{n/2} norm wall,
# or hit the SAME height obstruction?
#
# The defect count we want to cap: D_r = #{ b mod p : eta_b has a deep coincidence }
# The honest reduction of the p-adic lens:
#   if a sparse  f (<=2r terms, +-1 coeffs)  has  f(omega) = 0  in F_p
#   then  v_p(F(omega)) >= 1  where F is the integer lift,  and  |N(F(omega))| = p^{v_p} * (unit part).
#   The CRUCIAL chain:   1 <= v_p( N )  <=  log_p |N|  <=  log_p ( (2r)^{n/2} ) = (n/2) log_p(2r).
# So the p-adic valuation is ALSO bounded by the archimedean height divided by log p.
# This is the same height H = (n/2) log(2r) showing up -- p-adic v_p just divides it by log p.
#
# Baker/Yu would give an INDEPENDENT upper bound on v_p of a NONZERO linear form, of shape
#   v_p(Lambda) <= C(s,d) * (p/log p) * prod(log A_i) * log B
# The defect onset is when this Yu bound is < 1 is IMPOSSIBLE (it's huge); the useful direction
# is: number of FORCED coincidences = (height budget)/(per-coincidence valuation cost).
#
# Compare in log2 scale at prize params n=2^30:
mu = 30; n = 2**mu
for beta in [4,5]:
    logp2 = beta*mu          # log2 p
    print(f"\n== beta={beta}, log2 p = {logp2} ==")
    for r in [4,8,64,128]:
        s = 2*r
        # archimedean wall:  log2 |N| <= (n/2) * log2(2r)
        arch_log2 = (n/2)*math.log2(2*r)
        # p-adic valuation upper bound from archimedean:  v_p <= log_p|N| = arch_log2 / logp2
        vp_from_arch = arch_log2 / logp2
        # Yu combinatorial constant log2:  ~ 2s*log2(s)  (the s^{2s} factor) + (p/log p) term
        yu_const_log2 = 2*s*math.log2(s) if s>1 else 0
        yu_p_term_log2 = logp2 - math.log2(logp2*log2)  # log2( p/log p )
        yu_logB_log2 = math.log2(max(mu,1))             # log2 log2 B with B=n -> log2(mu)
        yu_bound_log2 = yu_const_log2 + yu_p_term_log2 + yu_logB_log2
        # The norm-wall depth threshold from MomentMethodPrizeDepthNoGo: (2r)^{n/2} < p  <=>  r <= 2 beta
        rmax = 2*beta
        clean = "CLEAN(transfers)" if r<=rmax else "WALL(>(2r)^{n/2}>=p)"
        print(f"  r={r:4d}: vp_from_arch~2^{vp_from_arch:8.2e}  yu_upper_log2={yu_bound_log2:8.1f}  rmax={rmax} -> {clean}")

print("\nKEY: the p-adic v_p is bounded by arch_height/log p -- SAME (n/2)log(2r) numerator.")
print("Yu's own bound carries the p/log p factor (POLYNOMIAL in p, ~2^{beta*mu}) -- itself > house.")
