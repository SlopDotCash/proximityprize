#!/usr/bin/env python3
"""
#407 [rojasleon] — PIN the exact gap between Rojas-Leon (2207.12439) and the prize sup-norm.

ROJAS-LEON Thm 4 (effective): for a FIXED number n of monomials with bounded exponents
maxj|a_ij|<=A, the joint normalized Gauss sums Phi_m(chi) on (S^1)^n equidistribute with
discrepancy (Weyl-sum of a single character c with ||c||=L1 norm):
    | (1/|S_m|) sum_{chi in S_m} Lambda_c(Phi_m(chi)) |
        <= [ C N^{||c||-1} A^{||c||} (q-1)^r q^{-1/2} + nA(q-1)^{r-1} ] / [ (q-1)^{r-1}(q-1-nA) ]
        ~  C N^{||c||-1} A^{||c||} q^{-1/2}    (leading term, r=1).
This is a q^{-1/2} (square-root) discrepancy for EACH FIXED test frequency c, with a constant
that BLOWS UP geometrically in ||c|| (the moment order) as N^{||c||}.

THE PRIZE needs: ||P||_inf = max_c |sum_{j=1}^{m-1} a_j e(-jc/m)| <= sqrt(2 m log m).
By Chernoff+union the sufficient input is the JOINT MGF over ALL L=m-1 phases:
    E[ exp( lambda Re(zeta-bar sum_j a_j w_j) ) ] <= exp( C m lambda^2 / 2 )   (sub-Gaussian, proxy m)
i.e. a moment bound  E[ |sum a_j w_j|^{2r} ] <= (C m)^r (2r-1)!!  up to r ~ log m.

THE GAP (three independent axes), quantified here:
 (G1) NUMBER of phases: RL controls n FIXED; prize needs L=m-1 ~ 2^128 GROWING with q.
 (G2) MOMENT DEPTH: RL's constant is N^{||c||} A^{||c||} -> to reach moment r~log m the
      discrepancy bound is C*N^r*q^{-1/2}; it beats trivial only while N^r < q^{1/2}, i.e.
      r < (log q)/(2 log N).  Pin (log q)/(2 log N) vs needed r~log m.
 (G3) FAMILY DIRECTION: RL equidistributes as q->infinity (over a TOWER of fields k_m);
      the prize is a SINGLE fixed field F_p.  No rate in q at a single p.
We compute (G2)'s crossover r_RL = (log q)/(2 log N) for the constant N (Forey-Fresan-Kowalski
absolute constant, geometric Betti-number bound; N>=2 always) and compare to r_need ~ log m,
showing r_RL is O(1)-to-O(log) but the constant N kills it well before r~log m at fixed p.
"""
import math

print("="*86)
print("Rojas-Leon (2207.12439) Thm 4 discrepancy  vs  prize sup-norm requirement: the gap")
print("="*86)
print("""
RL Thm4 (leading r=1):  |Weyl_c| <= C * N^{||c||-1} * A^{||c||} * q^{-1/2}   (per fixed freq c)
  - q^{-1/2} square-root discrepancy: GOOD, this is exactly Weil-strength.
  - BUT geometric blow-up N^{||c||} in the test-frequency L1-norm ||c|| (= the moment order).
Prize needs the JOINT control of the trig-poly sup-norm over ALL m-1 phases at the SINGLE field p,
which (MGF route) = moment E|sum a_j w_j|^{2r} sub-Gaussian up to r ~ log m.
""")
# G2: at what moment depth does RL's discrepancy stop being non-trivial, as a function of N?
# A single Weyl-sum estimate at frequency c with ||c||=r feeds an r-th moment.  RL gives
# discrepancy ~ C N^{r} q^{-1/2}; this is o(1) (real equidistribution at that c) iff N^r < q^{1/2},
# i.e. r < (log q)/(2 log N).  Needed r ~ log m ~ log q (prize: m ~ q).  So RL's reliable moment
# depth r_RL/(needed r) ~ 1/(2 log N) < 1 — a CONSTANT-FACTOR shortfall set by N.
print(f"{'log2 q':>8} {'log2 m':>8} {'r_need~ln m':>12} {'r_RL(N=2)':>10} {'r_RL(N=4)':>10} {'r_RL(N=8)':>10} {'r_RL/r_need(N=4)':>16}")
for log2q in [40, 80, 128, 160, 256]:
    lnq=log2q*math.log(2)
    # prize: m ~ q/n, n=2^mu small power; take m ~ q (index-fixed regime) and m ~ q^{4/5} (thin)
    log2m=log2q*1.0   # index-fixed/positive-proportion regime: m ~ q
    r_need=log2m*math.log(2)   # ~ ln m
    rows=[]
    for N in (2,4,8):
        r_RL=lnq/(2*math.log(N))   # crossover moment depth where N^r = q^{1/2}
        rows.append(r_RL)
    print(f"{log2q:8d} {log2m:8.0f} {r_need:12.1f} {rows[0]:10.1f} {rows[1]:10.1f} {rows[2]:10.1f} {rows[1]/r_need:16.3f}")
print("""
G2 reading: even with the SMALLEST possible RL/FFK constant N=2, the reliable moment depth
  r_RL = (ln q)/(2 ln N) = (ln q)/(2 ln 2) = 0.72 * log2 q,
while the prize needs r_need ~ ln m ~ ln q = 0.69*log2(q)*... actually ln m = log2(m)*ln2.
  ratio r_RL/r_need = 1/(2 ln N) -> for N=2: 1/(2*0.693)=0.72; N=4: 0.36; N=8: 0.24.
So RL with a real constant N>=2 reaches only a CONSTANT FRACTION (<=0.72) of the needed depth,
and crucially this is the per-FREQUENCY bound: the union over m-1 frequencies needs the constant
uniform, but RL's constant GROWS as N^{||c||} = N^r, so the union bound over m frequencies costs
another factor that RL's q^{-1/2} can absorb only while N^r < q^{1/2} (same crossover).
""")
# G1: the number-of-phases axis (the decisive one).
print("G1 (decisive): RL/Katz hold the NUMBER of Gauss sums n FIXED while q->infinity.")
print("  The prize couples ALL L=m-1 phases AT ONCE at a single q.  RL's Thm 1 hypothesis")
print("  ('the v_i are linearly independent') is a FIXED-n condition; for n=m-1~q it is")
print("  vacuous/unverifiable (you cannot have q-1 linearly independent v_i in a space whose")
print("  relevant dimension is controlled, and the HD/conjugation relations DO bind them).")
print("  => RL gives joint independence of any FIXED tuple of the a_j, NOT of the growing family.")
