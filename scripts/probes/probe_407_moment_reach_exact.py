#!/usr/bin/env python3
"""
#407 EXACT Markov-Krein extremal: the SHARP max support point of a symmetric mean-0 measure with
m atoms, variance 1, given 2R prescribed even moments, is governed by the Gauss-quadrature / 
Chebyshev-Markov theory. KEY THEOREM (Markov): given moments m_0..m_{2R} of a measure on R, the
largest possible value of the support's max equals the largest root of the (R+1)-th orthogonal
polynomial of the moment sequence (the principal representation). The SHARP upper bound on max-atom
given moments up to order 2R is the largest zero x_+ of the orthogonal polynomial P_{R+1}, with the
extremal measure putting an atom there of mass = (Christoffel) ~ 1/(sum K_R(x_+,x_+)). For our problem
the relevant SHARP statement is cleaner via the ONE-SIDED Markov inequality at the atom-mass level:
   max atom t_+ : the measure can place mass as small as the SMALLEST Christoffel weight at t_+, and the
   constraint is that mass >= 1/m for an actual atom. 

We just confirm the SCALING law that decides the route, exactly: with EXACTLY the Gaussian even-moment
sequence to order 2R (mu_{2r}=(2r-1)!!), the best moment-method atom bound is min_r (m (2r-1)!!)^{1/2r}/.
The Markov SHARP bound can only be <= this and >= the true max. We compute, for each R = #PROVEN moments,
the achievable bound, to show: bound ~ sqrt(2 ln m) requires R ~ ln m; with R=O(1) bound ~ m^{c/R}.
"""
import math

def moment_opt_bound(m, Rmax):
    """min over r<=Rmax of (m*(2r-1)!!)^{1/2r}, in units of sigma=sqrt(var). returns (rbest, bound)."""
    def ldf(r): return math.lgamma(2*r+1) - r*math.log(2) - math.lgamma(r+1)
    best=None
    for r in range(1,Rmax+1):
        v=(math.log(m)+ldf(r))/(2*r)
        if best is None or v<best[1]: best=(r,v)
    return best[0], math.exp(best[1])

print("="*90)
print(" #407 Markov reach: best max|eta|/sqrt(n) bound from R PROVEN char-0 even moments")
print("="*90)
print(f"\n{'R(#moments)':>12} | bound for log2(m)= 20, 30, 40, 50, 60 (each = max|eta|/sqrt(n))")
print("-"*90)
for R in (1,2,3,5,8,13,21,34):
    row=[]
    for log2m in (20,30,40,50,60):
        m=2**log2m
        _,b=moment_opt_bound(m,R)
        row.append(f"{b:8.2f}")
    print(f"{R:>12} | " + "  ".join(row))
print("-"*90)
print("target sqrt(2 ln m):  " + "  ".join(f"{math.sqrt(2*log2m*math.log(2)):8.2f}" for log2m in (20,30,40,50,60)))
print()
print("READ: the optimal moment depth r* GROWS like ln m (~14,21,28,35,42). With only R=O(1) proven")
print("char-0 moments (p-defect caps R at ~3 in regime), bound is FROZEN at the R-th row = m^{1/2R}-scale,")
print("i.e. polynomial in m, NEVER sqrt(2 ln m). EACH proven moment buys a fixed multiplicative cut but")
print("you need ~ln m of them. THIS is the route's information-theoretic wall, made exact.")
print()
print("How many proven moments R(log2 m) would be NEEDED to reach within 2x of target:")
for log2m in (20,30,40,50,60):
    m=2**log2m; tgt=math.sqrt(2*log2m*math.log(2))
    Rneed=None
    for R in range(1,200):
        _,b=moment_opt_bound(m,R)
        if b<=2*tgt: Rneed=R; break
    print(f"  log2 m={log2m:3d}: need R>={Rneed}  (p-defect onset r* ~ 3  => SHORT by {Rneed-3} moments)")
