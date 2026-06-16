#!/usr/bin/env python3
"""
C037 decisive sub-test: at what RATE does the KKH26 march pin delta* above Johnson?

The march pins delta*=1-r/n EXACTLY for the dimension-(r-1) code, but only inside the
band [C(n,r)/r , 2^r*C(n/2,r)] / p AND (canonical pin) requires r^2 <= 2^mu+1, i.e.
r <~ sqrt(n).  Dimension k=r-1 <~ sqrt(n) => rate rho=(r-1)/n -> 0.

PRIZE needs FIXED rate rho in {1/2,1/4,1/8,1/16}, i.e. k=rho*n=Theta(n), r=Theta(n).
At r=Theta(n) the canonical band condition r^2<=2^mu+1 FAILS, and the march cap
C(n,r)/r is astronomically larger than the prize budget q*eps* (~ n at q~n*2^128).
"""
import math
from math import comb

print("="*78)
print("C037: does the march reach PRIZE rate? (canonical band needs r^2<=2^mu+1)")
print("="*78)
for mu in [5,6,8,10,20,30]:
    n = 2**mu
    # canonical band requires r*r <= n+1  => r <= sqrt(n)
    rmax_canon = int(math.isqrt(n+1))
    rho_max_canon = (rmax_canon-1)/n
    # general pin (non-canonical) requires r <= 2^(mu-1) = n/2 and a prime
    #   p > (2^mu)^(2^(mu-1)) -- ASTRONOMIC, p ~ n^(n/2). Prize is p~n^4..5.
    # at prize rate rho=1/4: r=rho*n+1
    print(f"\n n=2^{mu}={n}")
    print(f"  canonical march reach: r<=sqrt(n)={rmax_canon}, max dim k={rmax_canon-1},"
          f" max rho={rho_max_canon:.5f}  (-> 0 as n grows)")
    for rho in [0.5,0.25,0.125,0.0625]:
        r = round(rho*n)+1
        if r<2 or r>n: continue
        # prime needed for the general (non-canonical) pin:
        # hp : (2^mu)^(2^(mu-1)) < p   -> p > n^(n/2)
        log2_p_needed = mu * (2**(mu-1)) if mu<=6 else float('inf')
        prize_log2_q = mu*4.5  # q ~ n^4.5 in prize
        cap = comb(n,r)//r if n<=64 else None
        capstr = f"{cap}" if cap is not None else "huge"
        print(f"   prize rho={rho}: r={r}, march needs prime with log2(p)>~{log2_p_needed if mu<=6 else 'inf (n^(n/2))'}"
              f"  vs prize log2(q)~{prize_log2_q:.0f}; band-floor C(n,r)/r={capstr}")

print("\n"+"="*78)
print("VERDICT LOGIC")
print("="*78)
print("""
1. The connection's STRUCTURAL reframing is CORRECT and insightful:
   - ladder pins delta* on the LOW region (delta <~ (n-k)/(3n) < Johnson), count linear ~e
   - march pins delta* on a HIGH region (delta=1-r/n > Johnson), count C(n,r)/r super-poly
   - for a FIXED code there IS an unmapped gap (knee) between them = the open core.
   This is a valid GEOMETRIC localization of sup{delta:I(delta)<=n}.

2. BUT the claim that they are 'the SAME I(delta) curve' FAILS at the prize rate:
   (a) The ladder and the march pin DIFFERENT codes at the same radius. The march
       above-Johnson pin (canonical, machine-proven) needs r^2 <= 2^mu+1, i.e.
       r <= sqrt(n), so dimension k=r-1 <= sqrt(n)-1 and rate rho -> 0. It is a
       VANISHING-RATE pin (Diamond-Gruen regime), NOT a fixed prize rate.
   (b) The non-canonical march pin (r=Theta(n), prize rate) requires a prime
       p > n^(n/2) -- astronomically larger than the prize q~n^4..5. Vacuous at prize.
   (c) So at FIXED prize rate, the march gives NO above-Johnson pin: the high end of
       'I(delta)' the connection wants does not exist as a proven curve at prize rate.

3. The 'knee' is therefore NOT a newly-localized object: it is exactly the same open
   core (BGK/Paley sqrt-cancellation for thin mu_n) restated geometrically. The
   march's super-poly count C(n,r)/r is an INCIDENCE upper bound on bad scalars, not a
   character-sum cancellation result; it controls delta* only for vanishing rate.

=> C037 is a correct, insightful REFRAMING that REDUCES nothing new: the 'knee' welds
   back to the W-Johnson wall / BGK. Honest label: OPEN (welds to W-Johnson), with the
   structural unification PARTIAL-true (true as geometry, false as 'one curve at prize
   rate').
""")
