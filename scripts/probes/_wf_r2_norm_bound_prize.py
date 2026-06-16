#!/usr/bin/env python3
"""
#407: is kappa_2<=1 PROVABLE AT THE PRIZE via the r=2 unit-equation norm bound?

kappa_2<=1 <=> N = #{(w,w') in mu_n^2, w,w'!=1 : (1-w)/(1-w') in mu_n} = forced floor 2n-3
            <=> the unit equation  (1-w) = u (1-w'),  u,w,w' in mu_{2^a},  w,w'!=1
            has ONLY the forced solutions (u=1 diagonal; u=-w^{-1} involution; w=-1 boundary).
An EXTRA solution = a nontrivial identity  (1-w) - u(1-w') = 0  in F_p among 2^a-th roots
that does NOT hold in char 0. Equivalently p divides the nonzero algebraic integer
   alpha = (1 - zeta) - u(1 - zeta')   in  Z[zeta_{2^a}],   zeta,zeta',u  2^a-th roots, NOT a forced sol.
If alpha != 0 in char 0 (it is, for non-forced (u,zeta,zeta')), then p | alpha forces
   p <= N(alpha) = prod over the phi(2^a)=2^{a-1}... wait alpha lives in Z[zeta_{2^a}], degree 2^{a-1}.
   |N(alpha)| = prod_{sigma} |sigma(alpha)|.  Each |sigma(alpha)| <= |1-zeta^?|+|u||1-zeta'^?| <= 2+2=4.
   So |N(alpha)| <= 4^{2^{a-1}} = 4^{n/2} = 2^n.   And |N(alpha)|>=1 (nonzero integer).
   => extra solution possible only if p <= 2^n  (a prime dividing alpha is <= |N(alpha)| <= 2^n).
THE PRIZE: n=2^a (a up to 40), p ~ n*2^128 = 2^{a+128}. Compare to the norm bound 2^n=2^{2^a}.
   a=7 (n=128): 2^n=2^128, p~2^135. p>2^n? 2^135 > 2^128 YES -> norm bound TOO WEAK (p can divide alpha).
   a=8 (n=256): 2^n=2^256, p~2^136. p < 2^256 -> norm bound USELESS (p << 2^n, easily divides).
   GENERAL: norm bound gives 'no defect' only when p > 2^n, i.e. 2^{a+128} > 2^{2^a}, i.e. a+128 > 2^a.
            a+128>2^a  holds for a<=7 (2^7=128, 7+128=135>128 OK) ; a=8: 2^8=256>136 FAILS.
   => the r=2 norm bound PROVES kappa_2<=1 ONLY for n<=128 (a<=7) at prize. FAILS n>=256.

So this probe CONFIRMS the norm-bound crossover a*=7 (n=128) and shows the SHARP norm of the
minimal non-forced alpha (is it really ~4^{n/2}, or much smaller = LamLeung dyadic house sqrt2?).
The LamLeung/dyadic refinement: |sigma(alpha)| is NOT generically 4; for a balanced sparse sum the
house can be as low as sqrt2, giving N(alpha) ~ (sqrt2)^{n/2}*... -> a SMALLER norm bound => WORSE.
We compute the actual minimal nonzero |N((1-zeta)-u(1-zeta'))| over small 2^a to fit the true exponent.
"""
import math, itertools
import sympy
from sympy import Rational, exp, I, pi, simplify, nsimplify, Poly, cyclotomic_poly, resultant, symbols

def minimal_norm_exact(a, sample_cap=None):
    """Smallest |N(alpha)| over non-forced alpha=(1-z)-u(1-z'), z,z',u in mu_{2^a}\\{forced}.
    Uses algebraic norm via product of conjugates numerically (high precision) then rounds."""
    import cmath
    n=2**a
    roots=[cmath.exp(2j*math.pi*t/n) for t in range(n)]
    # Galois group of Q(zeta_n)/Q for n=2^a: sigma_k: zeta->zeta^k, k odd, 1<=k<n.
    units=[k for k in range(1,n) if k%2==1]   # (Z/n)^*  has order n/2
    best=None;bestwit=None
    # iterate non-forced (i=exp of z, j=exp of z', l=exp of u); forced: u=1 (l=0) & z=z'(i=j);
    # involution: z'=z^{-1}, u=-z^{-1}; boundary z=1 or z'=1 (i=0 or j=0).
    cnt=0
    for i in range(1,n):       # z=zeta^i, i!=0 (z!=1)
        for j in range(1,n):   # z'=zeta^j, j!=0
            for l in range(0,n):  # u=zeta^l
                # forced filters:
                if l==0 and i==j: continue            # u=1, z=z' diagonal
                # involution: z'=z^{-1} => j=(-i)%n ; u=-z^{-1}=zeta^{n/2 -i} => l=(n//2 - i)%n
                if j==(-i)%n and l==(n//2 - i)%n: continue
                cnt+=1
                if sample_cap and cnt>sample_cap:
                    return best,bestwit,cnt
                # alpha = (1 - zeta^i) - zeta^l (1 - zeta^j)
                prod=1.0
                for k in units:
                    z=cmath.exp(2j*math.pi*(i*k%n)/n)
                    zp=cmath.exp(2j*math.pi*(j*k%n)/n)
                    u=cmath.exp(2j*math.pi*(l*k%n)/n)
                    val=(1-z)-u*(1-zp)
                    prod*=abs(val)
                if prod<1e-9: continue   # alpha=0 in char 0 (a hidden forced relation) skip
                Nrm=prod   # |N(alpha)| = prod |sigma alpha| (real, since complex conj is a Galois elt)
                if best is None or Nrm<best:
                    best=Nrm;bestwit=(i,j,l)
    return best,bestwit,cnt

if __name__=="__main__":
    print("#407: minimal non-forced norm |N((1-z)-u(1-z'))| over mu_{2^a}; fit exponent c: N~2^{c*n}")
    print("Norm bound: extra r=2 defect mod p possible only if p <= min|N(alpha)|.\n")
    print(f"{'a':>2}{'n':>5} | {'min|N|':>12} {'log2|N|':>8} {'log2|N|/n':>10} {'witness(i,j,l)':>16}")
    for a in [2,3,4,5]:
        n=2**a
        cap = 200000 if a<=4 else 400000
        best,wit,cnt=minimal_norm_exact(a, sample_cap=cap)
        if best:
            l2=math.log2(best)
            print(f"{a:>2}{n:>5} | {best:>12.2f} {l2:>8.2f} {l2/n:>10.4f} {str(wit):>16}  (scanned {cnt})")
        else:
            print(f"{a:>2}{n:>5} | (none<cap)")
    print("\nIf log2|N|/n -> c>0 const, min norm ~ 2^{c n}; r=2 defect needs p<=2^{c n}.")
    print("Prize p~2^{a+128}; crossover a+128 = c*2^a. With c=2 (norm<=4^{n/2}): a*~7 (n=128).")
    print("Smaller c (dyadic house refinement, balanced sums) => SMALLER crossover a* => WORSE for prize.")
