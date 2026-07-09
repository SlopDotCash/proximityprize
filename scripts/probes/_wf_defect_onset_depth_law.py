#!/usr/bin/env python3
"""
#407 cumulant-from-flatness FINAL: the defect-onset prime at depth r, p ~ n^{c_r}.

ESTABLISHED (this session):
 - kappa_r = (p/nm)^r W_r/(2r-1)!!, W_r = closed r-walk sum of autocorr R(h)=conj(tau_h)T_h/p.
 - r=2 defect onset at p ~ n^3 (largest bad m ~ n^2; once p>>n^3, N=2n-3 forced = kappa_2<=1).
 - PRIZE p ~ n*2^128 >> n^3 always => kappa_2<=1 UNCONDITIONALLY at prize.

THE WALL (what we now pin): at depth r the cumulant kappa_r picks up the r-FOLD unit-equation
count = #{ short (<=2r-term) +-1 relations of 2^a-th roots that vanish mod p }. In char 0 these
are ONLY the forced (matching) ones => kappa_r->1. A mod-p-only relation needs p | (nonzero
algebraic integer of house <=2r over Z[zeta_{2^a}]); the SMALLEST nonzero such has norm ~ (2r)^{n/2}
(its house >= sqrt2 dyadic floor; product over n/2 conjugates). So the depth-r defect onset is
   p ~ (2r)^{n/2}   <=>   r ~ (1/2) p^{2/n}   <=>   provable depth r_max(p) ~ p^{2/n}.
PRIZE: p ~ n m, log p ~ log n + 128 ln2. r_max ~ exp((2/n) ln p) ~ 1 + (2/n) ln p (since 2/n tiny).
   At n=2^30: (2/n) ln p ~ 2^-29 * 89 ~ 1.7e-7  => r_max ~ 1 + 1.7e-7  => ONLY r<=1,2 provable!
   NEEDED depth r* ~ ln m ~ 128 ln2 ~ 89. GAP: provable r_max ~ O(1), needed r* ~ ln m. WALL.

This probe MEASURES c_r = log_n(defect-onset p) at small n to confirm c_r ~ (n/2) log_n(2r) i.e.
the onset prime grows like (2r)^{n/2}, hence r_max(p)=onset-inverse ~ (1/2) p^{2/n}. We find, for
each r, the LARGEST m at which some prime still has kappa_r>1 (a real defect), vs n.
"""
import cmath, math
import sympy

def primitive_root(p): return int(sympy.primitive_root(p))

def kappa_r(p,n,r):
    m=(p-1)//n
    g=primitive_root(p)
    mu=[pow(g,(m*t)%(p-1),p) for t in range(n)]
    def psi(x): return cmath.exp(2j*math.pi*(x%p)/p)
    seen=set();reps=[];b=1
    while len(reps)<m and b<p:
        if b not in seen:
            reps.append(b)
            for x in mu: seen.add(b*x%p)
        b+=1
    etas=[abs(sum(psi(b*w%p) for w in mu)) for b in reps]
    df=1
    for i in range(1,r+1): df*=(2*i-1)
    return (sum(e**(2*r) for e in etas)/m)/(df*n**r)

def find_primes(n,cap,start=2):
    out=[];k=start
    while True:
        p=k*n+1
        if p>cap: break
        if sympy.isprime(p): out.append(p)
        k+=1
    return out

if __name__=="__main__":
    print("#407: defect-onset prime at depth r ~ (2r)^{n/2}; provable depth r_max ~ (1/2) p^{2/n}\n")
    print("For each (n,r): largest m with a prime having kappa_r>1 (real depth-r defect).")
    print(f"{'n':>3}{'r':>3} | {'max_bad_m':>9} {'onset_p~':>9} {'c_r=log_n(p)':>12} {'(2r)^(n/2)':>12}")
    for n in [4,8,16]:
        cap = min(20000, 60*n*n)
        primes=find_primes(n,cap)
        for r in [2,3,4]:
            max_bad_m=0; onset_p=0
            for p in primes:
                k=kappa_r(p,n,r)
                m=(p-1)//n
                if k>1.0 and m>max_bad_m:
                    max_bad_m=m; onset_p=p
            if max_bad_m>0:
                cr=math.log(onset_p)/math.log(n)
                pred=(2*r)**(n/2)
                print(f"{n:>3}{r:>3} | {max_bad_m:>9} {onset_p:>9} {cr:>12.2f} {pred:>12.2e}")
            else:
                print(f"{n:>3}{r:>3} | {'(none)':>9} {'-':>9} {'-':>12} {(2*r)**(n/2):>12.2e}")
    print("\nc_r = log_n(onset prime). If c_r grows with r (toward (n/2)log_n(2r)), the DEPTH r")
    print("provable is capped: r_max(p) ~ (1/2)p^{2/n}, which at prize (p~n*2^128, n>=2^16) is O(1),")
    print("while the needed depth is r*~ln m ~ 89. THE WALL, derived from the unit-equation/norm side.")
