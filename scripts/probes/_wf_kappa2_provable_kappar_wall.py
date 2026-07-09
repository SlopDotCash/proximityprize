#!/usr/bin/env python3
"""
#407 cumulant-from-flatness: IS kappa_2<=1 PROVABLE, and WHERE is the kappa_r wall?

PART 1 (kappa_2). Exact closed formula derived:
  kappa_2 = (p/(nm))^2 * [ R(0)^2 + (mN - (n-1)^2)/p ] / 3,    R(0)=(m-1+1/p)/m,
  where N = #{(w,w') in mu_n^2, w,w'!=1 : (1-w)/(1-w') in mu_n}.
  Forced floor N>=2n-3 (involution w->w^{-1}); N=2n-3 at GOOD primes.
  At N=2n-3, p=nm+1:  kappa_2 -> (1 + (2n-3)/n - ...)/3 -> 1^- as n,m -> infty.
  EXTRA solutions (N>2n-3) push kappa_2>1. So:
     kappa_2 <= 1  <=>  N <= 3n + n^2/m + O(1)  <=>  the UNIT EQUATION
        (1-w) = u*(1-w'),  u,w,w' in mu_{2^a},  w,w'!=1
     has at most ~3n solutions = ONLY the forced ones (diagonal w'=w gives u=1: n-1 sols;
     involution w'=w^{-1} gives u=-w^{-1}: n-1 sols; w=-1 boundary).
  THIS is a CHAR-0-style rigidity (no p) IF n^2/m -> 0, i.e. m >> n^2 i.e. p >> n^3.
  PRIZE: p ~ n*m, m~2^128 >> n^2 (n<=2^40 so n^2<=2^80 << 2^128). So n^2/m -> 0 AT PRIZE.
  => kappa_2 <= 1+o(1) at prize  <=>  the unit equation has only forced solns mod the prize prime.
  We TEST: at GOOD primes is N exactly 2n-3 once m>n^2? (the char-0 rigidity onset).

PART 2 (kappa_r wall). kappa_r = (p/nm)^r W_r/( (2r-1)!! ), W_r = sum closed r-walk prod R(h_i).
  Diagonal (matchings) = (2r-1)!! exactly. Off-diagonal = the r-fold unit-equation count.
  The Markov-Krein wall: from PROVEN moments E_1..E_R (R=O(1) at prize) cannot reach r~ln m.
  BUT the autocorrelation gives W_r EXACTLY. Question: does the off-diagonal of W_r stay o((2r-1)!!)
  up to r~ln m? We compute kappa_r (exact, from eta) at GOOD primes for r=2..6 and check the
  DEPTH r* at which kappa_r first exceeds 1 (the 'defect onset depth'), as a function of m.
  If r*(m) -> infty (grows with m, reaching ln m), the cumulant route CLOSES. If r* stays O(1)
  (capped at the p-defect onset r~2log_n p), it walls exactly as Markov-Krein predicts.
"""
import cmath, math
import sympy

def primitive_root(p): return int(sympy.primitive_root(p))

def kappa_profile(p,n,rmax=7):
    m=(p-1)//n
    g=primitive_root(p)
    mu=[pow(g,(m*t)%(p-1),p) for t in range(n)]
    mu_set=set(mu)
    def psi(x): return cmath.exp(2j*math.pi*(x%p)/p)
    seen=set();reps=[];b=1
    while len(reps)<m and b<p:
        if b not in seen:
            reps.append(b)
            for x in mu: seen.add(b*x%p)
        b+=1
    etas=[abs(sum(psi(b*w%p) for w in mu)) for b in reps]
    def dfac2(r):
        x=1
        for i in range(1,r+1): x*=(2*i-1)
        return x
    kap={r:(sum(e**(2*r) for e in etas)/m)/(dfac2(r)*n**r) for r in range(1,rmax+1)}
    # N count
    inv=[0]*p
    for x in range(1,p): inv[x]=pow(x,p-2,p)
    N=0
    for w in mu:
        if w==1:continue
        A=(1-w)%p
        for wp in mu:
            if wp==1:continue
            if (A*inv[(1-wp)%p])%p in mu_set: N+=1
    # first depth where kappa exceeds 1
    rstar=None
    for r in range(1,rmax+1):
        if kap[r]>1.0: rstar=r;break
    return dict(m=m,N=N,floor=2*n-3,kap=kap,rstar=rstar,n2_over_m=n*n/m)

def find_primes(n,count,start=2,cap=6000):
    out=[];k=start
    while len(out)<count:
        p=k*n+1
        if p>cap:break
        if sympy.isprime(p): out.append(p)
        k+=1
    return out

if __name__=="__main__":
    print("PART 1: char-0 rigidity onset -- at GOOD primes, is N=2n-3 forced once m>n^2?\n")
    print(f"{'n':>3}{'p':>6}{'m':>5} {'n2/m':>6} | {'N':>5}{'floor':>6} {'good?':>5}")
    for n in [4,8,16]:
        for p in find_primes(n,200,cap=4*n*n):  # go up to m~4n^2
            r=kappa_profile(p,n,rmax=2)
            if r['m']<n*n//2:
                if r['m'] not in (n*n//2,): continue
            good = (r['N']==r['floor'])
            if r['m'] in (n,2*n,n*n//2,n*n,2*n*n,3*n*n) or (r['m']>n*n and not good):
                print(f"{n:>3}{p:>6}{r['m']:>5} {r['n2_over_m']:>6.2f} | {r['N']:>5}{r['floor']:>6} {str(good):>5}")
    print("\nPART 2: kappa_r defect-onset depth r* vs m (GOOD primes). Does r* grow with m?\n")
    print(f"{'n':>3}{'p':>6}{'m':>5} | "+ "".join(f"k{r}".rjust(7) for r in range(1,7)) + f" | {'r*':>3}")
    for n in [8,16,32]:
        cnt=0
        for p in find_primes(n,400,cap=6000):
            r=kappa_profile(p,n,rmax=6)
            if r['N']!=r['floor']: continue  # good only
            if r['m']<8: continue
            cnt+=1
            if cnt% max(1,1)==0 and r['m'] in (9,11,15,21,29,42,57,72,99,128,150) :
                print(f"{n:>3}{p:>6}{r['m']:>5} | "+"".join(f"{r['kap'][rr]:7.3f}" for rr in range(1,7))+f" | {str(r['rstar']):>3}")
    print("\nr* = first r with kappa_r>1. If r* grows with m (toward ln m), cumulant route closes;")
    print("if r* stays ~2-3 (p-defect cap), it walls exactly as Markov-Krein predicts.")
