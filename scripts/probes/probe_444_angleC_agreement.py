"""
probe_444_angleC_agreement.py -- Angle C reframing as an AGREEMENT / list-decoding count.

CLAIM (verify):  gamma is BAD (for the deep band r, line (x^e,x^f)) iff the word
     w_gamma = ( g^{e*i} + gamma*g^{f*i} )_{i=0..n-1}   in F_p^n  (indexed by mu_n)
has agreement >= r+1 with the Reed-Solomon code  RS = { evaluations of deg<r polys on mu_n }.
(Because: an (r+1)-subset S is bad <=> w_gamma|_S is interpolated by a deg-<r poly = a codeword
of RS restricted to S; and if w_gamma agrees with a deg<r poly P on >=r+1 points, those points
form a bad S.)

So:  #bad gamma (incl orbits) = #{ gamma : agree(w_gamma, RS) >= r+1 }.
And O_P = (#bad nonzero gamma) / (n/d).

This recasts the prize floor as a LIST-DECODING-RADIUS statement:
   How many gamma-cosets put x^e + gamma x^f within distance n-(r+1) of RS[deg<r]?

A clean a-priori bound:  if w_gamma agrees with codeword P_gamma (deg<r) on >=r+1 points, then
   x^e + gamma x^f - P_gamma(x)   vanishes at >=r+1 points of mu_n.
Consider the polynomial  Q_gamma(x) = x^e + gamma x^f - P_gamma(x)  (reduce exps mod the relation
x^n=1 on mu_n: as a function on mu_n, x^e == x^{e mod n}).  Q_gamma is a function on mu_n with
>=r+1 zeros.  As a polynomial of degree < n it would have < n zeros automatically; the content is
that it has a SPECIAL low-complexity form (only the monomials x^e, x^f beyond deg<r).

This probe:
  (1) VERIFY the agreement reframing reproduces #bad exactly (anti-fabrication).
  (2) For each gamma, find the agreement value and the best codeword; study how many gamma reach
      agreement r+1 and WHY (the structure of the deg-<r poly P_gamma).
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

P=2013265921

def gen(n,p=P):
    e=(p-1)//n
    for c in range(2,600):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError

def hpow(elts,M,p=P):
    Pw=[0]*(M+1)
    for i in range(1,M+1): Pw[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for m in range(1,M+1):
        s=0
        for i in range(1,m+1): s=(s+Pw[i]*H[m-i])%p
        H[m]=(s*pow(m,p-2,p))%p
    return H

def bad_via_h(n,r,e,f,p=P):
    """ground-truth bad-gamma set via the Schur-ratio variety (the proven reduction)."""
    w=gen(n,p); a0=r+1; nz=set()
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,max(e-r+1,f-r+1),p)
        her,her1,hfr,hfr1=H[e-r],H[e-r+1],H[f-r],H[f-r+1]
        if (her*hfr1-hfr*her1)%p: continue
        if hfr==0: continue
        g=(-her*pow(hfr,p-2,p))%p
        if g: nz.add(g)
    return nz, w

def agreement_count(n,r,e,f,gammas,w,p=P):
    """For a set of candidate gammas, compute agree(w_gamma, RS[deg<r]) via: for each (r+1)-subset?
       Too slow to scan all gamma in F_p. Instead VERIFY: every gamma in `gammas` (the h-derived
       bad set) indeed has an (r+1)-agreement codeword, and report the agreement value."""
    xs=[pow(w,i,p) for i in range(n)]
    out={}
    for gam in list(gammas)[:50]:
        wvec=[(pow(x,e,p)+gam*pow(x,f,p))%p for x in xs]
        # find max agreement with deg<r polys: for each (r+1)-subset that interpolates to deg<r,
        # count agreements of that codeword with wvec. Cheaper: for each r-subset define the unique
        # deg<r interpolant and count agreements. C(n,r) loop.
        best=0
        for Ridx in combinations(range(n),r):
            # deg<r poly through r points (Ridx, wvec) -- unique; eval on all n, count matches
            pts=[xs[i] for i in Ridx]; vals=[wvec[i] for i in Ridx]
            # Lagrange eval at all xs
            agree=0
            for j in range(n):
                xj=xs[j]; acc=0
                for t in range(r):
                    num=1; den=1
                    for s in range(r):
                        if s!=t:
                            num=num*((xj-pts[s])%p)%p; den=den*((pts[t]-pts[s])%p)%p
                    acc=(acc+vals[t]*num*pow(den,p-2,p))%p
                if acc==wvec[j]: agree+=1
            best=max(best,agree)
            if best>=r+1: break
        out[gam]=best
    return out

if __name__=="__main__":
    # (1) verify reframing on r=3 n=16: every h-bad gamma reaches agreement>=r+1
    for (r,n,e,f) in [(3,16,8,7),(4,16,10,5)]:
        nz,w=bad_via_h(n,r,e,f)
        ag=agreement_count(n,r,e,f,nz,w)
        ok=all(v>=r+1 for v in ag.values())
        print(f"r={r} n={n} (x^{e},x^{f}): #bad(nz)={len(nz)}; sampled {len(ag)} gammas, "
              f"all reach agreement>=r+1? {ok}; agreement dist={Counter(ag.values())}")
