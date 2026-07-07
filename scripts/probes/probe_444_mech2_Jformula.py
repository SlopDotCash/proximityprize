"""
probe_444_mech2_Jformula.py -- find the CLOSED FORM of J in terms of S, then read off the
(r-1)-subset of squares it is determined by.

Finding so far (r=3): within-part index diffs {|a-b|,|c-d|} are dilation-INVARIANT and CONSTANT
per J, but only 4 distinct values vs O_P=6 -- they lose the cross-coupling a*b=-c*d sign data.

Now: compute gamma and J as explicit field elements and express via the elementary/power-sum data
of S, looking for J = (ratio of products over an (r-1)-subset of mu_{n/2}).  Specifically test:
  For r=3, gamma=-h_{e-r}(S)/h_{f-r}(S) = -h_{n/2-3}(S)/h_{n/2-4}(S) (e=n/2,f=n/2-1,r=3).
  Hypothesis: J=gamma^n is a function of CROSS-RATIOS.  We FIT J against candidate monomials in
  the 4 roots a,b,c,d (as field elements) that are dilation-invariant of weight 0:
     a/c, a/d, b/c, b/d, (ab)/(cd)=-1 (known), a/b, c/d.
  Since gamma(gS)=g^{e-f}gamma(S)=g^{-1}gamma(S), J=gamma^n is invariant; gamma itself has weight -1.
  So gamma ~ (weight -1 rational fn). Find it: gamma * (a) should be weight 0 => gamma=W0/a-type.

We brute-force: for r=3, regress log_w-style by computing gamma for many S and checking
  gamma =? -h_{n/2-3}/h_{n/2-4} and whether gamma = c0 * e_k-combinations.  Then J in terms of the
  TWO ratios {a/b, c/d} (each in mu_{n/2}) -> 2 'data' = (r-1)=2 subset.  TEST: is J determined by
  the unordered pair {a/b, c/d} (as elements of mu_{n/2})?  THIS is the candidate Phi.
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

P=2013265921
def gen(n,p=P):
    e=(p-1)//n
    for c in range(2,2000):
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
def collect(n,r,e,f,p=P):
    w=gen(n,p); a0=r+1; d=gcd((e-f)%n,n); nd=n//d
    J2S=defaultdict(list); g2info={}; Mmax=max(e-r+1,f-r+1)
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,Mmax,p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if not g: continue
        J=pow(g,nd,p); J2S[J].append((Sidx,g))
    return w,J2S,d,nd

def test_pair_invariant(n):
    """r=3: test if J is determined by the unordered pair {a/b, c/d} in mu_{n/2} (index form:
       {|ia-ib|, |ic-id|} already shown constant but lossy). Now use SIGNED ratios as FIELD elements
       and the cross product to recover full invariant."""
    r,e,f=3,n//2,n//2-1
    w,J2S,d,nd=collect(n,r,e,f)
    print(f"  r=3 n={n}: O_P={len(J2S)} C(n/4,2)={comb(n//4,2)} C(n/2,2)={comb(n//2,2)}")
    # For each J, gather the candidate invariants per S and check constancy+injectivity:
    #  inv_ratio = unordered { a*b^{-1} , c*d^{-1} }  (field elements in mu_{n/2})
    #  inv_cross = a*c^{-1} (mod sign)  etc.
    cands={
      'pair{a/b,c/d}': lambda a,b,c,dd:frozenset([a*pow(b,P-2,P)%P, c*pow(dd,P-2,P)%P,
                                                   b*pow(a,P-2,P)%P, dd*pow(c,P-2,P)%P]),
      'pair{a/c,b/d}': lambda a,b,c,dd:frozenset([a*pow(c,P-2,P)%P, b*pow(dd,P-2,P)%P]),
      'set{a/c,a/d,b/c,b/d}': lambda a,b,c,dd:frozenset([a*pow(c,P-2,P)%P,a*pow(dd,P-2,P)%P,
                                                         b*pow(c,P-2,P)%P,b*pow(dd,P-2,P)%P]),
      'sum a/c+b/d type e2': lambda a,b,c,dd:( (a*pow(c,P-2,P)+b*pow(dd,P-2,P))%P,
                                               (a*pow(dd,P-2,P)+b*pow(c,P-2,P))%P),
    }
    for name,fn in cands.items():
        J2inv=defaultdict(set)
        for J,Ss in J2S.items():
            for Sidx,g in Ss:
                xs=[pow(w,i,P) for i in Sidx]
                ev=[(i,pow(w,i,P)) for i in Sidx if i%2==0]
                od=[(i,pow(w,i,P)) for i in Sidx if i%2==1]
                if len(ev)!=2 or len(od)!=2:
                    J2inv[J].add(('BAD',)); continue
                a=ev[0][1]; b=ev[1][1]; c=od[0][1]; dd=od[1][1]
                J2inv[J].add(fn(a,b,c,dd))
        const=all(len(v)==1 for v in J2inv.values())
        if const:
            reps=[next(iter(v)) for v in J2inv.values()]
            nd_=len(set(reps))
            print(f"    [{name}] constant per J: True; #distinct={nd_} (==O_P {len(J2S)}? {nd_==len(J2S)})")
        else:
            nb=sum(1 for v in J2inv.values() if len(v)>1)
            print(f"    [{name}] constant per J: False ({nb}/{len(J2S)})")

if __name__=="__main__":
    for n in [16,32]:
        test_pair_invariant(n)
