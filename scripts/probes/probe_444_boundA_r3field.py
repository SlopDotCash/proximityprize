"""
probe_444_boundA_r3field.py -- derive J=gamma^n at r=3 as a FIELD function and explain O_P=C(n/4,2)
as a FIELD-VALUE count (not a subset count).

r=3, line (n/2, n/2-1). S={a,b,c,d}, gamma = -h_{n/2-3}(S)/h_{n/2-4}(S).
We want J=gamma^n in closed form in terms of (a,b,c,d) and the relation ab=-cd.

Key simplification: h_m(S) for m near n/2 can be related to power sums; but more useful is the
ORBIT invariant. Under dilation by g: S->gS, gamma->g^{e-f}gamma=g*gamma (e-f=1). So gamma itself
is NOT orbit-invariant; gamma^n=J is. Also gamma(gS)=g gamma(S) means gamma 'is' a coordinate.

Pick the orbit representative: we can dilate so that, say, the product of all 4 elements =1, or
one element =1. Let's instead directly compute J=gamma^n for all bad S and see how many distinct,
and express J via the symmetric functions e_k(S) (k=1..4) which ARE the natural coordinates.

CLAIM TO TEST: J = gamma^n is a function of the RATIOS of elementary symmetric polys that is
dilation-degree-0, i.e. J = F(e_1^4/e_4, e_2^2/e_4, e_3^4/e_4^3) or similar SCALE-INVARIANT
combos. Since #scale-invariant coords of 4 points up to dilation = 3, and the variety V is 1 eqn,
the bad locus is 2-dimensional in these coords, but J takes finitely many values because S is
DISCRETE (in mu_n). The count C(n/4,2) is the number of distinct J over the discrete bad set.

We test: is J a function of (e2^2/e4, e1*e3/e4) [the two genuinely scale-inv degree-low combos]?
And we COUNT distinct (e2^2/e4 mod something) to match C(n/4,2).
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

PRIMES=[2013265921,3221225473]
def gen(n,p):
    e=(p-1)//n
    for c in range(2,2000):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError
def hpow(elts,M,p):
    Pw=[0]*(M+1)
    for i in range(1,M+1): Pw[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for m in range(1,M+1):
        s=0
        for i in range(1,m+1): s=(s+Pw[i]*H[m-i])%p
        H[m]=(s*pow(m,p-2,p))%p
    return H
def esym(elts,p):
    # e_0..e_k
    E=[1]
    for z in elts:
        newE=E+[0]
        for i in range(len(E),0,-1):
            newE[i]=(newE[i]+E[i-1]*z)%p
        E=newE
    return E  # E[k]=e_k

def collect(n,p):
    r=3; e,f=n//2,n//2-1; a0=4; w=gen(n,p); d=gcd((e-f)%n,n); nd=n//d
    M=max(e-r+1,f-r+1)
    rows=[]
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,M,p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if not g: continue
        J=pow(g,nd,p)
        E=esym(xs,p)  # e1..e4
        rows.append((J,g,E[1],E[2],E[3],E[4],tuple(sorted(Sidx))))
    return rows

def inv(a,p): return pow(a,p-2,p)

if __name__=="__main__":
    p=PRIMES[0]
    for n in [16,32]:
        rows=collect(n,p)
        OP=len(set(r[0] for r in rows))
        print(f"### n={n}: O_P={OP} C(n/4,2)={comb(n//4,2)} #badS={len(rows)}")
        # scale-invariant combos: I1 = e2^2/e4 (deg 0), I2 = e1*e3/e4 (deg0), I3=e1^4/e4, I4=e3^4/e4^3
        def feats(row):
            J,g,e1,e2,e3,e4=row[:6]
            I1=(e2*e2%p)*inv(e4,p)%p
            I2=(e1*e3%p)*inv(e4,p)%p
            I3=(pow(e1,4,p))*inv(e4,p)%p
            I4=(pow(e3,4,p))*inv(pow(e4,3,p),p)%p
            return I1,I2,I3,I4
        # is J a function of (I1,I2)?
        for combo,getf in [("I1",lambda r:(feats(r)[0],)),
                           ("I2",lambda r:(feats(r)[1],)),
                           ("(I1,I2)",lambda r:(feats(r)[0],feats(r)[1])),
                           ("I3",lambda r:(feats(r)[2],)),
                           ("I4",lambda r:(feats(r)[3],)),
                           ("(I1,I2,I3,I4)",lambda r:feats(r))]:
            J2v=defaultdict(set); v2J=defaultdict(set)
            for row in rows:
                v=getf(row); J2v[row[0]].add(v); v2J[v].add(row[0])
            const=all(len(s)==1 for s in J2v.values())
            inj=all(len(s)==1 for s in v2J.values())
            print(f"   J vs {combo}: const-per-J={const} inj={inj} #vals={len(v2J)} (O_P={OP})")
