"""
probe_444_mech2_fiber.py -- the only constant-per-J index invariant is {|a-b|,|c-d|} (4 distinct
< O_P=6 at n=16). Map out which J share each {|u|,|v|} value and find the field-theoretic separator.

We print, for r=3 n=16/32: the full table J -> {|u|,|v|}, group J by that pair, and for each group
compute the extra discrete data (e.g. legendre of some cross quantity, or the value a*c which is the
genuine field coupling). Goal: identify a CLEAN finite separator that, combined with {|u|,|v|},
makes an injective map into a set of size <= C(n/2,r-1) (or the sharper C(n/4,2)).

Also: directly relate J to a 2-subset of mu_{n/4}.  mu_{n/4} = <w^4>, indices {0,4,8,...}.  The
proven count C(n/4,2). Test: is {|a-b|,|c-d|} actually a 2-subset of mu_{n/4} when we note |a-b|,
|c-d| are EVEN (in mu_{n/2}) and the constraint forces them div by ... let's measure parity of
|a-b|/2.
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
    J2S=defaultdict(list); Mmax=max(e-r+1,f-r+1)
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,Mmax,p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if not g: continue
        J2S[pow(g,nd,p)].append(Sidx)
    return w,J2S,d,nd

def study(n):
    r,e,f=3,n//2,n//2-1
    w,J2S,d,nd=collect(n,r,e,f)
    print(f"\n  r=3 n={n}: O_P={len(J2S)} C(n/4,2)={comb(n//4,2)} (mu_(n/4) has n/4={n//4} elts)")
    def uvpair(Sidx):
        ev=sorted(i for i in Sidx if i%2==0); od=sorted(i for i in Sidx if i%2==1)
        a,b=ev; c,dd=od
        u=min((a-b)%n,(b-a)%n); v=min((c-dd)%n,(dd-c)%n)
        return frozenset([u,v]) if u!=v else frozenset([u]), u, v
    # group J by {|u|,|v|}
    grp=defaultdict(list)
    for J,Ss in J2S.items():
        pr,_,_=uvpair(Ss[0])
        grp[pr].append(J)
    print("    {|a-b|,|c-d|} -> list of J sharing it:")
    for pr,Js in sorted(grp.items(), key=lambda kv:sorted(kv[0])):
        # are |u|,|v| divisible by 4 (mu_{n/4})?  div2 = (val/2) ; check /4
        vals=sorted(pr)
        div4=[v%4==0 for v in vals]
        print(f"      {sorted(pr)} (div4:{div4}) : {len(Js)} J's = {sorted(Js)[:4]}")
    # For groups with >1 J, what separates them? Compute a field coupling: pick canonical S per J
    # and look at the ACTUAL product a*b (=-(c*d)) reduced by orbit. Since a*b dilates as g^2,
    # (a*b)^{n/2}=(w-power)^{...}. Compute (a*b)^{n/ gcd} maybe distinguishes.
    print("    separator hunt for multi-J groups:")
    for pr,Js in sorted(grp.items(), key=lambda kv:sorted(kv[0])):
        if len(Js)<=1: continue
        rows=[]
        for J in Js:
            S=J2S[J][0]
            ev=sorted(i for i in S if i%2==0); od=sorted(i for i in S if i%2==1)
            a,b=ev; c,dd=od
            wa,wb,wc,wd=(pow(w,a,P),pow(w,b,P),pow(w,c,P),pow(w,dd,P))
            ab=wa*wb%P
            # ab is in mu_{n/2} times? ab=w^{a+b}. its index (a+b)%n.
            # cross coupling: a*c index (a+c)%n (odd). its ^2 -> mu_{n/2}.
            rows.append((J, (a+b)%n, (a-c)%n, (a-dd)%n))
        print(f"      group {sorted(pr)}: (J,(a+b)idx,(a-c)idx,(a-d)idx)={rows}")

if __name__=="__main__":
    for n in [16,32]:
        study(n)
