"""
probe_444_boundB_fiberparam.py -- PIN the r=3 fiber parametrization that gives degree C(n/4,2).

From probe_444_boundB_r3resultant: fix q=ab=-cd (dilation gauge). Then:
  a in mu_{n/2}, b=q/a  -> the pair {a,b} <-> a single 'half' coordinate; up to swap there are
     n/4 distinct unordered pairs? No: {a,q/a} for a in mu_{n/2} gives (n/2)/2 = n/4 pairs (a and
     q/a give same pair). Similarly {c,d} nonsquares with cd=-q: n/4 pairs.
So fiber base = (n/4) x (n/4) ordered, but J only depends on a SYMMETRIC combination.

We test: at fixed q, is J a function of the unordered pair { ratio a/b , ratio c/d }? or of the
pair {a/b, c/d} where a/b in mu_{n/2} (a square ratio)? The number of square-ratios is n/2 but
a/b and b/a give same unordered -> n/4. Map J <- (a/b-class, c/d-class) and check injectivity and
that the image has size C(n/4,2).

This identifies the EXACT degree-C(n/4,2) elimination object for r=3.
"""
from math import comb, gcd
from itertools import combinations
from collections import defaultdict

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

def fiber_param(n,e,f,p=P):
    w=gen(n,p); d=gcd((e-f)%n,n); nd=n//d
    sq=[pow(w,2*i,p) for i in range(n//2)]
    nsq=[pow(w,2*i+1,p) for i in range(n//2)]
    winv=pow(w,p-2,p)
    M=max(e-3+1,f-3+1)
    # fix q to a single representative: q = sq[0]*sq[?]; pick q = w^0 *? -- just fix ia0,ib0 so ab=1
    # choose q=1: a=w^{2i}, b=w^{-2i} -> ia,ib with 2ia+2ib=0 mod n -> ib=(n/2 - ia) mod n/2
    qfix=1
    J_to_keys=defaultdict(set); key_to_J=defaultdict(set)
    half=n//2
    for ia in range(half):
        ib=(-ia)%half   # so 2ia+2ib=0 mod n => ab=1=q
        if ib<ia: continue  # unordered, a/b ratio = w^{2ia-2ib}=w^{4ia}
        a,b=sq[ia],sq[ib]
        # need cd=-q=-1; c=nsq[ic], d=nsq[idd] with (2ic+1)+(2idd+1)=n/2*? cd=w^{2ic+1+2idd+1}=w^{2ic+2idd+2}
        # cd=-1=w^{n/2}. so 2ic+2idd+2 = n/2 mod n => ic+idd = (n/4 -1) mod (n/2)
        for ic in range(half):
            idd=((n//4 -1)-ic)%half
            if idd<ic: continue
            c,dd=nsq[ic],nsq[idd]
            if (c*dd)%p!=(-qfix)%p: continue
            S=[a,b,c,dd]; H=hpow(S,M,p)
            if (H[e-3]*H[f-3+1]-H[f-3]*H[e-3+1])%p: continue
            if H[f-3]==0: continue
            g=(-H[e-3]*pow(H[f-3],p-2,p))%p
            if not g: continue
            J=pow(g,nd,p)
            # a/b ratio = w^{2(ia-ib)} = w^{4ia} (since ib=-ia); class on mu_{n/2}: (2ia-2ib) mod n /2
            arat=(2*ia-2*ib)%n
            crat=(2*ic-2*idd)%n
            key=(min(arat,(-arat)%n), min(crat,(-crat)%n))
            J_to_keys[J].add(key); key_to_J[key].add(J)
    OP=len(J_to_keys)
    km=sum(1 for v in key_to_J.values() if len(v)>1)
    jm=sum(1 for v in J_to_keys.values() if len(v)>1)
    return OP, len(key_to_J), km, jm

if __name__=="__main__":
    print("r=3 fiber (fixed q=1): J <- (a/b ratio class, c/d ratio class):")
    print(f"{'n':>4} {'O_P':>5} {'#keys':>6} {'keys->1J?':>10} {'J->1key?':>10} {'C(n/4,2)':>9}")
    for n in [16,32,64]:
        e,f=n//2,n//2-1
        OP,nk,km,jm=fiber_param(n,e,f)
        print(f"{n:>4} {OP:>5} {nk:>6} {('yes' if km==0 else 'NO('+str(km)+')'):>10} "
              f"{('yes' if jm==0 else 'NO('+str(jm)+')'):>10} {comb(n//4,2):>9}")
