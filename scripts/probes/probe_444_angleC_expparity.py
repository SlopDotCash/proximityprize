"""
probe_444_angleC_expparity.py -- does the exponent-parity (e mod 2, f mod 2) govern O_P, and does
same-parity (e==f mod 2) collapse the problem onto mu_{n/2} (giving the load-bearing n/2)?

When e==f (mod 2): the witness word x^e+gamma x^f satisfies  W(-x)=(-1)^e W(x)  (since both
monomials have the same parity), so W is (anti)symmetric under x->-x.  Then agreement with a
deg<r poly P pairs up x and -x... explore whether bad-S come in antipodal-symmetric form and the
count reduces to choosing from n/2 antipodal pairs.

Tabulate O_P by exponent-parity class to see which class maximizes and whether the maximizer (the
worst line for the prize bound) is same-parity (=> the n/2 mechanism applies there).
"""
import sys
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

def build(n,r,p=P):
    w=gen(n,p); a0=r+1
    subs=list(combinations(range(n),a0))
    return w,subs,[hpow([pow(w,i,p) for i in S],n,p) for S in subs]

def OP(n,r,e,f,Hc,p=P):
    d=gcd((e-f)%n,n); nd=n//d; cos=set()
    for H in Hc:
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if g: cos.add(pow(g,nd,p))
    return len(cos),d

if __name__=="__main__":
    todo=[(3,16),(4,16),(5,16),(6,16)]
    if len(sys.argv)>1: todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    for (r,n) in todo:
        w,subs,Hc=build(n,r)
        # group lines by (e%2,f%2); record max O_P per class and the worst-ratio line
        byclass=defaultdict(lambda:(0,None,0))
        K=(1<<r)*comb(n//2,r)
        worst=(0.0,None,0,0,0)  # ratio O_P/(Kd/n), line, OP, d, class
        for e in range(r,n):
            for f in range(r,n):
                if e==f: continue
                if max(e-r+1,f-r+1)>n: continue
                op,d=OP(n,r,e,f,Hc)
                cls=(e%2,f%2)
                if op>byclass[cls][0]: byclass[cls]=(op,(e,f),d)
                ratio=op/(K*d/n)
                if ratio>worst[0]: worst=(ratio,(e,f),op,d,cls)
        print(f"r={r} n={n}: max O_P per (e%2,f%2) class:")
        for cls,(op,line,d) in sorted(byclass.items()):
            print(f"    class {cls}: maxO_P={op} at {line} d={d}")
        print(f"    WORST O_P/(Kd/n)={worst[0]:.3f} at line {worst[1]} (class {worst[4]}) O_P={worst[2]} d={worst[3]}")
