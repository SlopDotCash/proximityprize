#!/usr/bin/env python3
"""
probe_444_overlap_w2.py  (#444 SEAM A) -- FAST weight-2-only overlap scan.

Replaces the timed-out weight-3 n=32 scan. For every weight-2 word x^a+x^b (a,b != n/2),
at the WINDOW threshold s=round(2*rho*n) AND at a LOW threshold s=k (to grow lists), measure
the max pairwise overlap among distinct window-list members and whether it ever exceeds 2k.
"""
import itertools
from sympy import isprime, primitive_root

def find_window_prime(n, beta=4.0, idx_min=2):
    target=int(n**beta); base=target-(target%n)+1; p=base
    while True:
        if p>n and isprime(p) and (p-1)%n==0 and (p-1)//n>=idx_min: return p
        p+=n
def subgroup(n,p):
    g=primitive_root(p); zeta=pow(g,(p-1)//n,p)
    e,x=[],1
    for _ in range(n): e.append(x); x=(x*zeta)%p
    return e
def poly_mul(a,b,p):
    r=[0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b): r[i+j]=(r[i+j]+ai*bj)%p
    return r
def interp_coeffs(xs,ys,p):
    k=len(xs); c=[0]*k
    for i in range(k):
        num=[1]; den=1
        for j in range(k):
            if j==i: continue
            num=poly_mul(num,[(-xs[j])%p,1],p); den=(den*((xs[i]-xs[j])%p))%p
        inv=pow(den,p-2,p); sc=(ys[i]*inv)%p
        for t in range(len(num)): c[t]=(c[t]+sc*num[t])%p
    return tuple(c)
def peval(c,x,p):
    r=0
    for a in reversed(c): r=(r*x+a)%p
    return r
def list_RS_members(uvals, elts, k, s, p):
    n=len(elts); seen=set()
    for T in itertools.combinations(range(n),k):
        xs=[elts[i] for i in T]; ys=[uvals[i] for i in T]
        c=interp_coeffs(xs,ys,p)
        if c in seen: continue
        ag=sum(1 for i in range(n) if peval(c,elts[i],p)==uvals[i])
        if ag>=s: seen.add(c)
    return seen
def split_FG(c, k):
    c=list(c)+[0]*(k-len(c)); return tuple(c[i] for i in range(0,k,2)),tuple(c[i] for i in range(1,k,2))
def build_word(exps, elts, p):
    return [sum(pow(x,a,p) for a in exps)%p for x in elts]

def scan(n,k):
    rho=k/n; s_win=max(round(2*rho*n),k)
    p=find_window_prime(n,4.0); elts=subgroup(n,p)
    for label,s in [("window",s_win),("low(s=k)",k),("mid",max((k+s_win)//2,k))]:
        gmax=-1; gword=None; nviol=0; nwords=0; maxL=0
        for a in range(1,n):
            for b in range(0,a):
                if a==n//2 or b==n//2: continue
                u=build_word([a,b],elts,p)
                members=sorted(list_RS_members(u,elts,k,s,p))
                if len(members)<2: continue
                nwords+=1; maxL=max(maxL,len(members))
                ag=[frozenset(i for i in range(n) if peval(c,elts[i],p)==u[i]) for c in members]
                for i in range(len(members)):
                    for j in range(i+1,len(members)):
                        ov=len(ag[i]&ag[j])
                        if ov>gmax: gmax=ov; gword=(a,b,i,j,len(members))
                        if ov>2*k: nviol+=1
        print(f"  n={n} k={k} p={p} s={s}({label}): #words(|L|>=2)={nwords} maxL={maxL} "
              f"maxOverlap={gmax} (2k={2*k}) word/pair={gword}  overlap>2k count={nviol}")

if __name__=="__main__":
    print("#444 FAST weight-2 overlap scan: does any distinct pair overlap > 2k?")
    for (n,k) in [(16,2),(16,1),(16,4),(32,4),(32,2)]:
        scan(n,k)
