#!/usr/bin/env python3
"""
probe_444_forced_overlap.py  (#444 SEAM A)

The window-interior lists are tiny (|L|=4) with overlap 0, so the claim's packing premise never
even engages there. To STRESS-TEST the parity / overlap mechanism (Task 1 & 3), we LOWER the
agreement threshold s so that lists grow and members DO overlap, then check:

  (i)  does any DISTINCT pair overlap in MORE than 2k points? (refutes 'overlap<=2k' step)
  (ii) when a distinct pair overlaps in > k-1 points, is R=(F-F')^2 - y(G-G')^2 forced to ZERO?
       (if R==0 the parity claim 'a square can't equal y*square' is FALSE for these polys)
  (iii) what is the REAL relation on the overlap (should be f_i = f_j pointwise, i.e.
        (F-F')(y) = -x (G-G')(y), and squaring gives (F-F')^2 = y(G-G')^2 at those y ONLY).

We sweep s from k up to the window value, n in {16,32}, prize primes.
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
    c = list(c) + [0]*(k-len(c))
    return tuple(c[i] for i in range(0,k,2)), tuple(c[i] for i in range(1,k,2))

def build_word(exps, elts, p):
    return [sum(pow(x,a,p) for a in exps)%p for x in elts]

def poly_sub(a,b,p):
    L=max(len(a),len(b)); return tuple(((a[i] if i<len(a) else 0)-(b[i] if i<len(b) else 0))%p for i in range(L))
def poly_sq(a,p): return tuple(poly_mul(a,a,p))
def poly_trim(a):
    a=list(a)
    while len(a)>1 and a[-1]==0: a.pop()
    return tuple(a)
def deg(a):
    a=poly_trim(a); return len(a)-1 if any(x!=0 for x in a) else -1
def R_poly(F,Fp,G,Gp,sigma,p):
    dF=poly_sub(F,Fp,p); dG=poly_sub(G,tuple((sigma*g)%p for g in Gp),p)
    return poly_trim(poly_sub(poly_sq(dF,p), [0]+list(poly_sq(dG,p)), p))

def run(n,k,exps,wn,primes=1):
    rho=k/n
    ps=[find_window_prime(n,4.0)]+([find_window_prime(n,4.5)] if primes>1 else [])
    ps=list(dict.fromkeys(ps))
    s_window=max(round((rho+rho)*n),k)
    for p in ps:
        elts=subgroup(n,p); N=n//2
        u=build_word(exps,elts,p)
        print(f"\n  {wn}: n={n} k={k} p={p}  (window s={s_window}=2k)  sweeping s from k={k} up")
        for s in range(k, s_window+1):
            members=sorted(list_RS_members(u,elts,k,s,p))
            if len(members)<2:
                print(f"     s={s}: |L|={len(members)}"); continue
            agsets=[frozenset(i for i in range(n) if peval(c,elts[i],p)==u[i]) for c in members]
            cls=['E' if all(g==0 for g in split_FG(c,k)[1]) else 'M' for c in members]
            worst_ov=0; worst=None; Rzero_distinct=0; bad_parity=[]
            for i in range(len(members)):
                for j in range(i+1,len(members)):
                    ov=len(agsets[i]&agsets[j])
                    if ov>worst_ov: worst_ov=ov; worst=(i,j,cls[i],cls[j])
                    F,G=split_FG(members[i],k); Fp,Gp=split_FG(members[j],k)
                    Rp=R_poly(F,Fp,G,Gp,1,p); Rm=R_poly(F,Fp,G,Gp,-1,p)
                    if deg(Rp)<0 or deg(Rm)<0:
                        Rzero_distinct+=1
                    # parity falsifier: overlap large but R!=0 (claim OK) vs overlap large & R==0 (parity FALSE)
                    if ov>k and (deg(Rp)<0 or deg(Rm)<0):
                        bad_parity.append((i,j,ov,deg(Rp),deg(Rm)))
            print(f"     s={s}: |L|={len(members)} (E={cls.count('E')} M={cls.count('M')})  "
                  f"worst overlap={worst_ov} (2k={2*k}; {'<=2k' if worst_ov<=2*k else 'EXCEEDS 2k!'}) "
                  f"at pair {worst};  #distinct pairs with R==0={Rzero_distinct}; "
                  f"parity-falsifiers(ov>k & R==0)={len(bad_parity)}")

if __name__=="__main__":
    print("="*90)
    print("#444 FORCED-OVERLAP STRESS TEST (Tasks 1 & 3): lower s to grow lists, probe overlap & R")
    print("="*90)
    cfgs=[
        (16,2,[4,0],"x^4+1"),
        (16,2,[4,1,0],"x^4+x+1"),
        (16,4,[4,0],"x^4+1(k=4)"),
        (16,4,[6,3,0],"x^6+x^3+1(k=4)"),
        (32,4,[8,0],"x^8+1"),
        (32,4,[8,3,0],"x^8+x^3+1"),
    ]
    for (n,k,exps,wn) in cfgs:
        run(n,k,exps,wn)
