#!/usr/bin/env python3
"""
probe_444_overlap_scan.py  (#444 SEAM A)

Direct refutation engine. The claim says: distinct window-list members pairwise overlap
(share <= 2k agreement points). If TRUE, Fisher/Johnson packing caps L. We hunt for a
COUNTEREXAMPLE: a word whose window list has a pair of DISTINCT members overlapping in > 2k
points. We scan ALL weight-2 and weight-3 words (even & mixed), at n=16,32, both prize primes,
report:
  - the maximum pairwise overlap over all words and pairs,
  - the word/pair achieving it, with member classes (EVEN/MIXED),
  - whether worst overlap > 2k anywhere (=> packing-route claim REFUTED at the overlap step).

Also: for the EVEN-word restriction specifically (claim is stated for even words), the same.
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
    F = tuple(c[i] for i in range(0,k,2))
    G = tuple(c[i] for i in range(1,k,2))
    return F,G

def is_even_member(c,k):
    F,G=split_FG(c,k); return all(g==0 for g in G)

def build_word(exps, elts, p):
    return [sum(pow(x,a,p) for a in exps)%p for x in elts]

def scan(n,k,eta,weights=(2,3),even_word_only=False,beta_list=(4.0,4.5)):
    rho=k/n; s=round((rho+eta)*n); s=max(s,k); twok=2*k
    ps=[find_window_prime(n,b) for b in beta_list]; ps=list(dict.fromkeys(ps))
    summary=[]
    for p in ps:
        elts=subgroup(n,p)
        global_max_ov=-1; gm=None
        gm_distinct_max=-1; gmd=None   # max overlap among DISTINCT members (always distinct here)
        viol=[]   # words with a pair overlapping > 2k
        nwords=0
        for w in weights:
            for combo in itertools.combinations(range(0,n),w):
                if any(a==n//2 for a in combo): continue
                if even_word_only and any(a%2!=0 for a in combo): continue
                u=build_word(list(combo),elts,p)
                members=sorted(list_RS_members(u,elts,k,s,p))
                if len(members)<2: continue
                nwords+=1
                agsets=[(c,frozenset(i for i in range(n) if peval(c,elts[i],p)==u[i])) for c in members]
                cls=['EVEN' if is_even_member(c,k) else 'MIXED' for c in members]
                for i in range(len(members)):
                    for j in range(i+1,len(members)):
                        ov=len(agsets[i][1]&agsets[j][1])
                        if ov>global_max_ov:
                            global_max_ov=ov; gm=(combo,i,j,cls[i],cls[j],len(members))
                        if ov>twok:
                            viol.append((combo,i,j,ov,cls[i],cls[j],len(members)))
        summary.append(dict(n=n,k=k,s=s,p=p,twok=twok,nwords=nwords,
                            global_max_ov=global_max_ov,gm=gm,
                            nviol=len(viol),viol_sample=viol[:10]))
    return summary

if __name__=="__main__":
    print("#444 OVERLAP SCAN: is pairwise overlap of distinct window members ever > 2k?")
    test_set=[(16,2,0.125),(16,1,0.0625),(32,4,0.125),(32,2,0.0625)]
    for even_only in (False, True):
        print("\n"+"#"*90)
        print(f"###  even_word_only = {even_only}   (claim is stated for EVEN words)")
        print("#"*90)
        for (n,k,eta) in test_set:
            for row in scan(n,k,eta,weights=(2,3),even_word_only=even_only):
                print(f"\n  n={row['n']} k={row['k']} s={row['s']} p={row['p']}  2k={row['twok']}  "
                      f"#words(|L|>=2)={row['nwords']}")
                print(f"    GLOBAL max pairwise overlap = {row['global_max_ov']}  achieved by "
                      f"word/exps & pair {row['gm']}")
                print(f"    overlap > 2k ?  {row['global_max_ov']>row['twok']}   "
                      f"(# violating pairs = {row['nviol']})")
                for v in row['viol_sample']:
                    print(f"       VIOLATION word={v[0]} pair=({v[1]},{v[2]}) overlap={v[3]} "
                          f"cls=({v[4]},{v[5]}) |L|={v[6]}  > 2k={row['twok']}")
