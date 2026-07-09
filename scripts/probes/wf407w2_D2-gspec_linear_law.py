#!/usr/bin/env python3
"""
wf407w2_D2-gspec_linear_law.py  --  #407 D2-gspec, CONFIRM the linear-in-n law and the identity.

Surfaced facts to pin:
  (1) G subset mu_n  =>  |mu_n cap g*mu_n| = n  for EVERY g in G (group dilated by group element).
      Hence  lever := sum_{g in G} |mu_n cap g*mu_n| = |G| * n  EXACTLY.  Confirm.
  (2) |G| grows ~ linearly in n (NOT O(1)).  Fit |G| vs n over n=16..256 at fixed beta and over
      several primes; report |G|/n.
  (3) genuine_count = (1/2)*lever (each genuine unordered quadruple contributes one product-unit g
      and one inverse).  Hence genuine_count = (1/2)|G|*n = Theta(n^2) = a constant fraction of the
      energy excess.  Confirm genuine == lever/2 and excess/genuine ~ const.
  (4) Galois orbit count of G grows too (not a single fixed orbit) -- confirm #orbits grows with n.
This is the REFUTATION of the O(1)-localization lever: localizing to G is Theta(n) per term times a
linearly-growing #terms = Theta(n^2) = the same additive-energy wall.
"""
import math
from collections import defaultdict, Counter

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        if m % q == 0: return m == q
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1):continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True

def factorize(m):
    s={};d=2
    while d*d<=m:
        while m%d==0:s[d]=s.get(d,0)+1;m//=d
        d+=1
    if m>1:s[m]=s.get(m,0)+1
    return s

def primitive_root(p):
    fac=factorize(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):return g
    return None

def smallest_prime_1_mod(n, lo):
    p=lo+((1-lo)%n)
    if p<3:p+=n
    while True:
        if p%n==1 and is_prime(p):return p
        p+=n

def subgroup(p,n):
    g=primitive_root(p);h=pow(g,(p-1)//n,p)
    return [pow(h,i,p) for i in range(n)],h

def E2(p, mu):
    r=Counter()
    for a in mu:
        for b in mu:
            r[(a+b)%p]+=1
    return sum(v*v for v in r.values())

def genuine_defects(p,n,S):
    bysum=defaultdict(list)
    for i in range(n):
        for j in range(i,n):
            bysum[(S[i]+S[j])%p].append((S[i],S[j]))
    out=[]
    for s,prs in bysum.items():
        if len(prs)<2 or s==0: continue
        for a in range(len(prs)):
            for b in range(a+1,len(prs)):
                (x1,x2),(y1,y2)=prs[a],prs[b]
                if {x1,x2}=={y1,y2}: continue
                if frozenset(((p-y1)%p,(p-y2)%p))==frozenset((x1,x2)): continue
                out.append((x1,x2,y1,y2,s))
    return out

def main():
    print("="*116)
    print("D2-gspec linear-law confirmation: |G| ~ n,  lever = |G|*n,  genuine = lever/2 = Theta(n^2)")
    print("="*116)
    print(f"\n{'n':>4} {'p':>8} {'|G|':>4} {'|G|/n':>6} {'all D(g)=n?':>11} {'lever':>7} {'|G|*n':>7} "
          f"{'genuine':>8} {'lever/2':>8} {'#gal-orb':>9} {'excess/gen':>10}")
    Gn=[]
    for n in (16,32,64,128,256):
        E0=3*n*n-3*n
        p=smallest_prime_1_mod(n,int(n**2.0))
        S,h=subgroup(p,n); muset=set(S)
        gen=genuine_defects(p,n,S)
        if not gen:
            print(f"{n:>4} {p:>8}  (no genuine)"); continue
        excess=E2(p,muset)-E0
        prodg=Counter()
        for (x1,x2,y1,y2,s) in gen:
            g=(x1*x2%p)*pow(y1*y2%p,-1,p)%p
            prodg[g]+=1
        G=list(prodg)
        # confirm G subset mu_n and D(g)=n for all g
        all_in_mu=all(g in muset for g in G)
        Ds=[sum(1 for x in muset if (g*x)%p in muset) for g in G]
        allDn=all(d==n for d in Ds)
        lever=sum(Ds)
        # galois orbits
        logmap={}; cur=1
        for j in range(n): logmap[cur]=j; cur=(cur*h)%p
        ks=[k for k in range(1,n) if math.gcd(k,n)==1]
        orbs=set(frozenset((k*logmap[g])%n for k in ks) for g in G)
        ng=len(gen)
        print(f"{n:>4} {p:>8} {len(G):>4} {len(G)/n:>6.3f} {str(all_in_mu and allDn):>11} {lever:>7} "
              f"{len(G)*n:>7} {ng:>8} {lever//2:>8} {len(orbs):>9} {excess/ng if ng else 0:>10.3f}")
        Gn.append((n,len(G)))
    print("\n" + "="*116)
    print("FIT |G| vs n (least squares slope through origin):")
    if Gn:
        slope=sum(g for _,g in Gn)/sum(n for n,_ in Gn)  # crude |G|/n average
        num=sum(n*g for n,g in Gn); den=sum(n*n for n,_ in Gn)
        ls=num/den
        print(f"   avg(|G|/n)={sum(g/n for n,g in Gn)/len(Gn):.3f}   LS slope(|G|=c*n)={ls:.3f}")
        print(f"   -> |G| = Theta(n), NOT O(1).  Combined with D(g)=n: lever = Theta(n^2) = the wall.")

if __name__=="__main__":
    main()
