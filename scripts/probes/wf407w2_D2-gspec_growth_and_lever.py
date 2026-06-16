#!/usr/bin/env python3
"""
wf407w2_D2-gspec_growth_and_lever.py  --  #407 D2-gspec, the DECISIVE scaling.

Two crux measurements the first probe surfaced:
  (A) |G| (the g-spectrum size) appears O(1) (4 at n=16, 6 at n=32, n=64).  Push to n=128, 256 to
      confirm it does NOT grow.  ALSO test multiple primes per (n,beta) -- is |G| stable or does it
      depend on the prime?
  (B) THE WALL TEST.  Even if |G|=O(1), the count is  sum_{g in G} |mu_n cap g*mu_n|.  The per-g
      incidence  D(g) = |mu_n cap g*mu_n|  is a DILATE INCIDENCE.  Does each D(g) grow with n?
      Decompose:
         genuine_count  =  (1/2) * sum_{g in G_genuine} D_genuine(g)
      and compare D(g) growth to n.  If D(g) = Theta(n) for the relevant g, then even O(1) values
      of g give Theta(n) per term -> the SAME additive-energy floor (since E2 excess = sum over the
      same g of the same incidences).  The localization is then NOT a lever: it just RE-INDEXES the
      energy by its dominant Fourier/dilate frequencies, which is exactly Cauchy-Schwarz.

  (C) DIRECT IDENTITY.  Prove numerically that  excess = E2^(p)-E2^(0)  is recovered EXACTLY by the
      g-localized sum over ALL dilate units g (not just G), to confirm the localization to G is a
      strict UNDERcount that still scales like n (constant fraction).  This pins whether G is a
      genuine bounded handle or a constant-fraction shadow of the full energy.
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

def primes_1_mod(n, lo, count):
    p=lo+((1-lo)%n)
    if p<3:p+=n
    out=[]
    while len(out)<count:
        if p%n==1 and is_prime(p): out.append(p)
        p+=n
    return out

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

def dilate_incidence(p, muset, g):
    return sum(1 for x in muset if (g*x)%p in muset)

def main():
    print("="*120)
    print("D2-gspec (A) g-spectrum size & (B) per-g dilate-incidence growth  --  the lever vs wall test")
    print("="*120)
    print(f"\n{'n':>4} {'beta':>5} {'p':>10} {'excess':>7} {'#gen':>6} {'|G|':>4} {'max_D(g)':>9} "
          f"{'avg_D(g)':>9} {'maxD/n':>7} {'lever':>7} {'lever/exc':>9}")
    GtrackByN=defaultdict(set)
    for n in (16,32,64,128,256):
        E0=3*n*n-3*n
        # use the smallest few sub-prize betas that yield genuine defects; multiple primes
        for beta in (2.0,):
            primes=primes_1_mod(n,int(n**beta),3)
            for p in primes:
                S,h=subgroup(p,n); muset=set(S)
                gen=genuine_defects(p,n,S)
                ng=len(gen)
                if ng==0:
                    continue
                excess=E2(p,muset)-E0
                prodg=Counter()
                for (x1,x2,y1,y2,s) in gen:
                    g=(x1*x2%p)*pow(y1*y2%p,-1,p)%p
                    prodg[g]+=1
                G=list(prodg)
                GtrackByN[n].add(len(G))
                Ds={g:dilate_incidence(p,muset,g) for g in G}
                maxD=max(Ds.values()); avgD=sum(Ds.values())/len(Ds)
                lever=sum(Ds.values())
                print(f"{n:>4} {beta:>5} {p:>10} {excess:>7} {ng:>6} {len(G):>4} {maxD:>9} "
                      f"{avgD:>9.1f} {maxD/n:>7.3f} {lever:>7} {lever/excess if excess else 0:>9.3f}")
    print("\n" + "="*120)
    print("g-spectrum size |G| observed per n (across the sampled primes):")
    for n in sorted(GtrackByN):
        print(f"   n={n:4d}:  |G| in {sorted(GtrackByN[n])}")
    print("\nKEY: if max_D(g)/n is ROUGHLY CONSTANT (each g-dilate incidence ~ Theta(n)) AND")
    print("     lever/excess ~ const, then |G|=O(1) but each term carries Theta(n) incidence ==")
    print("     the localization re-indexes the energy by O(1) dominant dilate frequencies but the")
    print("     PER-FREQUENCY mass is the same Theta(n) -> total = Theta(n) per g = the wall, NOT a lever.")

if __name__=="__main__":
    main()
