#!/usr/bin/env python3
"""
wf407w2_D2-gspec_genuine_g_spectrum.py  --  #407 thread D2-gspec (T09 follow-up).

DECISIVE QUESTION.  Wave-1 T09 reported: the product-unit  g = (x1*x2)/(y1*y2)  of GENUINE E_2
defects (x1+x2 == y1+y2 mod p, {x1,x2}!={y1,y2}, NOT antipodal) lands in "only 4-6 clustered
values, all in mu_n".  IF |g-spectrum| = O(1) independent of n, the genuine-defect count could
re-localize to a BOUNDED union  sum_{g in Gset} |mu_n cap g*mu_n|  over a FIXED small g-set --
a potential route AROUND the additive-energy wall.

WE MEASURE EXACTLY (full enumeration, no sampling) at n=8,16,32,64:
  (1) The g-spectrum of GENUINE defects: distinct count |G|, multiplicities, and whether
      G subset mu_n.  Track vs n and vs beta (p ~ n^beta).
  (2) Orbit/coset structure of G: closure under inversion (g -> g^{-1}), under the Galois group
      Gal(Q(zeta_n)/Q) acting as g -> g^k for k coprime to n (= multiplier h^j on the subgroup),
      under negation (g -> -g).  Is G a single coset / orbit, or a union of subgroup cosets?
  (3) GROWTH: does |G| stay O(1) as n: 8->16->32->64, or grow?  Compare to n, sqrt(n), the
      genuine-defect count itself, and the energy excess E2^(p)-E2^(0).
  (4) THE LEVER TEST: compute  sum_{g in G} |mu_n cap g*mu_n|  and compare to the genuine count
      and to the FULL energy excess.  If the localized sum << excess we have a real lever; if it
      RECOVERS the excess (Cauchy-Schwarz floor) it inherits the wall.

Honesty: genuine (nonzero-sum, non-antipodal) defects only exist when the char-p energy EXCESS
is positive, i.e. at SUB-prize beta (small p relative to the r=2 onset 4^{n/2}).  At prize beta
the excess -> 0 and there are NO genuine defects.  So the g-spectrum is a sub-prize object; we
report its scaling and ask whether the localization mechanism, even where it exists, beats the
wall.
"""
import math
from collections import defaultdict, Counter

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
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
    """nonzero-sum, non-antipodal off-diagonal E2 collisions (unordered pairs of distinct reps)."""
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
                # drop antipodal (char-0 Lam-Leung): {-y1,-y2}=={x1,x2}
                if frozenset(((p-y1)%p,(p-y2)%p))==frozenset((x1,x2)): continue
                out.append((x1,x2,y1,y2,s))
    return out

def dilate_incidence(p, muset, g):
    """|mu_n cap g*mu_n|."""
    return sum(1 for x in muset if (g*x)%p in muset)

def orbit_structure(p, n, h, G, muset):
    """Classify G under inversion, Galois (g->g^k, gcd(k,n)=1), and negation."""
    Gset=set(G)
    inv_closed = all(pow(g,-1,p) in Gset for g in Gset)
    neg_closed = all((p-g)%p in Gset for g in Gset)
    in_mu = all(g in muset for g in Gset)
    # Galois orbits within mu_n: g and g^k (k coprime to n) are conjugate.  Represent each g in mu_n
    # by its discrete log j (g = h^j); Galois acts j -> k*j mod n, k in (Z/n)^*.
    logmap={}
    cur=1
    for j in range(n):
        logmap[cur]=j; cur=(cur*h)%p
    ks=[k for k in range(1,n) if math.gcd(k,n)==1]
    galois_orbits=set()
    if in_mu:
        seen=set()
        for g in Gset:
            j=logmap[g]
            orb=frozenset((k*j)%n for k in ks)
            galois_orbits.add(orb)
        # is G a UNION of full Galois orbits restricted to its logs?
    return dict(inv_closed=inv_closed, neg_closed=neg_closed, in_mu=in_mu,
                logs=sorted(logmap[g] for g in Gset) if in_mu else None,
                n_galois_orbits=len(galois_orbits))

def main():
    print("="*120)
    print("D2-gspec: genuine-E2-defect product-unit g-spectrum  --  growth, orbit structure, lever test")
    print("="*120)
    rows=[]
    for n in (8,16,32,64):
        E0=3*n*n-3*n
        for beta in (2.0, 2.2, 2.4):
            p=smallest_prime_1_mod(n,int(n**beta))
            S,h=subgroup(p,n); muset=set(S)
            Ep=E2(p,muset)
            excess=Ep-E0
            gen=genuine_defects(p,n,S)
            ng=len(gen)
            if ng==0:
                print(f" n={n:3d} beta={beta} p={p:>10d} (2^{math.log2(p):4.1f}): "
                      f"excess={excess:5d}  #genuine=0  (no g-spectrum)")
                continue
            prodg=Counter()
            for (x1,x2,y1,y2,s) in gen:
                g=(x1*x2%p)*pow(y1*y2%p,-1,p)%p
                prodg[g]+=1
            G=list(prodg)
            struct=orbit_structure(p,n,h,G,muset)
            # LEVER: sum over g-set of dilate incidence
            lever=sum(dilate_incidence(p,muset,g) for g in G)
            # full-energy floor for comparison: excess (this is the genuine count over all g)
            print(f" n={n:3d} beta={beta} p={p:>10d} (2^{math.log2(p):4.1f}): "
                  f"excess={excess:5d}  #genuine={ng:5d}  |G|={len(G):3d}  "
                  f"G<=mu_n:{struct['in_mu']!s:5}  inv-closed:{struct['inv_closed']!s:5}  "
                  f"neg-closed:{struct['neg_closed']!s:5}  #galois-orbits={struct['n_galois_orbits']}  "
                  f"sum_g|mu cap g*mu|={lever}")
            if struct['in_mu']:
                print(f"        G logs (g=h^j): {struct['logs']}   multiplicities: {sorted(prodg.values(),reverse=True)}")
            rows.append((n,beta,len(G),ng,excess,lever,struct))
    print("\n"+"="*120)
    print("GROWTH TABLE   (does |G| stay O(1) as n grows?)")
    print(f"   {'n':>4} {'beta':>5} {'|G|':>5} {'#genuine':>9} {'excess':>7} {'|G|/n':>7} {'|G|/sqrt(n)':>11} {'lever/excess':>12}")
    for (n,beta,gG,ng,exc,lev,st) in rows:
        print(f"   {n:>4} {beta:>5} {gG:>5} {ng:>9} {exc:>7} {gG/n:>7.3f} {gG/math.sqrt(n):>11.3f} "
              f"{(lev/exc if exc else 0):>12.3f}")
    print("\nVERDICT KEYS:")
    print("  * |G| stays bounded (O(1))  <=>  |G|/n -> 0 AND absolute |G| flat across n=8..64.")
    print("  * lever = sum_g |mu cap g*mu|.  If lever ~ excess => Cauchy-Schwarz floor recovered = WALL.")
    print("    If lever << excess with |G|=O(1) => genuine lever AROUND the wall.")

if __name__=="__main__":
    main()
