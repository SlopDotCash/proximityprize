#!/usr/bin/env python3
"""
C042 attack: "cross-parity defect A=-g.B and Conj-1.12 anti-spreading are DUAL halves of one
subset-sum image S0".  Test the three concrete claims at PROPER subgroups (prize regime),
NEVER the full group.

S0 := image of the distinct-element floor(b/2)-fold subset-sum of a subgroup G = mu_b.
The connection studies the cross-parity defect on mu_{n/2}-subset-sums (A,B over mu_{n/2}),
so I take G = mu_n (the FFT subgroup), and S0 = sumsetDistinct(mu_{n/2}, (n/2)/2 ... ).
Actually the connection's S0 is the (mu_{n/2}-subset-sum image).  I instantiate S0 two ways
and check both, to be faithful:
  (S0a) S0 = full subset-sum image of mu_n  (all subset sizes) -- the "subset-sum image"
  (S0b) S0 = distinct floor(b/2)-fold sumset of mu_n  (the Conj-1.12 object exactly)

CLAIMS:
  C1 (IDENTITY): #{cross-parity defects} =?= |S0 cap (-g)S0|.  The "cross-parity defect" =
     #{(A,B) in (subset-sums)^2, A=-g B mod q} where A,B range over the subset-sum image with
     multiplicity? or as SETS?  The RESULTS text says "#cross-parity-defects = |S0 cap (-g)S0|"
     i.e. as a SET self-intersection under dilate.  I compute |S0 cap (-g)S0| for varying g and
     compare to the count of additive-energy defects that are cross-parity (A=-gB).
  C2 (ANTI-CORRELATION): across many proper-subgroup primes, is |S0 cap (-g)S0|/|S0| LARGE
     exactly when |S0|/q -> 1 ?  (claim: worst self-intersection when S0 fills F_q)
  C3 (DUAL / sum-product): is |S0 cap (-g)S0| a genuine NEW handle (small for some g, giving
     a usable floor) or does it just track |S0|^2/q (a pure cardinality artifact = no structure
     beyond size) ?  If |S0 cap (-g)S0| ~ |S0|^2/q for ALL g (random-like), the "self-
     intersection" is NOT an independent lever -- it is determined by |S0| -> NOT dual halves,
     just two views welded to the same |S0|/BGK wall.
"""
import math, random
from itertools import combinations

def is_prime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        if m%q==0: return m==q
    d=m-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1):continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True

def factorize(m):
    s=set();d=2
    while d*d<=m:
        while m%d==0:s.add(d);m//=d
        d+=1
    if m>1:s.add(m)
    return s

def gen_Fp_star(p):
    F=factorize(p-1)
    for h in range(2,p):
        if all(pow(h,(p-1)//q,p)!=1 for q in F): return h
    return None

def find_prime(n, beta):
    """smallest prime q ~ n^beta with n | q-1 (proper subgroup mu_n exists, large prime)."""
    lo=int(n**beta);
    p = lo - (lo % n) + 1
    if p<lo: p+=n
    for _ in range(200000):
        if is_prime(p): return p
        p+=n
    return None

def subgroup(p, n):
    g0=gen_Fp_star(p)
    gen=pow(g0,(p-1)//n,p)
    return [pow(gen,i,p) for i in range(n)], g0

def subsetsum_image_full(mu, p):
    """all subset sums (every cardinality) of mu, as a SET in F_q. via subset-sum DP over set."""
    reach={0}
    for x in mu:
        reach |= {(v+x)%p for v in reach}
    return reach

def sumsetDistinct_card(mu, ell, p, cap=400000):
    """distinct ell-fold sumset image |{ sum of ell distinct elts of mu }|.  brute for small n."""
    n=len(mu)
    if math.comb(n,ell) > cap:
        # sample to estimate, but we keep n small so this won't trigger for n<=20
        S=set()
        seen=set()
        for _ in range(cap):
            T=tuple(sorted(random.sample(range(n),ell)))
            if T in seen: continue
            seen.add(T)
            S.add(sum(mu[i] for i in T)%p)
        return S, True  # sampled
    S=set()
    for T in combinations(range(n),ell):
        S.add(sum(mu[i] for i in T)%p)
    return S, False

def dilate_intersection(S, g, p):
    gS={(g*v)%p for v in S}
    return len(S & gS)

print("="*108)
print("C042: cross-parity self-intersection |S0 cap (-g)S0| vs |S0| (proper subgroups, prize regime)")
print("="*108)

random.seed(1)
rows=[]
for (n,beta) in [(8,4.0),(8,5.0),(16,4.0),(16,4.5),(32,4.0),(16,5.0)]:
    p=find_prime(n,beta)
    if p is None:
        print(f"n={n} beta={beta}: no prime"); continue
    mu,g0=subgroup(p,n)
    negg=(p-g0)%p   # -g  (g = primitive root); the dilate factor in the connection
    # S0a = full subset-sum image of mu_n
    S0a=subsetsum_image_full(mu,p)
    # S0b = Conj-1.12 object: distinct floor(n/2)-fold sumset of mu_n
    ell=n//2//2 if n>=8 else 1   # floor(b/2) of the order-(n/2) view; use floor(n/2) for the mu_n object
    ell=n//2
    S0b,sampled=sumsetDistinct_card(mu,ell,p)
    fillA=len(S0a)/p
    fillB=len(S0b)/p
    # self-intersection under -g dilate, and under a RANDOM dilate (control), for both S0
    def stats(S):
        gg=dilate_intersection(S,negg,p)
        # random dilate control: average over a few random units
        ctrl=[]
        for _ in range(8):
            h=random.randrange(1,p)
            ctrl.append(dilate_intersection(S,h,p))
        ctrl_avg=sum(ctrl)/len(ctrl)
        expected_random=len(S)*len(S)/p   # if S,gS independent: |S inter gS| ~ |S|^2/q
        return gg, ctrl_avg, expected_random
    a_gg,a_ctrl,a_exp=stats(S0a)
    b_gg,b_ctrl,b_exp=stats(S0b)
    print(f"\n--- n={n} q={p} (q~n^{math.log(p)/math.log(n):.2f})  -g={negg} ---")
    print(f"  S0a=full subset-sum image:  |S0a|={len(S0a):>7d}  fill={fillA:.4f}")
    print(f"     |S0a cap (-g)S0a| = {a_gg:>7d}   rand-dilate avg = {a_ctrl:8.1f}   |S0a|^2/q = {a_exp:8.1f}")
    print(f"  S0b=distinct {ell}-fold sumset: |S0b|={len(S0b):>7d}  fill={fillB:.4f}  {'(SAMPLED)' if sampled else ''}")
    print(f"     |S0b cap (-g)S0b| = {b_gg:>7d}   rand-dilate avg = {b_ctrl:8.1f}   |S0b|^2/q = {b_exp:8.1f}")
    rows.append((n,p,fillA,a_gg,a_exp,a_ctrl,fillB,b_gg,b_exp,b_ctrl))

print("\n" + "="*108)
print("ANTI-CORRELATION & DUALITY TEST")
print("="*108)
print("If |S0 cap (-g)S0| ~ |S0|^2/q AND ~ rand-dilate-avg for ALL primes, then the self-")
print("intersection is DETERMINED BY |S0| (no independent multiplicative lever): the two 'faces'")
print("collapse to one cardinality |S0| -> NOT dual halves, welds to the |S0|/BGK wall.")
print()
print("  n |    q     | fillA  | -g-int | |S|^2/q | rand-avg | ratio(-g/exp) | ratio(rand/exp)")
for (n,p,fA,agg,aexp,actrl,fB,bgg,bexp,bctrl) in rows:
    r1=agg/aexp if aexp else float('nan')
    r2=actrl/aexp if aexp else float('nan')
    print(f"  {n:>2d}| {p:>9d}| {fA:.4f} | {agg:>6d} | {aexp:7.1f} | {bctrl if False else actrl:8.1f} | {r1:13.3f} | {r2:.3f}")
