#!/usr/bin/env python3
"""
Opus-core CORE probe #3 (#509): EXACT formula + p-threshold for the dyadic kernel mass.

Confirmed empirically: for dyadic n (g^m=-1) and p above a saturation threshold,
S0 = repRF(0) = A(n,r) := #{ t in (Z/n)^r : multiset {g^{t_i}} is antipodally balanced }
                        = #{ t : forall j, #{i: t_i=j} = #{i: t_i=j+m} }.

Goals:
  1. closed form for A(n,r). Claim: A(n,r) = sum over pairings. For the antipodal-balanced
     condition, group the n indices into m antipodal PAIRS P_j={j, j+m}, j=0..m-1.
     A tuple is balanced iff within each pair the two indices appear equally often.
     Ordered count = sum over (k_0,...,k_{m-1}) with sum 2k_j = r of
        multinomial(r; k_0,k_0,k_1,k_1,...) = r! / prod (k_j!)^2.
     => A(n,r) = [z^r-ish] ... = coefficient extraction; verify numerically.
  2. Also: is A(n,r) = the constant term of (sum_j (x_j + x_j^{-1}))^r under the torus,
     i.e. the number of closed walks -> A(n,r) = sum_{k: |k|... } . Equivalent:
     A(n,r) = r! * [coeff] of prod I-like. We just verify the multinomial sum.
  3. p-threshold p*(n,r): smallest prime above which S0 == A(n,r) stably.
     (Below p*, extra 'accidental' char-p zero-sums inflate S0 = the SYZ53 artifact.)
  4. Thinness-essential check: for ODD n there are NO antipodes; the analogous
     'balanced' count is 0 for the same pairing, yet S0 != 0 generically -> so the
     dyadic formula is SPECIFIC to the 2-power subgroup. Confirm S0(odd n) is NOT given
     by any antipodal formula and instead tracks generic n^r/q asymptotically.
"""
import itertools, math
from collections import Counter
from math import comb, factorial

def is_prime(x):
    if x<2:return False
    for d in range(2,int(x**0.5)+1):
        if x%d==0:return False
    return True

def find_gen(p,n):
    if (p-1)%n!=0:return None
    def order(a):
        o=1;x=a%p
        while x!=1:
            x=(x*a)%p;o+=1
            if o>p:return None
        return o
    for a in range(2,p):
        if order(a)==p-1:
            g=pow(a,(p-1)//n,p)
            if order(g)==n and (n%2==1 or pow(g,n//2,p)==p-1):
                return g
    return None

def S0_exact(p,g,n,r):
    roots=[pow(g,t,p) for t in range(n)]
    cur=Counter({0:1})
    for _ in range(r):
        nxt=Counter()
        for v,cv in cur.items():
            for rt in roots: nxt[(v+rt)%p]+=cv
        cur=nxt
    return cur.get(0,0)

def A_formula(n,r):
    """Closed form via multinomial sum over pair-occupancy (k_0..k_{m-1}), sum 2k_j=r."""
    if r%2!=0: return 0  # odd r cannot antipodally balance
    m=n//2
    R=r//2
    total=0
    # distribute R 'pairs-worth' : need k_0+..+k_{m-1}=R, term = r!/ prod (k_j!)^2
    for ks in itertools.combinations_with_replacement(range(m),0):  # placeholder
        pass
    # iterate compositions of R into m nonneg parts
    def compositions(total_sum,parts):
        if parts==1:
            yield (total_sum,); return
        for first in range(total_sum+1):
            for rest in compositions(total_sum-first,parts-1):
                yield (first,)+rest
    for ks in compositions(R,m):
        denom=1
        for k in ks: denom*=factorial(k)**2
        total+=factorial(r)//denom
    return total

if __name__=="__main__":
    print("="*80)
    print("EXACT A(n,r) formula vs brute antipodal count vs stabilized S0")
    print("="*80)
    # verify formula matches brute antipodal count and stabilized S0
    for n in [4,8]:
        m=n//2
        for r in [2,4,6]:
            Af=A_formula(n,r)
            # stabilized S0 at a large-enough prime
            ps=[x for x in range(200,6000) if is_prime(x) and (x-1)%n==0][:3]
            s0s=[]
            for p in ps:
                g=find_gen(p,n)
                if g: s0s.append(S0_exact(p,g,n,r))
            print(f"n={n} r={r}: A_formula={Af:>7}  stabilized_S0={s0s}  match={all(s==Af for s in s0s)}")
    print()
    print("p-THRESHOLD p*(n,r): smallest prime above which S0==A(n,r) stays stable")
    for n in [4,8]:
        for r in [2,4,6]:
            Af=A_formula(n,r)
            pstar=None; ok_streak=0
            for p in [x for x in range(5,8000) if is_prime(x) and (x-1)%n==0]:
                g=find_gen(p,n)
                if not g: continue
                s0=S0_exact(p,g,n,r)
                if s0==Af:
                    ok_streak+=1
                    if ok_streak>=4 and pstar is None:
                        pstar=p_first_stable
                else:
                    ok_streak=0; pstar=None
                if ok_streak==1: p_first_stable=p
            print(f"n={n} r={r}: A={Af:>7}  p* (stable from) = {pstar}")
    print()
    print("THINNESS-ESSENTIAL: ODD n has A=0 for odd r and NO antipodal balancing.")
    print("Compare S0(odd n) to any antipodal formula:")
    for n in [3,5]:
        for r in [2,3,4]:
            ps=[x for x in range(200,6000) if is_prime(x) and (x-1)%n==0][:3]
            s0s=[]
            for p in ps:
                g=find_gen(p,n)
                if g: s0s.append((p,S0_exact(p,g,n,r)))
            print(f"  odd n={n} r={r}: (p,S0)={s0s}  <- varies with p (generic ~ (n^r-?)/q), NOT a dyadic constant")
