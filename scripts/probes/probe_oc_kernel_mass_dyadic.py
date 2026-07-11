#!/usr/bin/env python3
"""
Opus-core CORE probe #2 (#509): the KERNEL-CLASS MASS S0 = repRF(0) at dyadic n.

S0 = #{ (t_1..t_r) in (Z/n)^r : g^{t_1}+...+g^{t_r} = 0 in F_q }.

G88's kernel floor  q*S0^2 - n^{2r} <= centeredShadowMass  makes S0 the single
most important scalar. The question: at DYADIC n (g^m=-1, antipodal roots), does
S0 have a THINNESS-FORCED lower bound / exact value from antipodal pairing that a
generic subgroup lacks?

Antipodal fact: since g^{j+m} = -g^j, every root x has -x = g^{j+m} also a root.
So any tuple can be paired with its 'antipodal partner set'. For EVEN r, pairing
each of r/2 indices with its antipode gives a zero-sum: choose j_1..j_{r/2} freely
(n^{r/2} ways) and set the other r/2 to j_i+m. That produces
   x_1 + (-x_1) + x_2 + (-x_2) + ... = 0
for ANY assignment -> but we must count ORDERED tuples with the antipodal partner
placed anywhere. This gives a COMBINATORIAL LOWER BOUND on S0 independent of q,
purely from the 2-power (antipodal) structure. Let's measure it exactly and see:
  - is the antipodal-pairing count a genuine lower bound for S0?
  - does it match S0 at production-ish p (q large) or is S0 strictly larger?
  - how does it compare to the generic-subgroup expectation n^r / q ?
"""
import itertools, math
from collections import Counter

def is_prime(x):
    if x<2: return False
    for d in range(2,int(x**0.5)+1):
        if x%d==0: return False
    return True

def find_gen(p,n):
    if (p-1)%n!=0: return None
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
            for rt in roots:
                nxt[(v+rt)%p]+=cv
        cur=nxt
    return cur.get(0,0)

def antipodal_pairing_count(n,r):
    """Number of ordered r-tuples of indices in Z/n that can be perfectly matched
    into antipodal pairs (i, i+m). Only nonzero for even r. This is a q-INDEPENDENT
    count forced purely by g^m=-1: any such tuple sums to 0.
    Count = number of ways to: choose a perfect matching of r positions into r/2
    pairs, assign each pair an index j in Z/n (the pair is {g^j, -g^j} = zero).
    But positions are ordered and within a matched pair the two entries are j and j+m
    (distinguishable), so we count ordered tuples t in (Z/n)^r such that the multiset
    {g^{t_i}} is antipodally self-cancelling. Easiest: directly count tuples whose
    root-multiset is closed under negation with equal multiplicities. We MEASURE it."""
    if r%2!=0: return 0
    m=n//2
    # brute for small n,r: count ordered tuples whose multiset of roots is antipodal-balanced
    cnt=0
    for t in itertools.product(range(n),repeat=r):
        # multiset of root indices; balanced iff for every index j, count(j)==count(j+m)
        c=Counter(t)
        ok=all(c[j]==c[(j+m)%n] for j in range(n))
        if ok: cnt+=1
    return cnt

def analyze(p,n,r):
    g=find_gen(p,n)
    if g is None: return None
    S0=S0_exact(p,g,n,r)
    ap = antipodal_pairing_count(n,r) if (r%2==0 and n<=8) else None
    generic = (n**r)/p  # heuristic mean of repRF(0) if r-sums uniform over F_q
    return dict(p=p,n=n,r=r,S0=S0,antipodal_lb=ap,generic_mean=generic,
                S0_ge_ap=(ap is not None and S0>=ap),
                S0_eq_ap=(ap is not None and S0==ap))

if __name__=="__main__":
    print("="*90)
    print("KERNEL-CLASS MASS S0 = repRF(0) vs ANTIPODAL-PAIRING lower bound (dyadic thinness)")
    print("="*90)
    print(f"{'p':>6} {'n':>3} {'r':>2} {'S0':>8} {'antipodal_LB':>13} {'generic n^r/q':>13} {'S0>=AP':>7} {'S0==AP':>7}")
    print("-"*70)
    rows=[]
    for n in [4,8]:
        for r in [2,4]:
            for p in [x for x in range(17,600) if is_prime(x) and (x-1)%n==0][:5]:
                res=analyze(p,n,r)
                if res:
                    rows.append(res)
                    print(f"{res['p']:>6} {res['n']:>3} {res['r']:>2} {res['S0']:>8} {str(res['antipodal_lb']):>13} {res['generic_mean']:>13.2f} {str(res['S0_ge_ap']):>7} {str(res['S0_eq_ap']):>7}")
    print()
    # focus: does S0 - antipodal_LB scale with n^r/q (the generic part) as q grows?
    print("SCALING TEST (n=4,r=2): S0, antipodal_LB, residual S0-AP, and (residual)*q/n^r")
    ap42=antipodal_pairing_count(4,2)
    print(f"antipodal_LB(4,2) = {ap42}")
    for p in [x for x in range(17,4000) if is_prime(x) and (x-1)%4==0][:12]:
        g=find_gen(p,4); 
        if g is None: continue
        S0=S0_exact(p,g,4,2)
        resid=S0-ap42
        print(f"  p={p:>5} S0={S0:>4} resid={resid:>4} resid*q/n^r={resid*p/16:>8.2f}")
    print()
    print("INTERPRETATION:")
    print(" - If S0 == antipodal_LB EXACTLY at all large p: S0 is a THINNESS-FORCED constant")
    print("   (q-independent), a genuine dyadic invariant -> pins the kernel floor exactly.")
    print(" - If S0 = antipodal_LB + O(n^r/q) generic tail: dyadic gives the DOMINANT term,")
    print("   the rest is equidistribution -> still a structural decomposition worth a theorem.")
