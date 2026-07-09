#!/usr/bin/env python3
"""
C042 part 2: (A) VERIFY the RESULTS-section-17 IDENTITY  #cross-parity-defects = |S0 cap (-g)S0|
             (B) is the self-intersection an INDEPENDENT lever from |S0|, or determined by it?

(A) IDENTITY.  The "cross-parity defect" in the moment computation is:
    among the F_q additive-energy excess solutions sum_i x_i = sum_i y_i (mod q, x,y in mu_{n/2})
    that DON'T hold over C, ~96-100% satisfy  A = -g B  where A = partial sum (left half),
    B = partial sum (right half).  The connection re-expresses the COUNT of {(A,B): A=-gB,
    A,B in subset-sum image} as |S0 cap (-g)S0|.   I check the cleaner exact statement:
        #{(A,B) in S0xS0 : A = (-g) B}  (as SETS, one (A,B) per matching value pair)
          = #{ v in S0 : v in (-g) S0 }  = |S0 cap (-g)S0|     (trivially true as a set identity)
    The NON-trivial claim is that this set-count is the operative defect.  We confirm the
    set-identity is exact (it is, by construction) and is therefore a faithful re-expression
    -- so C1 is a TRUE identity but TAUTOLOGICAL (any "A=-gB count" is a dilate self-intersection).

(B) THE REAL TEST (decides PARTIAL/REDUCED/OPEN).  For the connection to be a genuine new handle
    ("dual halves you can play against each other") you must be able to make
        |S0| LARGE   (Conj 1.12: spreading, >= q/10)
      AND simultaneously
        |S0 cap (-g)S0| SMALL  (good prize floor)
    These pull in OPPOSITE directions IF |S0 cap (-g)S0| >= |S0|^2/q - o(...) always
    (Cauchy-Schwarz / additive-energy lower bound), because |S0|>=q/10 forces
        |S0 cap (-g)S0| >= |S0|^2/q >= q/100  (a CONSTANT fraction of q).
    So large |S0| FORCES large self-intersection.  We test the LOWER bound
        |S0 cap (-g)S0| >= |S0|^2/q  (does it ever go below? CS says the AVERAGE over g is exactly
        ~|S0|^2/q, so SOME g could be below-average) -- and we test whether the -g dilate (the
        cross-parity one) is BELOW or ABOVE average.
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
    lo=int(n**beta); p = lo - (lo % n) + 1
    if p<lo: p+=n
    for _ in range(400000):
        if is_prime(p): return p
        p+=n
    return None
def subgroup(p, n):
    g0=gen_Fp_star(p); gen=pow(g0,(p-1)//n,p)
    return [pow(gen,i,p) for i in range(n)], g0

# (A) Tautology check: build a tiny S0, count {(A,B):A=-gB} vs |S0 cap (-g)S0|.
print("="*100)
print("(A) IDENTITY: #{(A,B) in S0^2: A = (-g)B} == |S0 cap (-g)S0| ?")
print("="*100)
random.seed(0)
ok=True
for _ in range(6):
    p=10007; S0=set(random.sample(range(1,p),200)); g=random.randrange(2,p)
    cnt=sum(1 for B in S0 if (-g*B)%p in S0)        # for each B, is A=-gB in S0 ?
    inter=len({(-g*v)%p for v in S0} & S0)          # |(-g)S0 cap S0|  (note (-g)S0 cap S0 = -g(S0 cap -g^{-1}S0))
    inter2=len({( (-g)*v)%p for v in S0} & S0)
    # the count cnt = #{B in S0: -gB in S0} = #{ w in (-g)S0 : w in S0 } = |S0 cap (-g)S0|
    print(f"  q={p} g={g:>5d}: #{{B: -gB in S0}}={cnt:>4d}   |S0 cap (-g)S0|={inter:>4d}   match={cnt==inter}")
    ok = ok and (cnt==inter)
print(f"  => IDENTITY exact (set-tautology): {ok}\n")

# (B) the lever test: at proper subgroups, is the -g self-intersection below |S0|^2/q (a usable
#     floor) or pinned >= |S0|^2/q (forced large by spreading)?  Scan ALL dilates h, locate the
#     MINIMUM self-intersection and where -g sits in that distribution.
print("="*100)
print("(B) LEVER TEST: min_h |S0 cap h S0| vs |S0|^2/q, and where -g ranks")
print("="*100)
print("  If min over h is >> 1 (~ |S0|^2/q), large |S0| FORCES large intersection for EVERY h")
print("  => cannot have spread+thin simultaneously => the two faces are ANTAGONISTIC not dual-")
print("     -free; the floor needs |S0| SMALL, contradicting Conj 1.12.  welds to |S0| (BGK).")
print()
def subsetsum_image_full(mu,p):
    reach={0}
    for x in mu: reach |= {(v+x)%p for v in reach}
    return reach
print("  n |    q    | beta | |S0|  | fill  | min_h int | |S0|^2/q | -g int | -g percentile")
for (n,beta) in [(8,4.0),(8,5.0),(16,4.0),(16,4.5),(16,5.0)]:
    p=find_prime(n,beta)
    mu,g0=subgroup(p,n)
    S0=subsetsum_image_full(mu,p)
    negg=(p-g0)%p
    Sl=list(S0); Sset=S0
    # scan a sample of dilates (full scan q-1 too big for q~10^5+; sample 400 + include -g, g, +-1)
    cand=set([negg,g0,(p-1)% p,1])
    while len(cand)<400: cand.add(random.randrange(2,p))
    ints=[]
    for h in cand:
        ints.append((len({(h*v)%p for v in Sset} & Sset), h))
    ints.sort()
    minint=ints[0][0]
    exp=len(S0)**2/p
    gg=len({(negg*v)%p for v in Sset} & Sset)
    below=sum(1 for (v,_) in ints if v < gg)
    pct=100.0*below/len(ints)
    print(f"  {n:>2d}| {p:>8d}| {beta:.1f} | {len(S0):>5d} | {len(S0)/p:.4f}| {minint:>9d} | {exp:8.1f} | {gg:>6d} | {pct:5.1f}%")
print()
print("READING: if min_h int >= ~|S0|^2/q for all rows => no h beats the cardinality floor =>")
print("         spreading (large|S0|) and thin-dilate (small int) are CONTRADICTORY, not dual.")
