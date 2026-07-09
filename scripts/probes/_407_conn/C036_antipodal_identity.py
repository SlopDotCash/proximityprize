"""
C036: confirm the vanishing-power-sum subset count = Lam-Leung antipodal count,
and probe the genuinely WINDOW-INTERIOR (large-gap t) regime.

(I)  For t=2 (only p_1=0, i.e. sum-zero a-subsets of mu_{2^mu}): by Lam-Leung the only
     vanishing sums of 2-power roots are antipodal pairings, so a sum-zero a-subset must be
     a disjoint union of a/2 antipodal pairs {x,-x}. There are n/2 such pairs, so
        #{S:|S|=a,p_1=0} = C(n/2, a/2)   (a even), 0 (a odd).
     This is an EXACT binomial = an energy count, NOT O(n). Verify.

(II) Window-interior: t large (many constraints p_1=...=p_{t-1}=0). The floor claims #var=O(n)
     there. Check whether the count drops to O(n)/empty as t grows, and at what gap. This is
     the "deep window empty / thin crossover band" claim --- but proving it is exactly bounding
     the high-order simultaneous vanishing = the deep-moment Lam-Leung rigidity (the open core).
"""
import itertools
from math import comb, gcd

def is_prime(m):
    if m<2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%p==0: return m==p
    d=m-1;r=0
    while d%2==0: d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def find_q(n,beta_min=4):
    target=n**beta_min; k=target//n
    while k*n+1 < n*target*256:
        q=k*n+1
        if is_prime(q): return q
        k+=1
    return None

def subgroup(n,q):
    def order(a):
        o=1;x=a
        while x!=1: x=x*a%q;o+=1
        return o
    g=None
    for c in range(2,q):
        if order(c)==q-1: g=c;break
    h=pow(g,(q-1)//n,q)
    S=[];x=1
    for _ in range(n): S.append(x);x=x*h%q
    return S

def psum(sub,j,q): return sum(pow(x,j,q) for x in sub)%q

print("=== (I) t=2 sum-zero count vs antipodal binomial C(n/2, a/2) ===")
for n in (8,16,32):
    q=find_q(n,4); S=subgroup(n,q)
    for a in (2,4,6):
        if a>n: continue
        cnt=sum(1 for idx in itertools.combinations(range(n),a)
                if psum([S[i] for i in idx],1,q)==0)
        pred = comb(n//2, a//2) if a%2==0 else 0
        print(f"  n={n} a={a}: #sumzero={cnt}  C(n/2,a/2)={pred}  match={cnt==pred}")

print("\n=== (II) window-interior: how #var(a,t) decays as gap t grows ===")
for n in (16,32):
    q=find_q(n,4); S=subgroup(n,q)
    print(f"  n={n} q={q}:")
    for a in range(2,min(n,9)):
        row=[]
        for t in range(2,a+1):
            cnt=sum(1 for idx in itertools.combinations(range(n),a)
                    if all(psum([S[i] for i in idx],j,q)==0 for j in range(1,t)))
            row.append((t,cnt))
        # report only nonzero & whether O(n)
        rstr=" ".join(f"t={t}:{c}" for t,c in row if c>0)
        print(f"    a={a}: {rstr}")
