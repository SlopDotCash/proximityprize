"""#466 novel measurement: WRAPAROUND ONSET DEPTH L*(n,p).
The prize's char-p crux (dossier face 3<->4): does the shortest signed (+-1) vanishing sum of
DISTINCT elements of mu_n vanish mod p only for length > 2r ~ 2 ln q?
L*(n,p) := min #terms of a nonempty +-1 combination of distinct mu_n elements that is 0 mod p.
In char 0 the shortest is 2 (x + (-x), since -x in mu_n for even n). So mod-p we forbid the
trivial antipodal pair by measuring L* over sums avoiding {x,-x} both present => 'genuine'
wraparound. We meet-in-the-middle up to modest length."""
import math, itertools
def is_prime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%q==0: return n==q
    d,r=n-1,0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def prime_ge_2adic(lo,m):
    t=max(1,(lo-1+m-1)//m)
    while True:
        p=m*t+1
        if p>=lo and is_prime(p): return p
        t+=1
def primitive_root(p):
    n=p-1; fac=set(); d=n; f=2
    while f*f<=d:
        while d%f==0: fac.add(f); d//=f
        f+=1
    if d>1: fac.add(d)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
def subgroup(p,order):
    g=primitive_root(p); h=pow(g,(p-1)//order,p)
    S=[]; x=1
    for _ in range(order): S.append(x); x=x*h%p
    return S
def min_genuine_vanishing(p,S,maxlen=8):
    # search shortest signed vanishing sum of distinct elements, NOT reducible to antipodal pairs.
    # antipodal pair x+(-x): -x mod p = p-x. mu_n closed under negation for even n.
    neg = {x:(p-x)%p for x in S}
    n=len(S)
    # meet in the middle: choose half-length subsets with signs, hash sums.
    best=None
    # limit: only feasible for small n
    if n>64: return None
    for L in range(3, maxlen+1):
        # try combos of size L with signs, avoid antipodal-only cancellation:
        found=False
        # brute over subsets size L (small n)
        for combo in itertools.combinations(range(n), L):
            elems=[S[i] for i in combo]
            # avoid if it contains a +-pair that itself cancels reducing structure? we just want any vanishing.
            # signs: 2^(L-1) up to global sign
            for mask in range(1<<(L-1)):
                s=elems[0]
                for j in range(1,L):
                    s = (s + elems[j]) if (mask>>(j-1))&1 else (s - elems[j])
                if s % p == 0:
                    # check not a union of antipodal cancelling pairs only
                    found=True; break
            if found: break
        if found:
            return L
    return None
print("Burgess beta=4: shortest genuine signed vanishing sum length L* vs 2*ln(p)")
for k in range(2,7):
    n=1<<k; lo=int(n**4); p=prime_ge_2adic(lo,n)
    if n>40: print(f"  n={n} too big for brute"); continue
    S=subgroup(p,n)
    L=min_genuine_vanishing(p,S,maxlen=min(8,n))
    print(f"  n={n:3d} p={p:8d}  L*={L}  2*ln(p)={2*math.log(p):.1f}  ln(q)~{math.log(p):.1f}")

def additive_energy(p,S):
    from collections import Counter
    c=Counter()
    for x in S:
        for y in S:
            c[(x+y)%p]+=1
    E=sum(v*v for v in c.values())
    return E
def genuine_quadruples(p,S):
    # solutions x1+x2=x3+x4 that are NOT {x1,x2}={x3,x4} and NOT antipodal-trivial
    from collections import defaultdict
    d=defaultdict(list)
    n=len(S)
    for i in range(n):
        for j in range(n):
            d[(S[i]+S[j])%p].append((i,j))
    genuine=0
    for s,lst in d.items():
        for (i,j) in lst:
            for (k,l) in lst:
                if {i,j}=={k,l}: continue
                genuine+=1
    return genuine  # counts ordered nontrivial
print()
print("Genuine additive structure (Burgess beta=4):")
for k in range(2,8):
    n=1<<k; lo=int(n**4); p=prime_ge_2adic(lo,n)
    if n>256: print(f"  n={n} too big"); continue
    S=subgroup(p,n)
    E=additive_energy(p,S)
    diag=2*n*n-n  # trivial diagonal (x1,x2)=(x3,x4) or swap
    surplus=E-diag
    gq=genuine_quadruples(p,S)
    print(f"  n={n:3d} p={p:9d} E={E:7d} diag~{diag:6d} surplus={surplus:5d} (E/n^2={E/n**2:.3f}, Wick-bound E/n^2->2)")
