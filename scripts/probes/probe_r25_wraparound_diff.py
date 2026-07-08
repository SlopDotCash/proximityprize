"""#466: isolate the char-p WRAPAROUND SURPLUS in the additive moment tower for dyadic mu_n.
E_{2r}(char0) = #{(a_1..a_r,b_1..b_r) in (Z/n)^{2r} : sum zeta^{a_i} = sum zeta^{b_j}} in C.
E_{2r}(char p) = same identity but zeta -> primitive n-th root in F_p (Burgess p~n^4).
Wraparound surplus W_{2r} = E_{2r}(char p) - E_{2r}(char0) >= 0 is EXACTLY the char-p
Wick-breaking. Campaign claim: W=0 at fixed r for large n (fixed-r faces char-0-clean),
onset only at r ~ ln q. We measure W directly for r=2,3."""
import itertools, math
from collections import Counter
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

def char0_key(expos, n):
    # sum of zeta^a over a in expos; n=2^mu so zeta^{a} = (-1)^{a>=n/2} zeta^{a mod n/2}
    h=n//2
    c=Counter()
    for a in expos:
        a%=n
        if a>=h: c[a-h]-=1
        else: c[a]+=1
    return tuple(sorted((k,v) for k,v in c.items() if v!=0))
def charp_key(expos, root, p):
    s=0
    for a in expos: s=(s+pow(root,a,p))%p
    return s

for r in (2,3):
    print(f"=== moment 2r={2*r} (E_{2*r}), Burgess beta=4 ===")
    nmax = 64 if r==2 else 32
    for k in range(2, 1+int(math.log2(nmax))):
        n=1<<k; lo=int(n**4); p=prime_ge_2adic(lo,n)
        root=primitive_root(p); root=pow(root,(p-1)//n,p)  # primitive n-th root in F_p
        # enumerate all r-subsets-with-repetition exponent tuples, bucket by char0 and charp keys
        tuples=list(itertools.product(range(n), repeat=r))
        c0=Counter(); cp=Counter()
        for t in tuples:
            c0[char0_key(t,n)]+=1
            cp[charp_key(t,root,p)]+=1
        E0=sum(v*v for v in c0.values())
        Ep=sum(v*v for v in cp.values())
        W=Ep-E0
        print(f"  n={n:3d} p={p:9d} E{2*r}(0)={E0:8d} E{2*r}(p)={Ep:8d}  W={W:6d}  W/n^{r}={W/n**r:.3f}  ({'CLEAN' if W==0 else 'WRAPAROUND'})")
