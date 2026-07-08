"""#466: find minimal moment order 2r where char-p wraparound W_{2r}>0 first appears,
at fixed small n in Burgess regime p~n^beta. Extract onset scaling r*(n,beta)."""
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
def char0_key(expos,n):
    h=n//2; c=Counter()
    for a in expos:
        a%=n
        if a>=h: c[a-h]-=1
        else: c[a]+=1
    return tuple(sorted((k,v) for k,v in c.items() if v!=0))
def W_moment(n,p,root,r):
    c0=Counter(); cp=Counter()
    for t in itertools.product(range(n),repeat=r):
        c0[char0_key(t,n)]+=1
        s=0
        for a in t: s=(s+pow(root,a,p))%p
        cp[s]+=1
    return sum(v*v for v in cp.values())-sum(v*v for v in c0.values())

for beta in (2.0,3.0,4.0):
    print(f"=== beta={beta} : minimal r with W_2r>0 (onset) ===")
    for k in (2,3,4):
        n=1<<k; lo=int(n**beta); p=prime_ge_2adic(lo,n)
        root=pow(primitive_root(p),(p-1)//n,p)
        onset=None
        rmax = {2:8,3:6,4:5}[k]
        for r in range(2,rmax+1):
            if n**r > 3_000_000: break
            W=W_moment(n,p,root,r)
            if W>0: onset=r; break
        lnq=math.log(p)
        print(f"  n={n:3d} p={p:9d} ln q={lnq:5.1f}  onset r*={onset}  (2r*={2*onset if onset else None})  searched r<= {r}")
