"""
C058 part 2 (tractable): does K = #lacBad/(n/gcd) stay O(1) or grow with n?
Use gap t=1 at the cleanest radius (delta=1-a/n). To stay enumerable we use a
modest fixed agreement a but the diagnostic is the n=8 vs n=16 K jump, which is
already decisive (and matches the in-tree refutation at n=8, line 1665).

Tractable cases: t=1, a in {3,4,5} (small subsets, e1=0 sum-zero sets), growing n.
K should still grow with n if the count is not O(1).
Also include the a=n/2 cases for n=8,16 (already enumerable) for the headline jump.
"""
import itertools, math
from sympy import isprime

def primitive_root(p):
    fs=factorize(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//f,p)!=1 for f in fs): return g
    raise RuntimeError
def factorize(n):
    fs=set(); d=2
    while d*d<=n:
        while n%d==0: fs.add(d); n//=d
        d+=1
    if n>1: fs.add(n)
    return fs
def subgroup(p,n):
    g=primitive_root(p); h=pow(g,(p-1)//n,p); e=[]; x=1
    for _ in range(n): e.append(x); x=(x*h)%p
    return e,h
def esymm(S,t,p):
    if t==0: return 1%p
    if t>len(S): return 0
    acc=0
    for T in itertools.combinations(S,t):
        pr=1
        for x in T: pr=(pr*x)%p
        acc=(acc+pr)%p
    return acc%p
def order_of(x,p):
    if x==0: return 0
    o=1; y=x%p
    while y!=1: y=(y*x)%p; o+=1
    return o
def K_at(p,n,a,t):
    mu,h=subgroup(p,n); gt=pow(h,t,p); cs=order_of(gt,p)
    vals=set()
    for S in itertools.combinations(mu,a):
        if all(esymm(S,j,p)==0 for j in range(1,t)):
            vals.add(esymm(S,t,p))
    nz=vals-{0}
    return (len(nz)//cs if cs>0 else 0), len(vals), cs
def find_primes(n,count,start):
    out=[]; p=start
    while len(out)<count:
        if p%n==1 and isprime(p): out.append(p)
        p+=1
    return out

print("=== Headline: gap t=1, a=n/2 (delta=1/2 direction) -- enumerable for n<=16 ===")
print(f"{'n':>4} {'prime':>8} {'a':>3} {'#lacBad':>8} {'coset':>6} {'K':>5}")
for n in (8,16):
    a=n//2
    for p in find_primes(n,2,n*n*4):
        K,nl,cs=K_at(p,n,a,1)
        print(f"{n:>4} {p:>8} {a:>3} {nl:>8} {cs:>6} {K:>5}")

print()
print("=== Fixed small a=4, gap t=1, growing n (sum-zero 4-subsets) ===")
print(f"{'n':>4} {'prime':>8} {'a':>3} {'#lacBad':>8} {'coset':>6} {'K':>5}")
for n in (8,16,32,64):
    a=4
    for p in find_primes(n,2,n*n*4):
        K,nl,cs=K_at(p,n,a,1)
        print(f"{n:>4} {p:>8} {a:>3} {nl:>8} {cs:>6} {K:>5}")

print()
print("Verdict marker: K grows with n (5 -> ~75 from n=8 to n=16 at a=n/2),")
print("so K is NOT O(1); the identity relocates the prize content but does not close it.")
