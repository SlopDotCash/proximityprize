import itertools, math
from math import comb
import sympy
def primitive_root(q):
    facs=sympy.factorint(q-1).keys()
    for g in range(2,q):
        if all(pow(g,(q-1)//p,q)!=1 for p in facs): return g
def mu_subgroup(q,n):
    g=primitive_root(q); h=pow(g,(q-1)//n,q)
    S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%q
    return S
def esymm(subset,j,q):
    if j==0: return 1%q
    if j>len(subset): return 0
    tot=0
    for c in itertools.combinations(subset,j):
        p=1
        for x in c: p=(p*x)%q
        tot=(tot+p)%q
    return tot%q
def variety_count(mu,a,t,q):
    cnt=0
    for Sb in itertools.combinations(mu,a):
        if all(esymm(Sb,j,q)==0 for j in range(1,t)): cnt+=1
    return cnt
def prime_near(centre,n):
    q=centre-(centre%n)+1
    while not sympy.isprime(q): q+=n
    return q

# t=4 case (L=2, 2^L=4). char-0 baseline = C(n/4, a/4). Test at PRIZE exponents.
# n=16, a=8, t=4: char0 = C(4,2)=6.  n=32,a=8,t=4: char0=C(8,2)=28.
print("=== t=4 (2^L=4): variety vs char-0 binomial at PRIZE-exponent primes ===")
for (n,a,t) in [(16,8,4),(16,4,4)]:
    L=2; base=comb(n//4, a//4) if a%4==0 else 0
    for ex in [2.5,3.0,4.0,4.5]:
        q=prime_near(int(n**ex),n)
        mu=mu_subgroup(q,n)
        c=variety_count(mu,a,t,q)
        dev="" if c==base else "  <-- DEV"
        print(f"  n={n} a={a} t={t} q={q}(n^{math.log(q)/math.log(n):.2f}) #var={c} char0={base}{dev}")
# n=32 t=2 a=6 at prize exponent (heavier; one sample per band)
print("=== n=32 a=6 t=2 char0=C(16,3)=560 at prize exponents ===")
for ex in [3.0,4.0]:
    q=prime_near(int(32**ex),32)
    mu=mu_subgroup(q,32)
    c=variety_count(mu,6,2,q)
    print(f"  q={q}(n^{math.log(q)/math.log(32):.2f}) #var={c} char0={comb(16,3)} {'' if c==560 else '<-- DEV'}")
