import itertools, math
from math import comb
def factorize(m):
    fs=set(); d=2
    while d*d<=m:
        while m%d==0: fs.add(d); m//=d
        d+=1
    if m>1: fs.add(m)
    return fs
def primitive_root(q):
    facs=factorize(q-1)
    for g in range(2,q):
        if all(pow(g,(q-1)//p,q)!=1 for p in facs): return g
    raise RuntimeError
def mu_subgroup(q,n):
    g=primitive_root(q); h=pow(g,(q-1)//n,q)
    S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%q
    return S
def variety_count_a_t2(mu,a,q):
    cnt=0
    for Sb in itertools.combinations(mu,a):
        if sum(Sb)%q==0: cnt+=1
    return cnt
import sympy
# n=64, a=4, base=C(32,2)=496. Sample primes q=1 mod 64 across exponent bands up to n^4.5.
n=64; a=4; base=comb(n//2,2)
targets_exp=[2.7,2.9,3.1,3.3,3.5,3.7,3.9,4.1,4.3]
print(f"n={n} a={a} char0base={base}; prize q~n^4={n**4} .. n^5={n**5}")
for ex in targets_exp:
    centre=int(n**ex)
    # find a prime q=1 mod 64 near centre
    q=centre - (centre % n) + 1
    found=[]
    cnt_checks=0
    while len(found)<3 and cnt_checks<20000:
        if q>n and sympy.isprime(q):
            found.append(q)
        q+=n; cnt_checks+=1
    for q in found:
        mu=mu_subgroup(q,n)
        c=variety_count_a_t2(mu,a,q)
        dev = "" if c==base else f"  <-- DEVIATION ({c} vs {base})"
        print(f"  q={q} (n^{math.log(q)/math.log(n):.2f})  #variety={c}{dev}")
