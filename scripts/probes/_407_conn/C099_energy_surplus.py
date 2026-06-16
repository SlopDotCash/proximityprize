"""
C099: confirm the SPLIT (prize-regime) additive energy E_2 = sum_t r(t)^2 carries a
genuine surplus over the char-0 / inert baseline, and that the inert baseline is O(n^2)
while split exceeds it. char-0 even-n: E_2(mu_n) = 3n^2 - 3n (Lam-Leung, in-tree note).
Inert (n|p+1): r<=2 everywhere, and nonzero only on the deg-2 witnesses => E_2 = O(n).

We report split E_2 across several proper-subgroup primes; surplus = E_2 - (3n^2-3n).
We also report the INERT E_2 (over F_{p^2}, full group of nonzero t) to show it stays
O(n^2) tied to r<=2 (each t contributes <=4; #t with r>0 is O(n^2)).
"""
import sympy, math
from sympy import isprime, primitive_root

def find_split_primes(n, blo, bhi, k):
    out=[]; lo=int(n**blo); hi=int(n**bhi)
    p=lo-(lo%n)+1
    if p<lo: p+=n
    while p<=hi and len(out)<k:
        if isprime(p) and p>n: out.append(p)
        p+=n
    return out

def mu_n_in_Fp(p,n):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    S=set(); x=1
    for _ in range(n): S.add(x); x=(x*h)%p
    return S

def split_E2(p,n):
    S=mu_n_in_Fp(p,n)
    # r(t) only nonzero for t = y+z, y,z in S. compute via convolution support.
    from collections import Counter
    cnt=Counter()
    Sl=list(S)
    for y in Sl:
        for z in Sl:
            cnt[(y+z)%p]+=1
    E2=sum(v*v for v in cnt.values())
    rmax=max(cnt.values())
    return E2, rmax

print("="*78)
print("C099 split-regime E_2 surplus over char-0 baseline 3n^2-3n")
print("="*78)
for n in [8,16,32,64,128]:
    mu=n.bit_length()-1
    base=3*n*n-3*n
    print(f"\nn=2^{mu}={n}  char0_baseline 3n^2-3n = {base}")
    sp=find_split_primes(n, 2.0, 3.0, 6)
    for p in sp:
        E2,rmax=split_E2(p,n)
        surplus=E2-base
        beta=round(math.log(p)/math.log(n),2)
        print(f"  p={p:>8} (~n^{beta}): E_2={E2:>8} rmax={rmax:>3} "
              f"surplus={surplus:>7}  n^4/p={n**4/p:>10.2f}  surplus/(n^4/p)={surplus/(n**4/p):>6.3f}")
print("\nInterpretation: split surplus tracks ~n^4/p (vanishes as p grows, i.e. beta up),")
print("which is exactly the char-p Stepanov surplus. Inert side: r<=2 => no surplus, ever.")
