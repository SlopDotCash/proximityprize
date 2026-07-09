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
def sieve(lim):
    s=[True]*(lim+1); s[0]=s[1]=False
    for i in range(2,int(lim**.5)+1):
        if s[i]:
            for j in range(i*i,lim+1,i): s[j]=False
    return [i for i in range(lim+1) if s[i]]

# For each n, find the LARGEST prime q=1 mod n at which the variety still DEVIATES from char-0.
# char-0 baseline = coset-union count for (a,t=2): C(n/2, a/2) if 2|a else 0.
allp = sieve(200000)
def primes_mod(n, lo, hi):
    return [q for q in allp if lo<=q<=hi and (q-1)%n==0]

for n in [8,16,32]:
    a = n//2 + 2 if (n//2+2)%2==0 else n//2+3  # an even a near middle, keeps enum modest
    a = min(a, 6)  # cap enumeration cost (C(n,6))
    if a%2: a+=1
    t=2
    base = comb(n//2, a//2)
    # scan primes, find max q with deviation, report as exponent in n
    maxdev_q = None
    qs = primes_mod(n, n+1, min(200000, n**5))
    sample = qs if len(qs)<=400 else qs[:200]+qs[-200:]
    for q in sample:
        mu=mu_subgroup(q,n)
        c=variety_count(mu,a,t,q)
        if c!=base:
            if maxdev_q is None or q>maxdev_q: maxdev_q=q
    exp = math.log(maxdev_q)/math.log(n) if maxdev_q else None
    print(f"n={n:3d} a={a} t={t} base(char0)={base}: "
          f"max prime with DEVIATION = {maxdev_q} (= n^{exp:.2f})" if maxdev_q else
          f"n={n:3d} a={a} t={t} base={base}: NO deviation found among {len(sample)} primes up to {sample[-1]}")
    print(f"        (prize regime is q~n^4 to n^5 = {n**4} to {n**5})")
