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
def sieve(lim):
    s=[True]*(lim+1); s[0]=s[1]=False
    for i in range(2,int(lim**.5)+1):
        if s[i]:
            for j in range(i*i,lim+1,i): s[j]=False
    return [i for i in range(lim+1) if s[i]]
allp=sieve(70000)
def primes_mod(n,lo,hi): return [q for q in allp if lo<=q<=hi and (q-1)%n==0]

# Bound each scan to a manageable prime cap (<=70000), report max deviation exponent.
for n in [8,16,32,64]:
    a=4; base=comb(n//2,2)
    cap=min(70000, n**5)
    qs=primes_mod(n, n+1, cap)
    maxdev=None; ndev=0
    for q in qs:
        mu=mu_subgroup(q,n)
        if variety_count_a_t2(mu,a,q)!=base:
            ndev+=1
            if maxdev is None or q>maxdev: maxdev=q
    capexp=math.log(cap)/math.log(n)
    if maxdev:
        print(f"n={n:3d} a=4: base={base} scanned {len(qs)} primes up to q={cap}(=n^{capexp:.2f}); "
              f"#dev={ndev} MAXdev q={maxdev}=n^{math.log(maxdev)/math.log(n):.2f}")
    else:
        print(f"n={n:3d} a=4: base={base} scanned {len(qs)} primes up to q={cap}(=n^{capexp:.2f}); NO deviation")
