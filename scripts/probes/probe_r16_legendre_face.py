#!/usr/bin/env python3
"""R16 Legendre lane: deg=2 face of corrected Problem B.
W(s0) = sum_{x in mu_n} legendre(s0-x).  Targets:
  (1) coset invariance of |W| (exact, integer)
  (2) second moment identity sum_{s0 in F_p} W(s0)^2 = n*p - n^2 (exact)
  (3) joint distribution: max|W|/sqrt(n) vs M/sqrt(n) across primes (same wall or not?)
  (4) per-point Jacobi/Weil bound |W| <= sqrt(p)+eps check
"""
import math, cmath, sys
from sympy import isprime, primitive_root

def legendre_table(p):
    sq = [0]*p
    for a in range(1,p): sq[(a*a)%p]=1
    return [0]+[1 if sq[a] else -1 for a in range(1,p)]

def run(n, nprimes=30, pmin=None):
    res=[]
    p = (pmin or n*n) // n * n + 1
    found=0
    while found < nprimes:
        p += n
        if not isprime(p): continue
        found+=1
        g = primitive_root(p)
        m = (p-1)//n
        gm = pow(g,m,p)
        mu = []
        x=1
        for _ in range(n): mu.append(x); x=x*gm%p
        muset=set(mu)
        leg = legendre_table(p)
        # eta_b and M
        M=0.0
        for b in range(1,p):
            e = sum(cmath.exp(2j*math.pi*((b*x)%p)/p) for x in mu)
            M=max(M,abs(e))
        # W
        W=[0]*p
        for s0 in range(p):
            W[s0]=sum(leg[(s0-x)%p] for x in mu)
        # (2) second moment
        sm = sum(w*w for w in W)
        assert sm == n*p - n*n, (p, sm, n*p-n*n)
        # (1) coset invariance of |W| on s0 != 0
        cosets={}
        for s0 in range(1,p):
            # canonical coset rep: min of s0*mu
            rep=min(s0*x%p for x in mu)
            cosets.setdefault(rep,set()).add(abs(W[s0]))
        assert all(len(v)==1 for v in cosets.values()), p
        maxW = max(abs(W[s0]) for s0 in range(1,p))
        maxWoff = max(abs(W[s0]) for s0 in range(1,p) if s0 not in muset)
        maxWon = max(abs(W[s0]) for s0 in mu)
        assert maxW <= math.sqrt(p)+1+ n/math.sqrt(p)  # Jacobi-completion scale check (loose)
        res.append((p,M,maxW,maxWoff,maxWon))
    print(f"n={n}: {len(res)} primes")
    import statistics
    ratios=[r[3]/r[1] for r in res]
    print(f"  max|W_off|/M: min={min(ratios):.3f} max={max(ratios):.3f} mean={statistics.mean(ratios):.3f}")
    # correlation between maxWoff/sqrt(n) and M/sqrt(n)
    a=[r[3]/math.sqrt(n) for r in res]; b=[r[1]/math.sqrt(n) for r in res]
    ma,mb=statistics.mean(a),statistics.mean(b)
    cov=sum((x-ma)*(y-mb) for x,y in zip(a,b))
    corr=cov/math.sqrt(sum((x-ma)**2 for x in a)*sum((y-mb)**2 for y in b))
    print(f"  corr(max|W_off|, M) = {corr:.3f}; sqrt(2)*: ratio/sqrt2 max={max(ratios)/math.sqrt(2):.3f}")
    print(f"  max|W|/sqrt(p): max={max(r[2]/math.sqrt(r[0]) for r in res):.3f}")
    print(f"  on-diag vs off: max_on/max_off mean={statistics.mean(r[4]/max(r[3],1) for r in res):.3f}")
    tgt=[r[3]/math.sqrt(n*math.log(r[0])) for r in res]
    print(f"  max|W_off|/sqrt(n ln p): min={min(tgt):.3f} max={max(tgt):.3f}")
    return res

if __name__=="__main__":
    for n in (8,16,32):
        run(n, nprimes=25)
    # beta=4-ish window for n=16: p near n^4=65536
    print("beta=4 window n=16:")
    run(16, nprimes=8, pmin=60000)
