import numpy as np, math
from sympy import factorint
# alpha = zeta^{a1}+zeta^{a2}+zeta^{a3} - (1 + zeta^{b2}+zeta^{b3}), wlog b1=0 by rotation
# bad prime p (p=1 mod n): p | N(alpha) for some alpha != 0 in Z[zeta_n]
for n in (8,16,32):
    phi = n//2  # n = 2^k: phi(n)=n/2
    prim = [k for k in range(n) if math.gcd(k,n)==1]
    zs = np.exp(2j*np.pi*np.array(prim)/n)  # primitive n-th roots (conjugate set)
    badprimes=set(); maxnorm=0
    idx = np.arange(n)
    # enumerate a1<=a2<=a3 (multiset), b's: 0<=b2<=b3
    from itertools import combinations_with_replacement as cwr
    A=list(cwr(range(n),3)); B=[(0,)+t for t in cwr(range(n),2)]
    ZP = zs[None,:]  # (1,phi)
    Bv = {}
    for b in B:
        Bv[b]=sum(zs**e for e in b)
    for a in A:
        va=sum(zs**e for e in a)
        for b in B:
            d=va-Bv[b]
            if np.max(np.abs(d))<1e-9: continue  # alpha=0 in C => zero in Z[zeta]
            nrm=np.prod(np.abs(d)**1)  # product over conjugates of |alpha_sigma| — but norm=prod alpha_sigma real
            nr=np.prod(d).real
            N=round(abs(nr))
            if N==0:
                # numerically zero product but alpha nonzero? some conjugate zero -> norm 0 impossible for nonzero alg int... means alpha=0 under some embedding => norm 0 => alpha=0? No: norm 0 iff alpha=0. treat as zero
                continue
            maxnorm=max(maxnorm,N)
            for pf in factorint(N):
                if pf % n == 1: badprimes.add(pf)
    mb = max(badprimes) if badprimes else 0
    print(f"n={n}: max norm={maxnorm}, bad primes (≡1 mod n): count={len(badprimes)}, max={mb}, n³={n**3}, max/n³={mb/n**3:.3f}")
    print("   largest few:", sorted(badprimes)[-6:])
