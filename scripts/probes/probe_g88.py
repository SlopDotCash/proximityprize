import itertools
from fractions import Fraction

def probe(p, g, n, m, r):
    q = p
    assert pow(g, m, p) == p-1, "g^m != -1"
    # orderOf g == n check
    o=1; x=g%p
    while x!=1: x=x*g%p; o+=1
    assert o==n, (o,n)
    # repRF: count r-tuples over Fin n with sum g^{t_i} = c
    rep = {c:0 for c in range(p)}
    for t in itertools.product(range(n), repeat=r):
        s = sum(pow(g,ti,p) for ti in t) % p
        rep[s]+=1
    total = sum(rep.values()); assert total == n**r
    # 1. rotation invariance rep(g*c)=rep(c)
    for c in range(p):
        assert rep[(g*c)%p]==rep[c], ("rotinv fail",c)
    # shadowEnergy + collision = sum rep^2  (trust R312) -> centeredShadowMass = q*sum rep^2 - n^(2r)
    csm = q*sum(v*v for v in rep.values()) - n**(2*r)
    # class masses: gamma = c^n for c != 0
    classes = {}
    for c in range(1,p):
        gam = pow(c,n,p)
        classes.setdefault(gam,0)
        classes[gam]+=rep[c]
    parseval = q*(Fraction(rep[0]**2) + Fraction(sum(S*S for S in classes.values()), n)) - n**(2*r)
    assert parseval == csm, ("parseval fail", parseval, csm)
    # fiber sizes: each class has exactly n elements
    fibsz = {}
    for c in range(1,p):
        fibsz.setdefault(pow(c,n,p),0); fibsz[pow(c,n,p)]+=1
    assert all(v==n for v in fibsz.values()), fibsz
    # rep constant on classes
    for c in range(1,p):
        for t in range(n):
            assert rep[(pow(g,t,p)*c)%p]==rep[c]
    # 3. frame collision quantization
    for c in range(p):
        for cp in range(p):
            cnt = sum(1 for j in range(n) for k in range(n)
                      if (pow(g,j,p)*c)%p == (pow(g,k,p)*cp)%p)
            if c==0 and cp==0: assert cnt==n*n
            elif c==0 or cp==0: assert cnt==0
            elif pow(c,n,p)==pow(cp,n,p): assert cnt==n, (c,cp,cnt)
            else: assert cnt==0, (c,cp,cnt)
    # bracket check
    S0 = rep[0]; rest = n**r - S0
    lower = q*S0*S0 - n**(2*r)
    upper = q*Fraction(S0*S0) + q*Fraction(rest*rest,n) - n**(2*r)
    assert lower <= csm <= upper, (lower, csm, upper)
    print(f"p={p} g={g} n={n} m={m} r={r}: ALL OK  csm={csm} S0={S0} #classes={len(classes)} lower={lower} upper={float(upper):.1f}")

probe(17, 4, 4, 2, 2)
probe(17, 4, 4, 2, 3)
probe(97, 33, 8, 4, 2); probe(97, 33, 8, 4, 3)
probe(193, 3, 16, 8, 2)
