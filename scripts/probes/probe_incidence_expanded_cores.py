"""Exact production incidence certificates with expanded common-factor cores.
Author: Mikhail Izhutkin (@mashingaan)
Production output is an exact algebraic certificate, not a Lean theorem.
"""
from fractions import Fraction
import json

N = 2**30
D = 2**24
Q = 2**128
FIELDS = [N * (Q + 192) + 1, N * (2 * Q + 13) + 1]

def design(s, t):
    assert 3 <= s <= 33 and 1 <= t and s*t <= 33
    groups = [set(range(31+j*t, 31+(j+1)*t)) for j in range(s)]
    def height(b):
        return next((j for j, group in enumerate(groups) if b in group), s)
    slots = [(j, b, height(b)+j) for j in range(s) for b in range(31,64)
             if b not in groups[j]]
    assert len(slots) == s*(33-t)
    assert len({(b,a) for j,b,a in slots}) == len(slots)
    assert all(a > 0 for j,b,a in slots)
    return groups, height, slots

def production(p, s, t):
    groups, height, slots = design(s,t)
    coeffs = {a for j,b,a in slots}
    residues = {a: pow(a,N,p) for a in coeffs}
    assert len(set(residues.values())) == len(residues)
    for a in coeffs:
        independent = a % p
        for _ in range(30):
            independent = independent * independent % p
        assert independent == residues[a]
    for j,b,a in slots:
        h = height(b)
        assert h != j
        assert Fraction(h*h-j*j,h-j) == a
    count = len(slots)*D
    assert count*Q > p
    assert 31*D+1 < N//2 <= (31+t)*D
    return dict(s=s,t=t,field=p,common_degree=31*D,
                max_head_degree=31*D+1,support_size=(31+t)*D+1,
                radius=str(Fraction((33-t)*D-1,N)),
                bad_count_lower_bound=count,budget=p//Q,
                budget_excess=count-p//Q,
                coefficient_order_residues=residues)

def finite(s,t):
    groups,height,slots = design(s,t)
    n,d,k,p,g = 128,2,64,1409,1022
    assert pow(g,n,p)==1 and pow(g,n//2,p)!=1
    points=[pow(g,i,p) for i in range(n)]
    def z(x):
        value=1
        for b in range(31):
            value=value*(pow(x,d,p)-pow(g,d*b,p))%p
        return value
    zs=[z(x) for x in points]
    hs=[height(i%64) for i in range(n)]
    row1=[hs[i]*zs[i]%p for i in range(n)]
    row0=[hs[i]**2*zs[i]*points[i]%p for i in range(n)]
    def interp(basis,x):
        value=0
        for i in basis:
            num,den=1,1
            for other in basis:
                if i!=other:
                    num=num*(x-points[other])%p
                    den=den*(points[i]-points[other])%p
            value=(value+row1[i]*num*pow(den,-1,p))%p
        return value
    seen=set()
    for j in range(s):
        core=[i for i in range(n) if i%64<31 or i%64 in groups[j]]
        assert len(core)==(31+t)*d and len(core)>=k
        basis=core[:k]
        decoded=[interp(basis,x) for x in points]
        assert decoded==[j*v%p for v in zs]
        for i in range(n):
            if i in core:
                continue
            gamma=-(hs[i]+j)*points[i]%p
            assert decoded[i]!=row1[i]
            support=core+[i]
            for a in support:
                assert (j*j*zs[a]*points[a]+gamma*j*zs[a])%p == (row0[a]+gamma*row1[a])%p
            assert gamma not in seen
            seen.add(gamma)
    assert len(seen)==s*(33-t)*d
    return dict(n=n,p=p,g=g,s=s,t=t,count=len(seen),support=(31+t)*d+1)

results=[]
for p in FIELDS:
    feasible=[(t,s) for s in range(3,34) for t in range(1,34//s+1)
              if s*t<=33 and s*(33-t)*D*Q>p]
    t,s=max(feasible)
    results.append(production(p,s,t))
assert (results[0]['s'],results[0]['t'])==(3,11)
assert (results[1]['s'],results[1]['t'])==(5,6)
print(json.dumps(dict(production=results,finite=[finite(3,11),finite(5,6)]),indent=2))
