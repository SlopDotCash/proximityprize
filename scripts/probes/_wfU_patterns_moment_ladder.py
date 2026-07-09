import numpy as np, itertools, math
# Verify the UNIFIED moment identity:  sum_b ||eta_b||^{2r} = q * E_r(G)
# where eta_b = sum_{y in G} psi(b*y), psi primitive additive char of F_q (q prime here),
# and E_r(G) = #{(y_1..y_r, z_1..z_r) in G^{2r} : sum y_i = sum z_i}.
def test(q, G):
    psi = lambda a: np.exp(2j*np.pi*(a % q)/q)
    Fq = range(q)
    # eta_b for all b
    results = {}
    for r in (1,2,3):
        # left: sum_b ||eta_b||^{2r}
        lhs = 0.0
        for b in Fq:
            eta = sum(psi((b*y) % q) for y in G)
            lhs += abs(eta)**(2*r)
        # right: q * E_r(G)
        Er = 0
        for ys in itertools.product(G, repeat=r):
            for zs in itertools.product(G, repeat=r):
                if sum(ys) % q == sum(zs) % q:
                    Er += 1
        rhs = q * Er
        results[r] = (lhs, rhs, abs(lhs-rhs))
    return results

import random
random.seed(1)
for q in (7,11,13,17):
    # pick G = multiplicative subgroup-ish: a random subset and also a genuine subgroup
    # genuine subgroup of F_q^* of order n | q-1
    g = None
    for cand in range(2,q):
        # find a generator
        seen=set(); x=1; order=0
        for _ in range(q-1):
            x=(x*cand)%q; order+=1
            if x==1: break
        if order==q-1: g=cand; break
    # subgroup of order n where n | q-1
    qm1=q-1
    divs=[d for d in range(1,qm1+1) if qm1%d==0]
    n=random.choice([d for d in divs if 2<=d<=6])
    sub=set()
    x=1
    gen=pow(g,(q-1)//n,q)
    for _ in range(n):
        sub.add(x); x=(x*gen)%q
    G=sorted(sub)
    res=test(q,G)
    ok=all(d<1e-6 for (_,_,d) in res.values())
    print(f"q={q} G(subgroup ord {len(G)})={G}: ", {r:(round(l,3),rr,round(d,9)) for r,(l,rr,d) in res.items()}, "OK" if ok else "FAIL")
