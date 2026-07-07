#!/usr/bin/env python3
"""R17 JOINT lane: T_chi family joint moments.
T_chi(s0) = sum_{x in mu_n} chi(s0 - x), chi mult char mod p (chi(0)=0).

(a) full family: sum_{ALL chi mod p} |T_chi(s0)|^2 = (p-1)*(n - [s0 in mu_n])
    deg subfamily {chi: chi^deg = chi0}: = deg * #{(x,y) in mu_n^2, s0-x,s0-y != 0,
        (s0-x)/(s0-y) in (F_p^x)^deg}
(b) sum_{s0 in F_p} |T_chi(s0)|^2 = n*p - n^2  for chi nontrivial
(c) sum_{s0} |T_chi(s0)|^4 vs Wick: complex chi -> 2*p*n^2, real chi -> 3*p*n^2 (asympt).
    chi0-layer of the expansion = additive-energy-type object.
"""
import cmath, math
from sympy import isprime, primitive_root

def mults(p):
    g = primitive_root(p)
    # dlog table
    dlog = {}
    v = 1
    for k in range(p-1):
        dlog[v] = k
        v = v*g % p
    return g, dlog

def run(n, p, degs=(2,4,8)):
    assert isprime(p) and (p-1) % n == 0
    g, dlog = mults(p)
    mu = [pow(g, (p-1)//n * k, p) for k in range(n)]
    muset = set(mu)
    w = [cmath.exp(2j*math.pi*k/(p-1)) for k in range(p-1)]
    def chi_val(j, a):  # chi_j(a) = w^{j*dlog(a)}
        if a % p == 0: return 0
        return w[(j*dlog[a % p]) % (p-1)]
    def T(j, s0):
        return sum(chi_val(j, (s0-x) % p) for x in mu)

    print(f"== n={n} p={p} ==")
    # (a) fixed s0, full family
    for s0 in [mu[1], (mu[1]+1) % p, 3]:
        tot = sum(abs(T(j, s0))**2 for j in range(p-1))
        pred = (p-1)*(n - (1 if s0 in muset else 0))
        ok = abs(tot - pred) < 1e-6*max(1,pred)
        print(f"  (a) s0={s0} in_mu={s0 in muset}: sum_all_chi={tot:.4f} pred={pred} {'OK' if ok else 'FAIL'}")
        # deg subfamily
        for deg in degs:
            if (p-1) % deg: continue
            js = [ (p-1)//deg * k for k in range(deg)]
            sub = sum(abs(T(j, s0))**2 for j in js)
            # incidence count
            powres = { pow(a, deg, p) for a in range(1,p) }
            cnt = 0
            for x in mu:
                for y in mu:
                    u, v = (s0-x) % p, (s0-y) % p
                    if u and v and (u*pow(v, p-2, p)) % p in powres:
                        cnt += 1
            pred2 = deg*cnt
            ok2 = abs(sub - pred2) < 1e-6*max(1,pred2)
            print(f"      deg={deg}: subfam={sub:.4f} deg*count={pred2} {'OK' if ok2 else 'FAIL'}")
    # (b) sum over s0, per chi
    bad = 0
    for j in range(1, p-1):
        s = sum(abs(T(j, s0))**2 for s0 in range(p))
        if abs(s - (n*p - n*n)) > 1e-5*n*p: bad += 1
    print(f"  (b) all {p-2} nontrivial chi give n*p-n^2={n*p-n*n}: {'OK' if bad==0 else f'{bad} FAIL'}")
    # trivial chi
    s = sum(abs(T(0, s0))**2 for s0 in range(p))
    print(f"      chi0: sum={s:.2f}  (n-[s0 in mu])^2 summed = {sum((n-(1 if s0 in muset else 0))**2 for s0 in range(p))}")
    # (c) fourth moment
    for deg in degs:
        if (p-1) % deg: continue
        j = (p-1)//deg  # a character of exact order deg
        s4 = sum(abs(T(j, s0))**4 for s0 in range(p))
        wick_c = 2*p*n*n
        wick_r = 3*p*n*n
        print(f"  (c) order-{deg} chi: S4={s4:.1f}  S4/2pn^2={s4/wick_c:.4f}  S4/3pn^2={s4/wick_r:.4f}")
    # (c) chi0-layer: E_2(mu_n) additive energy for reference
    from collections import Counter
    diffs = Counter(((x-y) % p) for x in mu for y in mu)
    E2 = sum(c*c for c in diffs.values())
    print(f"      E2(mu_n) = {E2}  (Wick-ish 3n^2-... ; n^2={n*n})")

for n, p in [(8, 41), (8, 73), (16, 97), (16, 113), (32, 193), (32, 257)]:
    run(n, p)
