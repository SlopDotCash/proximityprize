"""
C052 disambiguation: the connection ties "imprimitive heavy" to gcd(d,n), d=a-b
(the GAP), claiming gcd(d,n)>1 => heavy.  The issue grounding (line 222-224) ties
heaviness to the gcd of the EXPONENTS a,b themselves (X^{2a'} on mu_n = X^{a'} on
mu_{n/2} pulled back).  These are DIFFERENT objects.  We measure #lacBad as a function
of BOTH gcd(d,n) [C052's quantity] and gcd(a,b,n) [the issue's pull-back quantity] to
see which one actually predicts heaviness, and whether C052's gap-gcd claim is right.

lacBad(mu_n,a,t=d) is the Vieta-pinned bad-scalar set at delta=1-a/n (DyadicLacunary).
Exact integer arithmetic over a proper-subgroup prime q=1 mod n.
"""
import itertools
from math import gcd
from sympy import isprime
from collections import defaultdict

def find_subgroup_prime(n, qmin):
    q = qmin - (qmin % n) + 1
    if q < qmin: q += n
    while not isprime(q): q += n
    return q

def mu_n(n, q):
    for cand in range(2, q):
        order, x, seen = 1, cand % q, cand % q
        while seen != 1:
            seen = (seen * cand) % q; order += 1
            if order > q: order = -1; break
        if order == q-1: prim = cand; break
    g = pow(prim, (q-1)//n, q)
    return [pow(g, j, q) for j in range(n)]

def esymm(S, t, q):
    if t == 0: return 1 % q
    if t > len(S): return 0
    acc = 0
    for c in itertools.combinations(S, t):
        p = 1
        for x in c: p = (p*x) % q
        acc = (acc+p) % q
    return acc

def lacBad_count(elts, a, t, q):
    vals = set()
    for S in itertools.combinations(elts, a):
        if all(esymm(S, j, q) == 0 for j in range(1, t)):
            vals.add(esymm(S, t, q))
    return len(vals)

for n in [8, 16]:
    q = find_subgroup_prime(n, 1000)
    elts = mu_n(n, q)
    print(f"\n=== n={n} q={q} ===")
    by_gapgcd = defaultdict(list)     # C052: gcd(a-b, n)
    by_expgcd = defaultdict(list)     # issue: gcd(a, b, n)  (pull-back level)
    rows = []
    for a in range(2, n+1):
        for b in range(0, a):
            d = a - b
            cnt = lacBad_count(elts, a, d, q)
            ggap = gcd(d, n)
            gexp = gcd(gcd(a, b), n)
            by_gapgcd[ggap].append(cnt)
            by_expgcd[gexp].append(cnt)
            rows.append((a, b, d, ggap, gexp, cnt))
    print(" Heaviness by GAP gcd(d,n) [C052's claim: gcd>1 => HEAVY]:")
    for g in sorted(by_gapgcd):
        cs = by_gapgcd[g]
        print(f"   gcd(d,n)={g:>2}: max={max(cs):>5} mean={sum(cs)/len(cs):6.1f} q={q}")
    print(" Heaviness by EXPONENT gcd(a,b,n) [issue's pull-back X^{2a'} level]:")
    for g in sorted(by_expgcd):
        cs = by_expgcd[g]
        print(f"   gcd(a,b,n)={g:>2}: max={max(cs):>5} mean={sum(cs)/len(cs):6.1f} q={q}")
    # the actual full-q heavy rows
    heavy = sorted([r for r in rows if r[5] >= q-2], key=lambda r:-r[5])
    print(f" Near-full-q heavy rows (#lacBad >= q-2 = {q-2}):")
    for (a,b,d,ggap,gexp,cnt) in heavy[:8]:
        print(f"   (a={a},b={b}) d={d} gcd(d,n)={ggap} gcd(a,b,n)={gexp}  #lacBad={cnt}")
