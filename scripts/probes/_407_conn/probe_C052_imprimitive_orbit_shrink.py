"""
Probe for connection C052 (#407): "Imprimitive heavy lines are a self-similar orbit
shrink into mu_{n/gcd} sub-tower (F3<->F8 descent)".

CLAIM under attack (from C052.json attack_plan):
  For monomial direction (x^a, x^b), gap d = a-b, on the dyadic subgroup mu_n over a
  large prime q = 1 mod n (proper subgroup), the bad-scalar set lacBad is invariant
  under gamma -> g^d * gamma where g generates mu_n.  Hence:
    (i)  ord(g^d) = n / gcd(d,n) divides #lacBad  (the orbit-divisibility law);
    (ii) gcd(d,n)>1 ("imprimitive") => SMALLER eigenratio order n/gcd  => the bad set
         tiles into cosets of the SMALLER group mu_{n/gcd}, claimed = the F8 2-adic
         descent (residence one tower level down);
    (iii) "heavy imprimitive lines": gcd>1 directions are claimed heavy (up to full-q
          incidence) while primitive concentrate.

We compute lacBad EXACTLY over the integers/mod q:
  lacBad(mu_n, a, t=d) = { e_t(S) mod q : S subset mu_n, |S|=a, e_1(S)=...=e_{t-1}(S)=0 }
This is the Vieta pin (DyadicLacunaryDeltaStar.lean): the bad scalars at delta = 1-a/n.

PRIZE REGIME: dyadic mu_n with n = 2^mu a PROPER subgroup, q prime = 1 mod n, large.
We can't brute-force C(n, a) subsets for prize-size n, so we use SMALL n (8,16,32) with
proper-subgroup large primes, exact integer arithmetic.  The orbit-divisibility law and
the heaviness comparison are STRUCTURAL (q-independent up to the relation-free transfer),
so small-n proper-subgroup tests are the right diagnostic (NOT full-group n=q-1).
"""

import itertools
from math import gcd
from sympy import isprime

def find_subgroup_prime(n, qmin):
    """Smallest prime q >= qmin with q = 1 mod n (so mu_n is a PROPER subgroup of F_q*)."""
    q = qmin - (qmin % n) + 1
    if q < qmin:
        q += n
    while True:
        if isprime(q):
            return q
        q += n

def mu_n(n, q):
    """The dyadic subgroup mu_n = { g^j } of order n in F_q*, with a fixed generator g."""
    # find an element of order exactly n
    # take a generator of F_q* via small search, raise to (q-1)/n
    for cand in range(2, q):
        # primitive root test (cheap-ish for small q): order == q-1
        order = 1
        x = cand % q
        seen = x
        while seen != 1:
            seen = (seen * cand) % q
            order += 1
            if order > q:  # safety
                order = -1
                break
        if order == q - 1:
            prim = cand
            break
    g = pow(prim, (q - 1) // n, q)
    elts = [pow(g, j, q) for j in range(n)]
    assert len(set(elts)) == n, "mu_n not of full order"
    return g, elts

def esymm(subset, t, q):
    """e_t of a list of field elements (mod q)."""
    if t == 0:
        return 1 % q
    if t > len(subset):
        return 0
    acc = 0
    for combo in itertools.combinations(subset, t):
        p = 1
        for x in combo:
            p = (p * x) % q
        acc = (acc + p) % q
    return acc % q

def lacBad(elts, a, t, q):
    """{ e_t(S) : S subset mu_n, |S|=a, e_1(S)=...=e_{t-1}(S)=0 }  (mod q)."""
    vals = set()
    variety_size = 0
    for S in itertools.combinations(elts, a):
        ok = True
        for j in range(1, t):
            if esymm(S, j, q) != 0:
                ok = False
                break
        if ok:
            variety_size += 1
            vals.add(esymm(S, t, q))
    return vals, variety_size

def order_of(x, q):
    if x % q == 0:
        return None
    o = 1
    y = x % q
    while y != 1:
        y = (y * x) % q
        o += 1
    return o

def run(n, a_list=None, verbose=True):
    q = find_subgroup_prime(n, 1000)  # large-ish proper-subgroup prime
    g, elts = mu_n(n, q)
    print(f"\n=== n={n}  q={q} (q-1)/n={(q-1)//n}  g={g} (order {order_of(g,q)}) ===")
    if a_list is None:
        a_list = list(range(2, n + 1))
    results = []
    for a in a_list:
        for b in range(0, a):  # b < a, gap d = a-b in [1..a]
            d = a - b
            if a > n:
                continue
            t = d
            vals, variety = lacBad(elts, a, t, q)
            count = len(vals)
            gd = gcd(d, n)
            ordgd = n // gd  # ord(g^d) = n/gcd(d,n)
            # zero membership: is 0 in lacBad? then orbit-divisibility excludes the 0-orbit
            has_zero = (0 in vals)
            nonzero = count - (1 if has_zero else 0)
            div_ok = (nonzero % ordgd == 0) if ordgd > 0 else True
            results.append((a, b, d, gd, ordgd, count, nonzero, has_zero, div_ok, variety))
    if verbose:
        print(f"{'a':>3}{'b':>3}{'d':>3}{'gcd':>4}{'ord=n/g':>8}{'#lacBad':>9}{'#nz':>5}{'0?':>3}{'div?':>5}{'#var':>7}")
        for (a,b,d,gd,ordgd,count,nz,hz,div_ok,var) in results:
            print(f"{a:>3}{b:>3}{d:>3}{gd:>4}{ordgd:>8}{count:>9}{nz:>5}{str(hz):>3}{str(div_ok):>5}{var:>7}")
    # divisibility check (claim i): nonzero part divisible by ord(g^d)=n/gcd(d,n)
    bad_div = [(a,b,d,gd,ordgd,count,nz) for (a,b,d,gd,ordgd,count,nz,hz,dv,var) in results if not dv]
    return q, results, bad_div

if __name__ == "__main__":
    all_bad = []
    for n in [8, 16]:
        q, results, bad_div = run(n)
        all_bad += bad_div
        # heavy-line diagnostic: for fixed a, compare incidence (#lacBad) across gaps d
        # grouped by primitive (gcd=1) vs imprimitive (gcd>1)
        print(f"  --- heaviness (n={n}): max #lacBad by gcd class ---")
        from collections import defaultdict
        byg = defaultdict(list)
        for (a,b,d,gd,ordgd,count,nz,hz,dv,var) in results:
            byg[gd].append(count)
        for gd in sorted(byg):
            cs = byg[gd]
            print(f"    gcd(d,n)={gd}: max#lacBad={max(cs)} mean={sum(cs)/len(cs):.1f} (n={n})")

    # n=32: restrict a to keep C(32,a) tractable; small a only
    q, results, bad_div = run(32, a_list=[2,3,4], verbose=True)
    all_bad += bad_div

    print("\n========== VERDICT DATA ==========")
    if all_bad:
        print(f"DIVISIBILITY VIOLATIONS (claim i FAILS): {len(all_bad)}")
        for r in all_bad[:20]:
            print("   ", r)
    else:
        print("DIVISIBILITY (claim i): HOLDS in all tested (a,b,n) — n/gcd(d,n) | #nonzero-lacBad.")
