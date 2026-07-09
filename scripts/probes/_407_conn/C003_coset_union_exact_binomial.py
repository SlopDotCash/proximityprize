#!/usr/bin/env python3
"""
C003 probe: "The lacunary variety is a coset-UNION, so I(δ) is an EXACT binomial
C(n/2^L,(k+t)/2^L)."

We test, by EXACT enumeration over a dyadic subgroup mu_n of F_q* (prize regime:
n=2^mu a PROPER subgroup, q prime = 1 mod n, q large-ish), the THREE claims:

  Claim A (forward, PROVEN in tree = coset_union_esymm_zero):
     every union of m=(k+t)/2^L distinct 2^L-cosets has e_1=...=e_{t-1}=0,
     so #{coset-unions of size k+t} = C(n/2^L, (k+t)/2^L) <= #variety.

  Claim B (reverse, = "full_tower" but it is proven only in CHAR 0):
     every S in the variety {|S|=k+t, e_1=...=e_{t-1}=0} IS a union of 2^L-cosets.
     Over F_q (char p) this is the OPEN char-p transfer.  If B fails, the variety
     is STRICTLY LARGER than the coset unions and the "EXACT binomial" is FALSE.

  Claim C (the headline number):  #variety == C(n/2^L, (k+t)/2^L)  with L=ceil(log2 t).

We enumerate the FULL variety exactly (integer arithmetic mod q) for small n.

Outputs a table: for each (n,k,t): #variety, coset-union count C(n/2^L,(k+t)/2^L),
the divisibility flag 2^L | (k+t), and whether variety == coset-unions.
"""
import itertools, math
from math import comb

def primitive_root(q):
    # find a generator of F_q*
    facs = factorize(q-1)
    for g in range(2, q):
        if all(pow(g, (q-1)//p, q) != 1 for p in facs):
            return g
    raise RuntimeError("no primitive root")

def factorize(m):
    fs = set()
    d = 2
    while d*d <= m:
        while m % d == 0:
            fs.add(d); m//=d
        d += 1
    if m > 1: fs.add(m)
    return fs

def mu_subgroup(q, n):
    # n must divide q-1; return the n-th roots of unity in F_q as a sorted list
    assert (q-1) % n == 0
    g = primitive_root(q)
    h = pow(g, (q-1)//n, q)   # primitive n-th root
    S = []
    x = 1
    for _ in range(n):
        S.append(x); x = (x*h) % q
    assert len(set(S)) == n
    return S, h

def esymm(subset, j, q):
    # e_j of the multiset 'subset' over F_q
    if j == 0: return 1 % q
    if j > len(subset): return 0
    total = 0
    for comb_idx in itertools.combinations(subset, j):
        p = 1
        for x in comb_idx:
            p = (p*x) % q
        total = (total + p) % q
    return total % q

def variety_count(mu, n, a, t, q):
    """ #{ S subset mu, |S|=a, e_1=...=e_{t-1}=0 } exactly. """
    cnt = 0
    members = []
    for S in itertools.combinations(mu, a):
        ok = True
        for j in range(1, t):       # j = 1 .. t-1
            if esymm(S, j, q) != 0:
                ok = False; break
        if ok:
            cnt += 1
            members.append(frozenset(S))
    return cnt, members

def cosets_of_mu_d(mu, n, h, d, q):
    """ return the n/d cosets of mu_d (d-th roots of unity) inside mu_n. """
    assert n % d == 0
    # mu_d = {h^{ (n/d)*i } : i}
    sub = set(pow(x, n//d, q)*0 for x in mu)  # placeholder
    mu_d = [pow(h, (n//d)*i, q) for i in range(d)]
    mu_d = list(dict.fromkeys(mu_d))
    assert len(mu_d) == d, (len(mu_d), d)
    # group mu_n by coset rep = x^d   (two elements same coset iff same d-th power)
    cosets = {}
    for x in mu:
        key = pow(x, d, q)
        cosets.setdefault(key, []).append(x)
    cl = [frozenset(v) for v in cosets.values()]
    assert len(cl) == n//d, (len(cl), n//d)
    for c in cl: assert len(c) == d
    return cl

def coset_union_members(cosets, m):
    """ all unions of m distinct cosets -> set of frozensets """
    res = set()
    for combo in itertools.combinations(cosets, m):
        u = frozenset().union(*combo)
        res.add(u)
    return res

def run_case(q, n, k, t, verbose=True):
    mu, h = mu_subgroup(q, n)
    a = k + t
    if a > n:
        return None
    L = max(0, (t-1).bit_length()) if t >= 2 else 0   # ceil(log2 t): t=1 ->0, t=2->1, t=3->2, t=4->2...
    # careful: ceil(log2 t). t=1:0, t=2:1, t=3:2, t=4:2, t=5:3, t=8:3, t=9:4
    L = 0 if t <= 1 else math.ceil(math.log2(t))
    twoL = 2**L
    vc, members = variety_count(mu, n, a, t, q)
    # claimed exact binomial: requires 2^L | n and 2^L | a
    binom = None
    div_ok = (n % twoL == 0) and (a % twoL == 0)
    if div_ok:
        binom = comb(n//twoL, a//twoL)
    else:
        binom = 0  # no coset-unions of that size exist
    # coset-union members (the proven-forward lower bound), if divisible
    cu_set = set()
    if (n % twoL == 0) and (a % twoL == 0) and twoL <= n:
        cosets = cosets_of_mu_d(mu, n, h, twoL, q)
        cu_set = coset_union_members(cosets, a//twoL)
    var_set = set(members)
    is_subset = cu_set.issubset(var_set)      # forward direction sanity (should be True)
    is_equal = (cu_set == var_set)            # the EXACT-binomial reverse direction
    extra = len(var_set - cu_set)             # variety elements NOT coset unions
    return {
        "q": q, "n": n, "k": k, "t": t, "a": a, "L": L, "2^L": twoL,
        "div_ok(2^L|n & 2^L|a)": div_ok,
        "#variety": vc,
        "C(n/2^L,a/2^L)": binom,
        "#coset_unions": len(cu_set),
        "cu_subset_variety": is_subset,
        "variety==coset_unions": is_equal,
        "#variety_not_cosetunion": extra,
    }

def main():
    # prize-flavored proper-subgroup primes: q = 1 mod n, n=2^mu proper, q reasonably large
    # n=8: q=257 (8|256), proper subgroup (mu_8 < F_257*, |F*|=256). also q=41 (8|40), q=73.
    # n=16: q=257 (16|256), q=97 (16|96), q=193.
    # n=4: q=13, q=17, q=29.
    cases = []
    # ---- n=4 (mu_4), several primes ----
    for q in [13, 29, 37, 53]:
        if (q-1) % 4 != 0: continue
        for t in range(1, 4):
            for k in range(0, 4):
                a = k+t
                if 1 <= a <= 4:
                    cases.append((q,4,k,t))
    # ---- n=8 (mu_8) ----
    for q in [41, 73, 89, 257]:
        if (q-1) % 8 != 0: continue
        for t in range(1, 8):
            for k in range(0, 8):
                a = k+t
                if 2 <= a <= 8:
                    cases.append((q,8,k,t))
    # ---- n=16 (mu_16) over a few primes; cap a to keep enumeration cheap ----
    for q in [97, 193, 257]:
        if (q-1) % 16 != 0: continue
        for t in range(1, 8):
            for k in range(0, 6):
                a = k+t
                if 3 <= a <= 8:     # keep |S|<=8 for speed
                    cases.append((q,16,k,t))

    hdr = ["q","n","k","t","a","L","2^L","div_ok(2^L|n & 2^L|a)","#variety",
           "C(n/2^L,a/2^L)","#coset_unions","cu_subset_variety",
           "variety==coset_unions","#variety_not_cosetunion"]
    print("\t".join(hdr))
    counterexamples = []
    forward_failures = []
    seen = set()
    for (q,n,k,t) in cases:
        key = (q,n,k,t)
        if key in seen: continue
        seen.add(key)
        r = run_case(q,n,k,t)
        if r is None: continue
        row = [str(r[c]) for c in hdr]
        print("\t".join(row))
        # forward direction must hold (proven): coset unions subset variety
        if not r["cu_subset_variety"]:
            forward_failures.append(r)
        # the EXACT-binomial claims:
        #  (i) #variety == C(...)  and (ii) variety == coset_unions
        if r["#variety"] != r["C(n/2^L,a/2^L)"]:
            counterexamples.append(("count_mismatch", r))
        if not r["variety==coset_unions"]:
            counterexamples.append(("variety!=cosetunion", r))

    print("\n=== SUMMARY ===")
    print(f"forward-direction failures (should be 0): {len(forward_failures)}")
    print(f"exact-binomial counterexamples: {len(counterexamples)}")
    # show a few clean counterexamples where variety strictly exceeds coset unions
    strict = [r for (tag,r) in counterexamples if tag=='variety!=cosetunion' and r['#variety_not_cosetunion']>0]
    print(f"  of which variety STRICTLY larger than coset-unions: {len(strict)}")
    for r in strict[:12]:
        print("   ", {k2:r[k2] for k2 in ["q","n","k","t","a","2^L","#variety","C(n/2^L,a/2^L)","#coset_unions","#variety_not_cosetunion","div_ok(2^L|n & 2^L|a)"]})
    cm = [r for (tag,r) in counterexamples if tag=='count_mismatch']
    print(f"  count mismatches (#variety != binomial): {len(cm)}")
    for r in cm[:12]:
        print("   ", {k2:r[k2] for k2 in ["q","n","k","t","a","2^L","#variety","C(n/2^L,a/2^L)","div_ok(2^L|n & 2^L|a)"]})

if __name__ == "__main__":
    main()
