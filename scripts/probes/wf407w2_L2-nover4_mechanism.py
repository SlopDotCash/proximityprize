"""
wf407-w2 / L2-nover4 — MECHANISM: when does char-0 #orbits(w=4) = n/4-1 hold, and why does 3|n break it?

For n=2^mu (and more generally when 3 does not divide n), every e_2=0 quartet has its 6 pairwise-
product exponents pairing antipodally (diff n/2). When 3|n there are EXTRA e_2=0 quartets whose
pairwise products realize a *regular 3-gon* vanishing relation  zeta^a + zeta^{a+n/3} + zeta^{a+2n/3}=0
(needs 3 of the 6 products, but we only have 6 -> two disjoint 3-gons, or a 3-gon + an antipodal pair
is 5 -> not 6, so it must be other structure). We classify the 6 anomalous-n quartets.

Outputs:
  (1) for each n, fraction of e_2=0 quartets that are antipodally paired.
  (2) for n=12 and n=24, classify the e_2=0,e_1!=0 orbit reps: antipodal vs 3-gon-type.
  (3) the closed-form HYPOTHESIS test for general n.
"""

import itertools
from sympy import symbols, Poly, cyclotomic_poly, ZZ, factorint, divisors

X = symbols('X')

def phi_poly(n):
    return Poly(cyclotomic_poly(n, X), X, domain=ZZ)

def is_zero(terms, n, Phi):
    coeff = {}
    for (e, c) in terms:
        coeff[e % n] = coeff.get(e % n, 0) + c
    d = {(j,): v for j, v in coeff.items() if v != 0}
    if not d:
        return True
    P = Poly.from_dict(d, gens=X, domain=ZZ)
    return P.rem(Phi).is_zero

def e2_zero(exps, n, Phi):
    return is_zero([((exps[i] + exps[j]) % n, 1) for i, j in itertools.combinations(range(4), 2)], n, Phi)

def e1_zero(exps, n, Phi):
    return is_zero([(e % n, 1) for e in exps], n, Phi)

def antipodal_paired(exps, n):
    """Do the 6 pairwise-sum exponents pair into 3 antipodal (diff n/2) pairs? (needs n even)"""
    if n % 2 != 0:
        return False
    half = n // 2
    sums = [((exps[i] + exps[j]) % n) for i, j in itertools.combinations(range(4), 2)]
    cnt = {}
    for s in sums:
        cnt[s] = cnt.get(s, 0) + 1
    used = 0
    for s in sorted(cnt):
        while cnt.get(s, 0) > 0:
            t = (s + half) % n
            if t == s:
                return False
            if cnt.get(t, 0) > 0:
                cnt[s] -= 1; cnt[t] -= 1; used += 1
            else:
                return False
    return used == 3

def canon(exps, n):
    best = None
    for t in range(n):
        sh = tuple(sorted((e + t) % n for e in exps))
        if best is None or sh < best:
            best = sh
    return best

def analyze(n):
    Phi = phi_poly(n)
    orbits = {}
    e2cnt = 0; e2_anti = 0
    for exps in itertools.combinations(range(n), 4):
        if not e2_zero(exps, n, Phi):
            continue
        e2cnt += 1
        if antipodal_paired(exps, n):
            e2_anti += 1
        if e1_zero(exps, n, Phi):
            continue
        c = canon(exps, n)
        if c not in orbits:
            orbits[c] = antipodal_paired(exps, n)
    return e2cnt, e2_anti, orbits

if __name__ == "__main__":
    print(f"{'n':>4} {'fac':>10} {'#e2=0':>6} {'#antip':>7} {'all_anti?':>9} "
          f"{'#orb':>4} {'#orb_anti':>9} {'#orb_other':>10} {'n/4-1':>6}")
    for n in [8, 12, 16, 20, 24, 28, 32]:
        e2cnt, e2_anti, orbits = analyze(n)
        norb = len(orbits)
        norb_anti = sum(1 for v in orbits.values() if v)
        norb_other = norb - norb_anti
        fac = "*".join(f"{p}^{e}" if e > 1 else f"{p}" for p, e in factorint(n).items())
        print(f"{n:>4} {fac:>10} {e2cnt:>6} {e2_anti:>7} {str(e2cnt==e2_anti):>9} "
              f"{norb:>4} {norb_anti:>9} {norb_other:>10} {n//4-1:>6}")
    print()
    print("HYPOTHESIS: #orb_anti == n/4 - 1 ALWAYS (the antipodal/2-power family is the universal floor),")
    print("            and #orb_other > 0 exactly when 3 | n (regular-3-gon cyclotomic relations).")
    print("            On the PRIZE shape n=2^mu, #orb_other=0 so #orbits == n/4 - 1.")
