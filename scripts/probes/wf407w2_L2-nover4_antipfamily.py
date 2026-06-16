"""
wf407-w2 / L2-nover4 — verify the ANTIPODAL family is EXACTLY {0,j,2j,n/2+j}, j=1..n/4-1.

The Sweep_A16 Lean lower bound builds reps exponentRep M j = {0, j, 2j, 2M+j}, M=n/4.
Claim: for 4|n, the antipodally-paired e_2=0, e_1!=0 orbits are EXACTLY the orbits of these,
and they are n/4 - 1 distinct orbits (j ranges 1..n/4-1; j=n/4 is excluded since e_1=0 there).

Check:
  (A) each {0,j,2j,n/2+j} has e_2=0 (ring identity, char-0) and e_1 = 1 + zeta^{2j} != 0 for j != n/4.
  (B) distinct j in 1..n/4-1 give distinct orbits.
  (C) the SET of antipodal orbit reps from full enumeration == {orbit of {0,j,2j,n/2+j} : j=1..n/4-1}.
"""

import itertools
from sympy import symbols, Poly, cyclotomic_poly, ZZ

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
    return Poly.from_dict(d, gens=X, domain=ZZ).rem(Phi).is_zero

def e2_zero(exps, n, Phi):
    return is_zero([((exps[i] + exps[j]) % n, 1) for i, j in itertools.combinations(range(4), 2)], n, Phi)

def e1_zero(exps, n, Phi):
    return is_zero([(e % n, 1) for e in exps], n, Phi)

def antip(exps, n):
    half = n // 2
    sums = [((exps[i] + exps[j]) % n) for i, j in itertools.combinations(range(4), 2)]
    cnt = {}
    for s in sums: cnt[s] = cnt.get(s, 0) + 1
    used = 0
    for s in sorted(cnt):
        while cnt.get(s, 0) > 0:
            t = (s + half) % n
            if t == s: return False
            if cnt.get(t, 0) > 0:
                cnt[s] -= 1; cnt[t] -= 1; used += 1
            else: return False
    return used == 3

def canon(exps, n):
    best = None
    for t in range(n):
        sh = tuple(sorted((e + t) % n for e in exps))
        if best is None or sh < best: best = sh
    return best

for n in [8, 12, 16, 20, 24, 28, 32, 36, 40]:
    if n % 4 != 0:
        continue
    Phi = phi_poly(n)
    M = n // 4
    half = n // 2
    # (A)+(B): family reps
    fam_reps = set()
    okA = True
    for j in range(1, M):  # 1..M-1
        S = (0, j, 2*j % n, (half + j) % n)
        if len(set(S)) != 4:
            okA = False
        if not e2_zero(S, n, Phi):
            okA = False
        if e1_zero(S, n, Phi):
            okA = False  # must be nonzero
        fam_reps.add(canon(S, n))
    # (C): full antipodal enumeration
    full_anti = set()
    for exps in itertools.combinations(range(n), 4):
        if not e2_zero(exps, n, Phi):
            continue
        if e1_zero(exps, n, Phi):
            continue
        if antip(exps, n):
            full_anti.add(canon(exps, n))
    print(f"n={n:>3} M={M:>3}: family reps={len(fam_reps)} (expect {M-1}), "
          f"family valid(e2=0,e1!=0,card4)={okA}, "
          f"full_antipodal_orbits={len(full_anti)}, "
          f"family==full_antipodal: {fam_reps == full_anti}")
