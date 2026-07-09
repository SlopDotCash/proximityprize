"""
A16 — Exact char-0 closed form: #orbits of size-4, e_2=0, nonzero-e_1 subsets of mu_n = n/4 - 1.

mu_n = {zeta^j : j in 0..n-1}, zeta = primitive n-th root of unity, n = 2^mu.
We count 4-element SUBSETS S = {zeta^a, zeta^b, zeta^c, zeta^d} (distinct exponents mod n) with
  e_2(S) = sum of pairwise products = 0   (char-0, exact in Z[zeta_n] / cyclotomic)
  e_1(S) = sum of the four roots != 0
under the action of mu_n: S |-> zeta^t * S = {zeta^{a+t}, ...}.

This script:
  (1) EXACTLY (over Q(zeta_n), no floating point) enumerates 4-subsets with e_2=0, e_1!=0
      and counts mu_n-orbits, for n = 8,16,32,64.
  (2) Prints the orbit count and compares to n/4 - 1.
  (3) Dumps a canonical representative of each orbit (exponent multiset, normalized so min exp = 0)
      to expose the STRUCTURE the Lean proof must capture.

KEY ALGEBRAIC FACT we exploit / verify:
  Write the 4 exponents as a multiset {a,b,c,d} in Z/n. e_2 = sum_{i<j} zeta^{exp_i+exp_j}.
  e_2 = 0 is a vanishing sum of 6 n-th roots of unity. By Lam-Leung (n = 2^mu, a prime power),
  every vanishing sum of n-th roots is a Z>=0-combination of "rotated antipodal pairs"
  (1 + zeta^{n/2})*zeta^j = zeta^j + zeta^{j+n/2}, since 2 is the only prime dividing n.
  So the 6 pairwise-sum exponents {a+b,a+c,a+d,b+c,b+d,c+d} must pair up into 3 antipodal pairs
  (each pair differing by n/2 mod n). We verify this combinatorial characterization too.
"""

import itertools
from fractions import Fraction

def exact_e2_is_zero(exps, n):
    """exps: 4-tuple of exponents in Z/n. Return True iff sum_{i<j} zeta^{e_i+e_j} = 0 in Z[zeta_n].
       Represent the sum as a vector of coefficients on {zeta^0,...,zeta^{n-1}}, then reduce mod
       the cyclotomic Phi_n. For n=2^mu, Phi_n = X^{n/2}+1, so zeta^{n/2}=-1: reduce exponents
       mod n into [0,n) then fold the top half: coeff[j] -= coeff[j+n/2] for j in [0,n/2)."""
    half = n // 2
    coeff = [0] * n
    pairs = list(itertools.combinations(range(4), 2))
    for (i, j) in pairs:
        coeff[(exps[i] + exps[j]) % n] += 1
    # reduce mod Phi_{2^mu} = X^{n/2}+1  : zeta^{j+half} = -zeta^j
    red = [0] * half
    for j in range(n):
        if j < half:
            red[j] += coeff[j]
        else:
            red[j - half] -= coeff[j]
    return all(c == 0 for c in red)

def exact_e1_is_zero(exps, n):
    """sum of the 4 roots zeta^{e_i} == 0 in Z[zeta_n]?"""
    half = n // 2
    coeff = [0] * n
    for e in exps:
        coeff[e % n] += 1
    red = [0] * half
    for j in range(n):
        if j < half:
            red[j] += coeff[j]
        else:
            red[j - half] -= coeff[j]
    return all(c == 0 for c in red)

def antipodal_pairing_ok(exps, n):
    """Check the 6 pairwise-sum exponents pair into 3 antipodal (diff = n/2) pairs."""
    half = n // 2
    sums = sorted(((exps[i] + exps[j]) % n) for i, j in itertools.combinations(range(4), 2))
    multiset = {}
    for s in sums:
        multiset[s] = multiset.get(s, 0) + 1
    # greedily match s with (s+half)%n
    cnt = dict(multiset)
    used = 0
    keys = sorted(cnt.keys())
    for s in keys:
        while cnt.get(s, 0) > 0:
            t = (s + half) % n
            if cnt.get(t, 0) > 0 and (t != s):
                cnt[s] -= 1
                cnt[t] -= 1
                used += 1
            elif t == s:
                # antipode equals itself impossible for half>0; a self-coeff>=2 cannot pair antipodally
                return False
            else:
                return False
    return used == 3

def canonical_orbit_rep(exps, n):
    """Canonical key for the mu_n-orbit: translate so multiset min-rotation is lexicographically least.
       Orbit = {exps + t mod n : t in Z/n} as a multiset (4-subset)."""
    base = tuple(sorted(e % n for e in exps))
    best = None
    for t in range(n):
        shifted = tuple(sorted((e + t) % n for e in exps))
        if best is None or shifted < best:
            best = shifted
    return best

def enumerate_orbits(n):
    half = n // 2
    orbits = set()
    all_subsets = 0
    e2zero_count = 0
    e2zero_e1nonzero = 0
    antipodal_match = 0
    for exps in itertools.combinations(range(n), 4):
        all_subsets += 1
        if not exact_e2_is_zero(exps, n):
            continue
        e2zero_count += 1
        if antipodal_pairing_ok(exps, n):
            antipodal_match += 1
        if exact_e1_is_zero(exps, n):
            continue
        e2zero_e1nonzero += 1
        orbits.add(canonical_orbit_rep(exps, n))
    return {
        "n": n,
        "all_4subsets": all_subsets,
        "e2zero": e2zero_count,
        "e2zero_match_antipodal": antipodal_match,
        "e2zero_e1nonzero": e2zero_e1nonzero,
        "num_orbits": len(orbits),
        "predicted_n_over_4_minus_1": n // 4 - 1,
        "orbit_reps": sorted(orbits),
    }

if __name__ == "__main__":
    for n in [8, 16, 32, 64]:
        r = enumerate_orbits(n)
        print(f"=== n = {n} (mu = {n.bit_length()-1}) ===")
        print(f"  4-subsets total                 : {r['all_4subsets']}")
        print(f"  with e_2 = 0                     : {r['e2zero']}")
        print(f"    of those, antipodal-paired     : {r['e2zero_match_antipodal']}  (== e_2=0 count? {r['e2zero']==r['e2zero_match_antipodal']})")
        print(f"  with e_2 = 0 AND e_1 != 0        : {r['e2zero_e1nonzero']}")
        print(f"  # mu_n-orbits                    : {r['num_orbits']}")
        print(f"  predicted n/4 - 1                : {r['predicted_n_over_4_minus_1']}")
        print(f"  MATCH                            : {r['num_orbits'] == r['predicted_n_over_4_minus_1']}")
        # show orbit reps as exponent multisets (translation-normalized) + their pairwise-diff structure
        print(f"  orbit reps (normalized exponents, first coord 0):")
        for rep in r["orbit_reps"]:
            shifted = tuple(sorted((e - rep[0]) % n for e in rep))
            print(f"      {shifted}")
        print()
