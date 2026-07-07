"""
probe_wmax6_repthree.py -- the RepThree (r=3 additive-energy) reading of Wmax(6).

In SixTermResultantImproved the six roots come from an order-3 additive-energy relation
    a1 + a2 + a3 = b1 + b2 + b3,   a_i, b_j in mu_n  (here 2^M-th roots),
equivalently the SIGNED zero-sum
    a1 + a2 + a3 - b1 - b2 - b3 = 0.
Collecting equal roots gives a signed multiplicity pattern m: support -> Z with
    sum_{k} m_k * r_k = 0,   sum_{m_k > 0} m_k <= 3,  sum_{m_k < 0} (-m_k) <= 3,
i.e. net "+3 / -3" budget (a root shared by both sides cancels and drops out).

"Antipodally pairable" = the leftover (non-cancelled) pattern is a union of antipodal pairs
{z,-z} with equal signed multiplicity (m(k)=m(k+N/2)); these are the TRIVIAL relations that do
NOT contribute a genuine RepThree defect.  Wmax(6) is the max of sum_k m_k^2 over the GENUINE
(non-pairable) patterns -- this is the elementary input that sets the threshold p>(2*Wmax)^{n/4}.

We enumerate ALL (a1,a2,a3,b1,b2,b3) in mu_N^6 with a1+a2+a3=b1+b2+b3 (exact, over Q(zeta_N)),
collapse to signed multiplicities, and maximize sum m_k^2 over non-pairable ones.
"""

from itertools import product
import cmath
from collections import Counter

def roots(N):
    return [cmath.exp(2j * cmath.pi * k / N) for k in range(N)]

def antipode(k, N):
    return (k + N // 2) % N

def signed_pattern(aidx, bidx):
    """Net signed multiplicity by exponent index: +1 per a, -1 per b, collected, drop zeros."""
    c = Counter()
    for k in aidx:
        c[k] += 1
    for k in bidx:
        c[k] -= 1
    return {k: v for k, v in c.items() if v != 0}

def pairable(pat, N):
    """pattern (dict exp->mult) is a union of antipodal pairs with equal signed mult."""
    if not pat:
        return True  # empty = trivial
    for k, m in pat.items():
        if pat.get(antipode(k, N), 0) != m:
            return False
    return True

def run(N):
    R = roots(N)
    best = -1
    best_examples = []
    profile_set = set()
    tol = 1e-9
    rng = range(N)
    for a in product(rng, repeat=3):
        sa = R[a[0]] + R[a[1]] + R[a[2]]
        for b in product(rng, repeat=3):
            if abs((R[b[0]] + R[b[1]] + R[b[2]]) - sa) > tol:
                continue
            pat = signed_pattern(a, b)
            if pairable(pat, N):
                continue
            sm2 = sum(v * v for v in pat.values())
            if sm2 > best:
                best = sm2
                best_examples = [(a, b, dict(pat))]
                profile_set = {tuple(sorted(abs(v) for v in pat.values()))}
            elif sm2 == best:
                profile_set.add(tuple(sorted(abs(v) for v in pat.values())))
                if len(best_examples) < 5:
                    best_examples.append((a, b, dict(pat)))
    return best, profile_set, best_examples

if __name__ == "__main__":
    print("RepThree reading of Wmax(6): a1+a2+a3=b1+b2+b3 over mu_N (N=2^M), non-pairable max sum m^2")
    for M in (2, 3, 4, 5):
        N = 1 << M
        best, profs, ex = run(N)
        print(f"\nN=2^{M}={N}:  Wmax(6) = {best}   maximizer |mult| profiles = {sorted(profs)}")
        for (a, b, pat) in ex[:3]:
            print(f"    a-exps={a} b-exps={b}  signed pattern (exp->mult)={pat}")
    print("\nExpected: Wmax(6) = 26")
