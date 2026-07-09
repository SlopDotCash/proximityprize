#!/usr/bin/env python3
"""[sweep][A08]  Window-INTERIOR worst monomial direction dir(a,b) with b-a>1.

ACTIONABLE A08: with an EXACT Z[zeta_n] enumerator, for window-INTERIOR directions dir(a,b) with
b-a>1 (NOT the refuted dir(k+1,k+2)/e_2=0 near-capacity family), enumerate #bad at
rho in {1/2,1/4,1/8,1/16} for n=8,16,32 over F_q and char-0; decide O(n) vs super-linear; derive
the b-a=2 symmetric-function constraint explicitly (the analogue of e_2=0).

SETUP.  Smooth RS[k] on mu_n.  Monomial line dir(a,b): u0=X^b, u1=X^a.
  B(a,b,w) = { gamma : (X^b + gamma X^a) mod m_S has degree < k for some |S|=w subset of mu_n }.
m_S=prod_{x in S}(X-x), deg w; delta=1-w/n.  Closeness <=> the w-k top coeffs (X^k..X^{w-1}) of
P_gamma=(X^b mod m_S)+gamma(X^a mod m_S) all vanish: w-k equations, one unknown gamma.

EXACT enumerator: cyclotomic_exact_enumerator.py (basis zeta^0..zeta^{n/2-1}, zeta^{n/2}=-1).
We run BOTH char-0 (Z[zeta_n]) and char-p (F_q) and compare.

CONSISTENCY-CHECK TRICK (char-0): a candidate gamma exists iff the high-coeff rows are pairwise
proportional in R=Z[zeta_n].  We pick a pivot row and verify the rest by EXACT cross-multiplication
Pb[j]*Pa[piv]==Pb[piv]*Pa[j] in R (no division).  Distinct gamma are then counted by evaluating the
(num,den) pair at zeta in a single large prime (an algebraic gamma is determined by one generic value;
we double-check with a 2nd prime).
"""
import sys, os
from itertools import combinations
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cyclotomic_exact_enumerator import (
    ZetaRing, monomial_mod_ring, gen_mu, monomial_mod_Fq, esym_Fq,
)

_MU_CACHE = {}
def mu(q, n):
    if (q, n) not in _MU_CACHE:
        _MU_CACHE[(q, n)] = gen_mu(q, n)
    return _MU_CACHE[(q, n)]

# ---------------------------------------------------------------- char-p enumeration
def bad_dir_Fq(n, k, a, b, q, w):
    g = mu(q, n)
    if g is None:
        return None
    bad = set()
    inv = lambda x: pow(x, q - 2, q)
    for Sidx in combinations(range(n), w):
        vals = [g[i] for i in Sidx]
        Pa = monomial_mod_Fq(vals, a, q)
        Pb = monomial_mod_Fq(vals, b, q)
        gamma = None; ok = True
        for j in range(k, w):
            ca, cb = Pa[j] % q, Pb[j] % q
            if ca == 0:
                if cb != 0:
                    ok = False; break
            else:
                cand = (-cb * inv(ca)) % q
                if gamma is None:
                    gamma = cand
                elif gamma != cand:
                    ok = False; break
        if ok and gamma is not None and gamma != 0:
            bad.add(gamma)
    seen = set(); cosets = 0
    for gm in bad:
        if gm in seen: continue
        cosets += 1
        for z in g: seen.add(gm * z % q)
    return len(bad), cosets

# ---------------------------------------------------------------- char-0 enumeration (exact)
def bad_dir_char0(n, k, a, b, w, p1=40961, p2=59393):
    """Return (#distinct char-0 gamma!=0, #valid S).  Validity & gamma computed exactly in Z[zeta_n];
    distinct gamma counted by evaluating exact (num,den) at zeta in two large primes (q=1 mod n)."""
    R = ZetaRing(n)
    g1, g2 = mu(p1, n), mu(p2, n)
    keys = set(); valid_S = 0
    rows = list(range(k, w))
    for Sidx in combinations(range(n), w):
        Pa = monomial_mod_ring(R, list(Sidx), a)
        Pb = monomial_mod_ring(R, list(Sidx), b)
        piv = None
        for j in rows:
            if not R.is_zero(Pa[j]):
                piv = j; break
        if piv is None:
            # gamma unconstrained by these rows: only valid if all Pb rows vanish too (gamma free => not discrete)
            if all(R.is_zero(Pb[j]) for j in rows):
                valid_S += 1
            continue
        ok = True
        for j in rows:
            lhs = R.mul(Pb[j], Pa[piv]); rhs = R.mul(Pb[piv], Pa[j])
            if not R.is_zero(R.sub(lhs, rhs)):
                ok = False; break
        if not ok:
            continue
        valid_S += 1
        numv = R.smul(-1, Pb[piv]); denv = Pa[piv]
        sig = []
        for (q, gg) in ((p1, g1), (p2, g2)):
            z = gg[1]
            nu = de = 0; zp = 1
            for c in numv:
                nu = (nu + c * zp) % q; zp = zp * z % q
            zp = 1
            for c in denv:
                de = (de + c * zp) % q; zp = zp * z % q
            sig.append((nu * pow(de, q - 2, q)) % q if de else None)
        keys.add(tuple(sig))
    keys.discard((0,) * 2)
    return len(keys), valid_S

# ---------------------------------------------------------------- the explicit b-a=2 constraint (verified)
def verify_ba2_constraint(n=16, p=193):
    """For dir(w-1, w+1) at k=w-2 (the 2-row b-a=2 cell), the derivation gives:
        gamma = e_2 - e_1^2 ,   CONSTRAINT  e_3 = e_1 e_2 .
    Verify it exactly against the enumerator over F_p (the analogue of 'gamma=-e_1, e_2=0')."""
    w = 6; a, b, k = w - 1, w + 1, w - 2
    g = mu(p, n)
    checked = 0; matched = 0
    for Sidx in combinations(range(n), w):
        vals = [g[i] for i in Sidx]
        e = esym_Fq(vals, p)  # e[0..w]
        e1, e2, e3 = e[1] % p, e[2] % p, e[3] % p
        constraint = ((e3 - e1 * e2) % p == 0)
        Pa = monomial_mod_Fq(vals, a, p); Pb = monomial_mod_Fq(vals, b, p)
        # enumerator's verdict for this S:
        gamma = None; ok = True
        for j in range(k, w):
            ca, cb = Pa[j] % p, Pb[j] % p
            if ca == 0:
                if cb != 0: ok = False; break
            else:
                cand = (-cb * pow(ca, p - 2, p)) % p
                if gamma is None: gamma = cand
                elif gamma != cand: ok = False; break
        enum_bad = ok and gamma is not None
        checked += 1
        if enum_bad == constraint:
            if constraint:
                pred = (e2 - e1 * e1) % p
                if gamma is None or pred == gamma % p:
                    matched += 1
            else:
                matched += 1
    print(f"  [b-a=2 constraint verify] n={n} p={p} w={w} dir({a},{b}), k={k}: "
          f"{matched}/{checked} subsets agree with  'e_3=e_1 e_2  &  gamma=e_2-e_1^2'")
    return matched == checked

# ---------------------------------------------------------------- main
def feasible(n, w, cap=400000):
    from math import comb
    return comb(n, w) <= cap

if __name__ == "__main__":
    print("=" * 92)
    print("[A08] Window-INTERIOR monomial direction dir(a,b) with b-a=2 (a=w-1,b=w+1).")
    print("       delta=1-w/n.  k=rho*n fixed; rows = w-k.   #bad over n,rho,w.")
    print("=" * 92)
    PRIMES = {8: [41, 97, 337, 769], 16: [97, 193, 353, 769], 32: [97, 193, 449, 769]}
    for n in (8, 16, 32):
        for rho in (0.5, 0.25, 0.125, 0.0625):
            k = int(round(rho * n))
            if k < 1 or k > n - 3:
                continue
            johnson = 1 - rho ** 0.5; capacity = 1 - rho
            printed_header = False
            for w in range(k + 2, n):
                delta = 1 - w / n
                if not (johnson < delta < capacity):
                    continue
                if not feasible(n, w):
                    if not printed_header:
                        print(f"\n--- n={n} rho={rho} k={k}  window=({johnson:.3f},{capacity:.3f}) ---"); printed_header = True
                    print(f"    w={w} (delta={delta:.3f}): SKIPPED (C(n,w) too large)")
                    continue
                a, b = w - 1, w + 1
                rows = w - k
                fq = []
                for q in PRIMES[n]:
                    r = bad_dir_Fq(n, k, a, b, q, w)
                    fq.append((q, None if r is None else r[0], None if r is None else r[1]))
                c0, _ = bad_dir_char0(n, k, a, b, w)
                if not printed_header:
                    print(f"\n--- n={n} rho={rho} k={k}  window=({johnson:.3f},{capacity:.3f}) ---"); printed_header = True
                big = fq[-1][1]
                flag = "" if big is None else ("<=n" if big <= n else "~%.2fn" % (big / n))
                fqs = ", ".join(f"{q}:{nb}({co})" for (q, nb, co) in fq)
                print(f"    w={w} d={delta:.3f} dir({a},{b}) rows={rows}: char0={c0}  F_q[{fqs}]  [big {flag}]")
    print("\n" + "=" * 92)
    print("Explicit b-a=2 symmetric-function constraint (analogue of e_2=0):")
    print("  dir(w-1,w+1) at k=w-2:  gamma = e_2 - e_1^2 ,   CONSTRAINT  e_3 = e_1 e_2 .")
    verify_ba2_constraint(8, 41)
    verify_ba2_constraint(16, 193)
