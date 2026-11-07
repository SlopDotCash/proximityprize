#!/usr/bin/env python3
"""
SYZ50 — witness realizability at rate 1/2.

Question A (the decisive polytope):  At rate exactly 1/2 (n = 2k), does the
BALANCED-INTERIOR region intersect the BAND-REALIZABLE profile polytope?

Band-realizable Venn model (SYZ27/28/37/G172, at rate 1/2, n = 2k):
  reduced degrees      a,b,c  (sizes of the three pairwise-EXCLUSIVE overlap
                              regions S_AB,S_AC,S_BC — mutually disjoint AND
                              disjoint from the triple region T)
  triple size          t = |T|
  DISJOINTNESS         a + b + c + t <= n = 2k       (all live in the n-pt domain)
  BUDGET cap           max(a,b,c) <= k - 1 - t       (SYZ37 uniform window)
  INTERIOR slack       a + b + c   >= 2*(k-1-t) + 3  (G172)
  BALANCED interior    max(a,b,c) + 1 < (a+b+c)//2   (SYZ48.BalancedInterior)

These four inequalities are only NECESSARY conditions (a relaxation): they do not
guarantee three integer cores in the strict interior band 2n/3 < |core| < 3n/4.
With S_AB,S_AC,S_BC of sizes a,b,c, the cores are
  core_A = S_AB ∪ S_AC ∪ T ∪ P_A,  core_B = S_AB ∪ S_BC ∪ T ∪ P_B,
  core_C = S_AC ∪ S_BC ∪ T ∪ P_C,
with P_A,P_B,P_C PRIVATE (single-core) coordinates, all regions pairwise disjoint.
STRICT-BAND realizability additionally needs private counts p_X >= 0 with
  floor(2n/3)+1 <= |core_X| <= ceil(3n/4)-1   for each X, and
  a + b + c + t + p_A + p_B + p_C <= n.
Example (audit finding L129, repository review 2026-10-28): (a,b,c,t,k)=(4,5,5,3,9)
passes the relaxation, but n=18 needs every core >= 13 coordinates; the prescribed
regions give cores of sizes 12,12,13 and occupy 17 coordinates, leaving 1 private
coordinate for the 2 that are needed.  No strict-band core system exists.
`realizable` below is the relaxation; `strict_band_realizable` adds the ownership check.

ι >= 2 needs the balanced interior (SYZ47 floor discharges the rest).  So:
  is  {balanced interior}  ∩  {band-realizable, rate 1/2}  EMPTY?

Question B: the specific SYZ49 μ12 witness (a=b=c=4) — realizable at n=12?

Question C: given realizable configs, do actual on-domain ι=2 witnesses exist?
"""
from itertools import combinations


def balanced_interior(a, b, c):
    S = a + b + c
    return max(a, b, c) + 1 < S // 2


def realizable(a, b, c, t, k):
    """NECESSARY-condition relaxation of band realizability (degree/disjointness/budget
    inequalities only).  It does NOT check that integer strict-band cores exist; use
    strict_band_realizable for that."""
    n = 2 * k
    if a < 1 or b < 1 or c < 1 or t < 0:
        return False
    if a + b + c + t > n:                    # disjointness in domain
        return False
    if max(a, b, c) > k - 1 - t:             # budget cap
        return False
    if a + b + c < 2 * (k - 1 - t) + 3:      # interior slack
        return False
    return True


def band_bounds(n):
    """integer strict interior band 2n/3 < s < 3n/4, as (lo, hi) with lo <= s <= hi."""
    lo = (2 * n) // 3 + 1          # least s with 3s > 2n
    hi = (3 * n - 1) // 4          # greatest s with 4s < 3n
    return lo, hi


def strict_band_ownership(a, b, c, t, k):
    """Minimal private-coordinate allocation (p_A, p_B, p_C) making core_A = S_AB+S_AC+T+P_A,
    core_B = S_AB+S_BC+T+P_B, core_C = S_AC+S_BC+T+P_C all lie in the strict band, or None.

    Pair regions have sizes |S_AB|=a, |S_AC|=b, |S_BC|=c.  Each p_X is independently minimal
    (raising a private count only uses more coordinates), so this decides feasibility."""
    n = 2 * k
    if not realizable(a, b, c, t, k):
        return None
    lo, hi = band_bounds(n)
    bases = (a + b + t, a + c + t, b + c + t)
    if any(base > hi for base in bases):
        return None
    privates = tuple(max(0, lo - base) for base in bases)
    if a + b + c + t + sum(privates) > n:
        return None
    return privates


def strict_band_realizable(a, b, c, t, k):
    return strict_band_ownership(a, b, c, t, k) is not None


# ---- Question C: on-domain ι=2 witness search in a REALIZABLE config ------
# smallest realizable (4,4,4) profile: n=14, t=2 -> need 3 disjoint 4-subsets
# of μ14 with a constant syzygy, leaving exactly t=2 points for the triple T.

def find_witnesses(p, n, a):
    """μ_n ⊂ F_p^×; find disjoint a-subsets S_AC,S_BC and a size-a level set
    S_AB of R=W_BC/W_AC, all disjoint, leaving n-3a points for the triple."""
    assert (p - 1) % n == 0
    # a primitive n-th root of unity
    g = None
    for x in range(2, p):
        if pow(x, n, p) == 1 and all(pow(x, n//q, p) != 1
                                     for q in set(_prime_factors(n))):
            g = x; break
    mu = [pow(g, i, p) for i in range(n)]
    def Weval(S, om):                    # ∏_{s∈S}(om - s) mod p
        r = 1
        for s in S: r = (r * (om - s)) % p
        return r
    wit = []
    idx = list(range(n))
    seen = 0
    for AC in combinations(idx, a):
        rest1 = [i for i in idx if i not in AC]
        for BC in combinations(rest1, a):
            if BC[0] < AC[0]:            # dedupe AC<->BC symmetry lightly
                continue
            S_AC = [mu[i] for i in AC]; S_BC = [mu[i] for i in BC]
            rest = [i for i in rest1 if i not in BC]
            # level of R on remaining points
            level = {}
            ok = True
            for i in rest:
                om = mu[i]
                d = Weval(S_AC, om)
                if d % p == 0:
                    ok = False; break
                R = (Weval(S_BC, om) * pow(d, p-2, p)) % p
                level.setdefault(R, []).append(i)
            if not ok: continue
            seen += 1
            for R, pts in level.items():
                if len(pts) >= a:
                    for AB in combinations(pts, a):
                        leftover = n - 3*a
                        wit.append((AC, BC, tuple(AB), R, leftover))
                        if len(wit) <= 3:
                            print(f"    WITNESS: S_AC(idx)={AC} S_BC(idx)={BC} "
                                  f"S_AB(idx)={AB} level R={R} triple_leftover={leftover}")
    return wit, seen

def _prime_factors(m):
    f=[]; d=2
    while d*d<=m:
        while m%d==0: f.append(d); m//=d
        d+=1
    if m>1: f.append(m)
    return f

def question_a(kmax=40):
    """Enumerate balanced-interior profiles (a<=b<=c) passing the relaxation, and the
    subset that is strict-band realizable (integer cores with private ownership)."""
    relaxed, strict = [], []
    for k in range(2, kmax + 1):
        for t in range(0, k):
            for a in range(1, k):
                for b in range(a, k):        # a<=b<=c WLOG
                    for c in range(b, k):
                        if balanced_interior(a, b, c) and realizable(a, b, c, t, k):
                            relaxed.append((k, a, b, c, t))
                            if strict_band_realizable(a, b, c, t, k):
                                strict.append((k, a, b, c, t))
    return relaxed, strict


def main():
    # ---- Question A: enumerate the intersection polytope ----------------------
    print("="*70)
    print("QUESTION A: balanced-interior ∩ band-realizable at rate 1/2 (n=2k)")
    print("="*70)
    relaxed, hits = question_a()
    print(f"total (k<=40, a<=b<=c) balanced-interior points passing the NECESSARY "
          f"relaxation: {len(relaxed)}")
    print(f"  of which STRICT-BAND realizable (integer cores 2n/3<|core|<3n/4 with "
          f"private ownership): {len(hits)}")
    print(f"  relaxation-only (no strict-band core system): {len(relaxed) - len(hits)}"
          f"  e.g. (a,b,c,t,k)=(4,5,5,3,9): relaxed={realizable(4,5,5,3,9)} "
          f"strict={strict_band_realizable(4,5,5,3,9)}")
    if hits:
        hits.sort(key=lambda x: (x[0], -(x[1]+x[2]+x[3])))
        print("smallest-k strict-band examples:")
        kmin = hits[0][0]
        for h in [h for h in hits if h[0] <= kmin+1][:12]:
            k, a, b, c, t = h
            S = a+b+c
            print(f"  n={2*k:3d} k={k:2d}  (a,b,c)=({a},{b},{c}) t={t}  "
                  f"S={S} max={max(a,b,c)} floorS/2={S//2}  budget={k-1-t}  "
                  f"privates={strict_band_ownership(a, b, c, t, k)}")
    else:
        print("  *** EMPTY — balanced interior is VACUOUS on strict-band profiles ***")

    # ---- Question B: the SYZ49 μ12 witness ------------------------------------
    print("\n" + "="*70)
    print("QUESTION B: SYZ49 witness profile (a,b,c)=(4,4,4) at rate 1/2")
    print("="*70)
    for k in [6, 7, 8]:
        n = 2*k
        ok_ts = [t for t in range(0, k) if realizable(4, 4, 4, t, k)]
        strict_ts = [t for t in range(0, k) if strict_band_realizable(4, 4, 4, t, k)]
        forced = []
        for t in range(0, k):
            # band constraints WITHOUT domain disjointness (algebra-only)
            if max(4, 4, 4) <= k-1-t and 4+4+4 >= 2*(k-1-t)+3:
                forced.append(t)
        fits = [t for t in forced if 4+4+4+t <= n]
        print(f"  n={n} k={k}: band-forced t (ignoring domain) = {forced}; "
              f"of those, DOMAIN-FIT (a+b+c+t<=n) = {fits}; relaxation t = {ok_ts}; "
              f"strict-band t = {strict_ts}")
    print("  => n=12 (μ12, the SYZ49 domain): no t passes even the necessary relaxation.")

    print("\n" + "="*70)
    print("QUESTION C: on-domain ι=2 witness in STRICT-BAND config n=14,t=2 (μ14⊂F29)")
    print("="*70)
    assert strict_band_ownership(4, 4, 4, 2, 7) == (0, 0, 0)
    w, seen = find_witnesses(29, 14, 4)
    print(f"  disjoint-pair scans: {seen};  size-4 level-set witnesses found: {len(w)}")
    print("  (n-3a = 2 = t, so the leftover is exactly the triple region and every core has"
          " size 10, inside the strict band 10 <= s <= 10 for n=14)")
    if not w:
        print("  *** NO on-domain constant syzygy with room for the triple: "
              "realizable configs carry NO ι=2 witness (μ14) ***")

    # ---- Question D: lift ceiling on the realizable n=14 witness --------------
    # cores size s = a+b+t = 4+4+2 = 10 (each core = its two pairwise regions + T).
    # pencil-yield cap = sum(n - s_i); strict interior forces <= n-1 (SYZ22/SYZ28).
    print("\n" + "="*70)
    print("QUESTION D: pencil-yield lift ceiling on n=14 realizable witness")
    print("="*70)
    n, a, b, c, t = 14, 4, 4, 4, 2
    s = a + b + t   # each core hosts two pairwise regions + the triple
    cap = 3 * (n - s)
    print(f"  core size s = a+b+t = {s};  n-s = {n-s};  sum(n-s_i)=3*(n-s) = {cap}")
    print(f"  budget n-1 = {n-1}.  cap <= budget? {cap <= n-1}  "
          f"(so even a full bad-lift cannot outrun the SYZ22 budget)")


if __name__ == "__main__":
    main()
