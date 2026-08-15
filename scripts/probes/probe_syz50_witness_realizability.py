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

ι >= 2 needs the balanced interior (SYZ47 floor discharges the rest).  So:
  is  {balanced interior}  ∩  {band-realizable, rate 1/2}  EMPTY?

Question B: the specific SYZ49 μ12 witness (a=b=c=4) — realizable at n=12?

Question C: given realizable configs, do actual on-domain ι=2 witnesses exist?
"""

def balanced_interior(a, b, c):
    S = a + b + c
    return max(a, b, c) + 1 < S // 2

def realizable(a, b, c, t, k):
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

# ---- Question A: enumerate the intersection polytope ----------------------
print("="*70)
print("QUESTION A: balanced-interior ∩ band-realizable at rate 1/2 (n=2k)")
print("="*70)
hits = []
for k in range(2, 41):
    for t in range(0, k):
        for a in range(1, k):
            for b in range(a, k):        # a<=b<=c WLOG
                for c in range(b, k):
                    if realizable(a, b, c, t, k) and balanced_interior(a, b, c):
                        hits.append((k, a, b, c, t))
print(f"total (k<=40, a<=b<=c) feasible balanced-interior realizable points: {len(hits)}")
if hits:
    hits.sort(key=lambda x: (x[0], -(x[1]+x[2]+x[3])))
    print("smallest-k examples:")
    kmin = hits[0][0]
    for h in [h for h in hits if h[0] <= kmin+1][:12]:
        k,a,b,c,t = h
        S=a+b+c
        print(f"  n={2*k:3d} k={k:2d}  (a,b,c)=({a},{b},{c}) t={t}  "
              f"S={S} max={max(a,b,c)} floorS/2={S//2}  budget={k-1-t}")
else:
    print("  *** EMPTY — balanced interior is VACUOUS on realizable profiles ***")

# ---- Question B: the SYZ49 μ12 witness ------------------------------------
print("\n" + "="*70)
print("QUESTION B: SYZ49 witness profile (a,b,c)=(4,4,4) at rate 1/2")
print("="*70)
for k in [6, 7, 8]:
    n = 2*k
    ok_ts = [t for t in range(0, k) if realizable(4,4,4,t,k)]
    forced = []
    for t in range(0, k):
        # band constraints WITHOUT domain disjointness (algebra-only)
        if max(4,4,4) <= k-1-t and 4+4+4 >= 2*(k-1-t)+3:
            forced.append(t)
    fits = [t for t in forced if 4+4+4+t <= n]
    print(f"  n={n} k={k}: band-forced t (ignoring domain) = {forced}; "
          f"of those, DOMAIN-FIT (a+b+c+t<=n) = {fits}; fully-realizable t = {ok_ts}")
print("  => n=12 (μ12, the SYZ49 domain): see whether any t survives both.")

# ---- Question C: on-domain ι=2 witness search in a REALIZABLE config ------
# smallest realizable (4,4,4) profile: n=14, t=2 -> need 3 disjoint 4-subsets
# of μ14 with a constant syzygy, leaving exactly t=2 points for the triple T.
from itertools import combinations

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

print("\n" + "="*70)
print("QUESTION C: on-domain ι=2 witness in REALIZABLE config n=14,t=2 (μ14⊂F29)")
print("="*70)
w, seen = find_witnesses(29, 14, 4)
print(f"  disjoint-pair scans: {seen};  size-4 level-set witnesses found: {len(w)}")
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
