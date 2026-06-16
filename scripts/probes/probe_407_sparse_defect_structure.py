#!/usr/bin/env python3
"""
probe_407_sparse_defect_structure.py  -- WHY is the sparse-support defect count an EXCESS over 1/p?

The previous probe found T(distinct sparse defects) * p / |T_r| = 33..578 >> 1: the sparse defects
are FAR MORE COMMON than random density 1/p. This probe identifies the STRUCTURE generating them:

  HYPOTHESIS: every sparse defect at depth r is generated from the FEW shortest vectors of 𝔭
  (minimal-house elements), closed under the lattice's automorphisms:
    (i)  Z/n  rotation  z -> ζ·z   (multiply by a root of unity = cyclic shift of group coords),
    (ii) Galois  z -> z^σ  (σ ∈ Gal = (Z/n)^*, permutes power coords),
    (iii) negation, and
    (iv) sub-sum padding (add a balanced 0-pair ζ^a - ζ^a, raising r by 1).
  If so, the count is (orbit size) ~ n × |Gal| × (padding multiplicity) -- a STRUCTURED count, not
  random. That is the mechanism behind the excess, and it tells us the sparse-support sub-count is
  governed by the SHORTEST vectors of 𝔭 (the SVP minimum), not by box volume.

We:
  (A) extract the actual distinct sparse defect points for n=16,32 at the onset r, list their
      house, norm, support size (Hamming wt in power basis), and Z/n-orbit / Galois-orbit sizes;
  (B) check: is every sparse defect a Z/n-rotation and/or Galois image of ONE primitive short
      vector?  (=> the excess is exactly the automorphism orbit of the SVP-min element);
  (C) report min-house / λ_1 ratio and whether minHouse grows with r (it should NOT if it's the
      fixed SVP minimum being padded).
"""
import sys, math, itertools
from collections import defaultdict

sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, primitive_root


def prize_prime(n, beta, pmax=10**9):
    base = int(round(n ** beta)); base -= base % n; base += 1; p = base
    while p < pmax:
        if is_prime(p) and odd_part((p - 1) // n) > 1:
            return p
        p += n
    return None


def order_n_root(p, n):
    return pow(primitive_root(p), (p - 1) // (n), p)


def ang_table(n):
    D = n // 2
    return [([math.cos(2*math.pi*t*k/n) for k in range(D)],
             [math.sin(2*math.pi*t*k/n) for k in range(D)]) for t in range(1, n, 2)]


def house_norm_wt(dfold, ang):
    D = len(dfold); house = 0.0; logN = 0.0; ok = True
    for (rc, rs) in ang:
        re = im = 0.0
        for k in range(D):
            if dfold[k]:
                re += dfold[k]*rc[k]; im += dfold[k]*rs[k]
        mag = math.hypot(re, im); house = max(house, mag)
        if mag < 1e-9: ok = False
        else: logN += math.log(mag)
    wt = sum(1 for x in dfold if x != 0)
    return house, (math.exp(logN) if ok else float('nan')), wt


def canon(dz):
    """canonical sign: leading nonzero positive."""
    lead = next((x for x in dz if x != 0), 0)
    return tuple(-x for x in dz) if lead < 0 else tuple(dz)


def rotate_group(dfold, n, shift):
    """multiply z by ζ^shift: in GROUP coords c (len n) it's a cyclic shift; fold to power basis.
       We reconstruct a group vector from dfold (put +d_k at k, with the convention c_{k}=d_k,
       c_{k+D}=0), shift, then refold (ζ^{D+j} = -ζ^j)."""
    D = n // 2
    c = [0]*n
    for k in range(D): c[k] = dfold[k]
    c2 = [0]*n
    for k in range(n): c2[(k+shift) % n] = c[k]
    out = [0]*D
    for k in range(n):
        if c2[k]:
            if k < D: out[k] += c2[k]
            else: out[k-D] -= c2[k]
    return canon(out)


def galois_map(dfold, n, a):
    """z -> z^a, a in (Z/n)^*: ζ^k -> ζ^{ak}. fold."""
    D = n // 2
    out = [0]*D
    for k in range(D):
        if dfold[k]:
            kk = (a*k) % n
            if kk < D: out[kk] += dfold[k]
            else: out[kk-D] -= dfold[k]
    return canon(out)


def collect_sparse_defects(p, z, n, r, ang):
    D = n // 2
    zpow = [pow(z, k, p) for k in range(n)]
    side = defaultdict(lambda: defaultdict(int))
    for combo in itertools.combinations_with_replacement(range(n), r):
        v = 0; fold = [0]*D
        for a in combo:
            v = (v + zpow[a]) % p
            if a < D: fold[a] += 1
            else: fold[a-D] -= 1
        side[v][tuple(fold)] += 1
    pts = {}
    for v, folds in side.items():
        its = list(folds.items())
        for (fx, cx) in its:
            for (fy, cy) in its:
                if fx == fy: continue
                dz = canon(tuple(fx[k]-fy[k] for k in range(D)))
                pts[dz] = pts.get(dz, 0) + cx*cy
    return pts


def main():
    print("="*100)
    print(" #407 SPARSE DEFECT STRUCTURE: is the excess the AUTOMORPHISM ORBIT of the SVP-min vector?")
    print("="*100)
    units = lambda n: [a for a in range(1, n) if math.gcd(a, n) == 1]
    for (n, beta) in ((16, 4.0), (32, 4.0)):
        D = n//2; ang = ang_table(n)
        p = prize_prime(n, beta); z = order_n_root(p, n)
        lam1 = math.sqrt(n/2)
        print(f"\n--- n={n} D={D} p={p} (2^{math.log2(p):.1f}) λ_1~{lam1:.2f} ---")
        # find onset r
        onset = None
        for r in range(2, 6):
            pts = collect_sparse_defects(p, z, n, r, ang)
            if pts:
                onset = r; break
        if onset is None:
            print("   no sparse defect up to r=5"); continue
        for r in range(onset, min(onset+2, 6)):
            pts = collect_sparse_defects(p, z, n, r, ang)
            if not pts: continue
            # group points by (house, norm, wt) and by Z/n x Galois orbit
            # build orbit closure
            allpts = set(pts)
            seen = set(); orbits = []
            for dz in allpts:
                if dz in seen: continue
                orb = set()
                frontier = {dz}
                while frontier:
                    x = frontier.pop()
                    if x in orb: continue
                    orb.add(x)
                    for s in range(n):
                        y = rotate_group(list(x), n, s)
                        if y not in orb: frontier.add(y)
                    for a in units(n):
                        y = galois_map(list(x), n, a)
                        if y not in orb: frontier.add(y)
                # intersect orbit with the defect set
                orbit_in_set = orb & allpts
                orbits.append((dz, len(orb), len(orbit_in_set)))
                seen |= orbit_in_set
            # summary
            houses = []; norms = []; wts = []
            for dz in pts:
                h, N, w = house_norm_wt(list(dz), ang); houses.append(h); norms.append(N); wts.append(w)
            print(f"  r={r}: #distinct defect pts = {len(pts)};  #orbits(Z/n×Gal) = {len(orbits)}")
            print(f"        house: min={min(houses):.3f} max={max(houses):.3f}  (λ_1~{lam1:.2f}, "
                  f"min/λ_1={min(houses)/lam1:.3f})")
            print(f"        norm/p: {sorted(set(round(N/p,2) for N in norms if not math.isnan(N)))[:8]}")
            print(f"        support wt (power basis): min={min(wts)} max={max(wts)} (D={D})")
            for (rep, orbfull, orbin) in orbits[:6]:
                h,N,w = house_norm_wt(list(rep), ang)
                print(f"        orbit rep house={h:.3f} norm/p={N/p:.2f} wt={w}: full-orbit={orbfull}, in-defect-set={orbin}")
            if len(orbits) <= 2:
                print(f"        => ALL sparse defects are the SINGLE automorphism orbit of one SVP-min vector.")
    print("\nINTERPRETATION:")
    print(" If #orbits is tiny (1-2) and min-house ≈ λ_1 and norm/p ∈ {1,2,..}: the sparse-support")
    print(" defect set is EXACTLY the automorphism orbit of the shortest vector(s) of 𝔭 (the SVP-min),")
    print(" padded by balanced 0-pairs. The count is then n·|Gal|·(pad) — structured, NOT 1/p random,")
    print(" and governed by SVP-min, not box volume. minHouse not growing with r confirms padding.")


if __name__ == "__main__":
    main()
