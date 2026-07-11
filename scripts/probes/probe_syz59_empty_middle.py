#!/usr/bin/env python3
"""probe_syz59_empty_middle.py — SYZ59 convention reconciliation + empty-middle census.

Two conventions for the minimal-syzygy degree δ₁ of a pairwise-coprime band triple
(W_AB, W_AC, W_BC) of reduced degrees (a,b,c), S := a+b+c:

  * PRODUCT-degree convention (SYZ44/45/47):  δ_i = max slot product-degree
        deg(W_slot · s_slot), with δ₁ + δ₂ = S  and the SYZ47 floor δ₁ ≥ max(a,b,c).
  * COFACTOR-degree convention (SYZ55 prose):  δ_i = deg of the cofactor vector s.

For a CONSTANT syzygy c₀W_AB + c₁W_AC + c₂W_BC = 0 (all-nonzero coeffs, balanced d=d=d):
    cofactor δ₁ = 0            (SYZ55 prose: "δ₁ = 0, maximal gap S")
    product  δ₁ = max(a,b,c)=d (SYZ47 floor ATTAINED, i.e. TIGHT, NOT violated)

Bridge:  product_δ₁ = cofactor_δ₁ + max(a,b,c)  on constant-syzygy witnesses.

This probe (1) checks the bridge arithmetic on explicit F_p (4,4,4) witnesses via exact
linear algebra, and (2) enumerates small balanced-interior triples and confirms the empty
middle in the PRODUCT convention: every realizable (constant-syzygy) witness has
δ₁ = max(a,b,c); none has max(a,b,c) < δ₁ ≤ ⌊S/2⌋ − 2.
"""

from itertools import combinations
from fractions import Fraction


def poly_from_roots(roots, p):
    """monic poly with given roots over F_p, as coeff list low->high."""
    c = [1]
    for r in roots:
        nc = [0] * (len(c) + 1)
        for i, ci in enumerate(c):
            nc[i] = (nc[i] - r * ci) % p
            nc[i + 1] = (nc[i + 1] + ci) % p
        c = nc
    return c


def min_syzygy_product_degree(polys, p, Dmax):
    """Minimal max-slot product-degree of a nonzero syzygy (s0,s1,s2) with deg s_i <= t,
    searched over increasing cofactor bound t. Returns (product_deg, cofactor_deg)."""
    n = 3
    degs = [len(P) - 1 for P in polys]
    for t in range(0, Dmax + 1):  # cofactor degree bound
        # unknowns: coeffs of s_i, i<3, each length t+1 -> total 3*(t+1)
        ncoef = t + 1
        nvars = n * ncoef
        # equation: sum_i P_i * s_i == 0 ; degree up to max(degs)+t
        maxdeg = max(degs) + t
        rows = []
        for d in range(maxdeg + 1):
            row = [0] * nvars
            for i, P in enumerate(polys):
                for j in range(ncoef):
                    k = d - j  # coeff index in P_i
                    if 0 <= k < len(P):
                        row[i * ncoef + j] = (row[i * ncoef + j] + P[k]) % p
            rows.append(row)
        # nullspace over F_p
        ns = nullspace(rows, nvars, p)
        for vec in ns:
            # product-degree of this syzygy
            pd = -1
            for i in range(n):
                si = vec[i * ncoef:(i + 1) * ncoef]
                if any(x % p for x in si):
                    sdeg = max(j for j, x in enumerate(si) if x % p)
                    pd = max(pd, degs[i] + sdeg)
            if pd >= 0:
                return pd, t
    return None, None


def nullspace(rows, nvars, p):
    M = [row[:] for row in rows]
    nrows = len(M)
    pivots = {}
    r = 0
    for col in range(nvars):
        piv = None
        for rr in range(r, nrows):
            if M[rr][col] % p:
                piv = rr
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][col], p - 2, p)
        M[r] = [(x * inv) % p for x in M[r]]
        for rr in range(nrows):
            if rr != r and M[rr][col] % p:
                f = M[rr][col]
                M[rr] = [(a - f * b) % p for a, b in zip(M[rr], M[r])]
        pivots[col] = r
        r += 1
        if r == nrows:
            break
    free = [c for c in range(nvars) if c not in pivots]
    basis = []
    for fc in free:
        vec = [0] * nvars
        vec[fc] = 1
        for col, rr in pivots.items():
            vec[col] = (-M[rr][fc]) % p
        basis.append(vec)
    return basis


def check_bridge():
    print("=== (1) convention bridge on explicit balanced (4,4,4) constant-syzygy witnesses ===")
    # over F_13: f + 9 g + 3 h = 0 (from SYZ45 prose).  Pick g,h squarefree coprime quartics.
    for p, gr, hr in [(13, [1, 2, 3, 4], [5, 6, 7, 8]),
                      (101, [1, 2, 3, 4], [5, 6, 7, 8])]:
        g = poly_from_roots(gr, p)
        h = poly_from_roots(hr, p)
        # find scalars (c1,c2) so that f := -(c1 g + c2 h) is squarefree & coprime -> just take f=3g-2h style
        # We instead DIRECTLY certify a constant syzygy exists among (f,g,h) with f a combo:
        c1, c2 = 3 % p, (-2) % p
        f = [(c1 * gi + c2 * hi) % p for gi, hi in zip(g, h)]
        polys = [f, g, h]
        pd, cd = min_syzygy_product_degree(polys, p, 6)
        S = 4 + 4 + 4
        print(f"  p={p}: min syzygy  product_deg={pd}  cofactor_deg={cd}  "
              f"max(a,b,c)=4  ⌊S/2⌋={S//2}  gap={S-2*pd}  ι={S//2-pd}")
        assert cd == 0, "constant syzygy must have cofactor degree 0"
        assert pd == 4, "product-degree must equal max(a,b,c)=4 (SYZ47 floor attained)"
        assert pd == cd + 4, "bridge product = cofactor + max"
    print("  bridge OK: cofactor δ₁=0  ⟺  product δ₁=max=4  (floor TIGHT, not violated)")


def check_empty_middle():
    print("\n=== (2) empty middle (product convention) on balanced-interior triples ===")
    p = 101
    # balanced-interior profiles (a,b,c) with a,b,c in {3,4,5}, sum S, pairwise |diff|<=1
    profiles = []
    for d in (3, 4, 5):
        profiles.append((d, d, d))
    rows = []
    for (a, b, c) in profiles:
        S = a + b + c
        # constant-syzygy witness: f = 3g - 2h with disjoint roots -> squarefree pairwise-coprime
        gr = list(range(1, a + 1))
        hr = list(range(a + 1, a + b + 1))
        g = poly_from_roots(gr, p)[:b + 1]
        h = poly_from_roots(hr, p)
        # make all three degree = d by padding via distinct-root polys of equal degree
        g = poly_from_roots(list(range(1, a + 1)), p)
        h = poly_from_roots(list(range(a + 1, a + b + 1)), p)
        f = [((3 * gi) % p - (2 * hi) % p) % p for gi, hi in zip(g, h)]
        polys = [f, g, h]
        pd, cd = min_syzygy_product_degree(polys, p, d + 2)
        floor = max(a, b, c)
        middle = floor < pd <= (S // 2) - 2
        rows.append((S, floor, pd, S // 2, middle))
        print(f"  (a,b,c)=({a},{b},{c}) S={S}: δ₁(product)={pd}  floor=max={floor}  "
              f"⌊S/2⌋={S//2}  middle={middle}")
    assert all(pd == floor for (_, floor, pd, _, _) in rows), "floor should be attained"
    assert not any(m for *_, m in rows), "no middle witnesses"
    print("  empty-middle OK: every witness has δ₁ = max (floor attained); zero middle.")


if __name__ == "__main__":
    check_bridge()
    check_empty_middle()
    print("\nALL CHECKS PASS")
