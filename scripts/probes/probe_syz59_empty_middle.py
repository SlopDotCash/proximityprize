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
linear algebra, and (2) checks three hand-built balanced (d,d,d) examples, d ∈ {3,4,5}, in the
PRODUCT convention: each has δ₁ = max(a,b,c), so none has max(a,b,c) < δ₁ ≤ ⌊S/2⌋ − 2.

Scope (read before citing (2) as an "empty middle" census):
  * Every example in (2) is built as f = 3g − 2h, i.e. with a constant syzygy planted by
    construction.  Its δ₁ = max(a,b,c) is therefore forced by the carrier; the three examples
    are not an enumeration of split locator triples, and f is not checked to split on any
    evaluation domain.  The absence of a middle witness here says nothing about triples outside
    this constant-syzygy carrier.
  * A genuine on-domain middle witness exists: SYZ71 (`probe_syz71_verify_f41.py`) replays a
    (6,6,6) band triple on mu_20 ⊂ F_41 with linear cofactors (29+10X, 30+X), product degree 7,
    and no constant syzygy.  So "the realizable middle is empty" is false in general; it is not
    a bad-scalar or prize counterexample either.
  * `min_syzygy_product_degree` grades each slot by its own polynomial degree (slot i gets
    cofactor degree ≤ D − deg f_i), so it minimises the product degree also on unequal-degree
    inputs; a uniform cofactor bound does not (see scripts/tests/test_syz_generator_gap.py).
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


def _degree(P, p):
    """Degree of a coefficient list (low->high) over F_p; -1 for the zero polynomial."""
    return max((i for i, x in enumerate(P) if x % p), default=-1)


def _graded_syzygies(polys, p, bounds):
    """Basis of the syzygies sum_i s_i P_i = 0 with deg s_i <= bounds[i] (bounds[i] < 0 forces
    s_i = 0).  Each basis vector is returned as a list of per-slot coefficient lists."""
    sizes = [max(b + 1, 0) for b in bounds]
    offsets = [sum(sizes[:i]) for i in range(len(sizes))]
    nvars = sum(sizes)
    if nvars == 0:
        return []
    maxdeg = max(len(P) - 1 + sz - 1 for P, sz in zip(polys, sizes) if sz)
    rows = []
    for d in range(maxdeg + 1):
        row = [0] * nvars
        for i, P in enumerate(polys):
            for j in range(sizes[i]):
                k = d - j  # coeff index in P_i
                if 0 <= k < len(P):
                    row[offsets[i] + j] = (row[offsets[i] + j] + P[k]) % p
        rows.append(row)
    return [[vec[offsets[i]:offsets[i] + sizes[i]] for i in range(len(polys))]
            for vec in nullspace(rows, nvars, p)]


def syzygy_degrees(slots, polys, p):
    """(product degree, cofactor degree) of a nonzero syzygy given by per-slot coefficients."""
    degs = [_degree(P, p) for P in polys]
    sdegs = [_degree(s, p) for s in slots]
    product = max(degs[i] + sdegs[i] for i in range(len(slots)) if sdegs[i] >= 0)
    return product, max(sdegs)


def has_constant_syzygy(polys, p):
    """True iff some nonzero constant vector (c_i) has sum_i c_i P_i = 0 over F_p."""
    return bool(_graded_syzygies(polys, p, [0] * len(polys)))


def min_syzygy_product_degree(polys, p, Dmax):
    """Minimal max-slot PRODUCT degree max_i deg(s_i P_i) of a nonzero syzygy, searched over the
    product bound D = 0..Dmax with the slot-specific grading deg s_i <= D - deg P_i.  Returns
    (product_deg, cofactor_deg) where cofactor_deg is the cofactor degree of one syzygy attaining
    the minimum, or (None, None) if no syzygy has product degree <= Dmax.

    For equal input degrees d this agrees with searching a uniform cofactor bound t (product
    degree d + t); for unequal degrees only the slot-specific grading is a minimiser."""
    degs = [_degree(P, p) for P in polys]
    for D in range(0, Dmax + 1):
        basis = _graded_syzygies(polys, p, [D - d for d in degs])
        if basis:
            product, cofactor = syzygy_degrees(basis[0], polys, p)
            assert product == D, "graded search must attain its own bound"
            return product, cofactor
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
        pd, cd = min_syzygy_product_degree(polys, p, 12)
        S = 4 + 4 + 4
        print(f"  p={p}: min syzygy  product_deg={pd}  cofactor_deg={cd}  "
              f"max(a,b,c)=4  ⌊S/2⌋={S//2}  gap={S-2*pd}  ι={S//2-pd}")
        assert cd == 0, "constant syzygy must have cofactor degree 0"
        assert pd == 4, "product-degree must equal max(a,b,c)=4 (SYZ47 floor attained)"
        assert pd == cd + 4, "bridge product = cofactor + max"
    print("  bridge OK: cofactor δ₁=0  ⟺  product δ₁=max=4  (floor TIGHT, not violated)")


def check_empty_middle():
    print("\n=== (2) floor attainment (product convention) on three planted f = 3g - 2h triples ===")
    print("    (constant syzygy planted by construction; not a census of split locator triples)")
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
        pd, cd = min_syzygy_product_degree(polys, p, S)
        floor = max(a, b, c)
        middle = floor < pd <= (S // 2) - 2
        rows.append((S, floor, pd, S // 2, middle))
        print(f"  (a,b,c)=({a},{b},{c}) S={S}: δ₁(product)={pd}  floor=max={floor}  "
              f"⌊S/2⌋={S//2}  middle={middle}")
    assert all(pd == floor for (_, floor, pd, _, _) in rows), "floor should be attained"
    assert not any(m for *_, m in rows), "no middle witnesses"
    print("  floor OK: each planted constant-syzygy example has δ₁ = max (floor attained).")
    print("  (Not an empty-middle theorem: SYZ71 replays a genuine product-degree-7 (6,6,6)")
    print("   middle witness on mu_20 ⊂ F_41; see probe_syz71_verify_f41.py.)")


if __name__ == "__main__":
    check_bridge()
    check_empty_middle()
    print("\nALL CHECKS PASS")
