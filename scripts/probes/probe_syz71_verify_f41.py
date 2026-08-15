#!/usr/bin/env python3
"""Verify the F_41 mu_20 linear-middle witness and extract cofactors."""
from probe_syz71_linear_middle_slot import (
    gf_rank,
    mu_domain,
    remaining_rows,
    vanishing_eval,
)


def kernel_one(rows, p):
    """Return one nonzero kernel vector of a matrix over F_p."""
    M = [row[:] for row in rows]
    nrows = len(M)
    ncols = len(M[0])
    pivots = {}
    r = 0
    for col in range(ncols):
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
    free = [c for c in range(ncols) if c not in pivots]
    if not free:
        return None
    fc = free[0]
    vec = [0] * ncols
    vec[fc] = 1
    for col, rr in pivots.items():
        vec[col] = (-M[rr][fc]) % p
    return vec


def poly_mul(a, b, p):
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] = (out[i + j] + ai * bj) % p
    return out


def poly_add(a, b, p):
    n = max(len(a), len(b))
    out = [0] * n
    for i in range(n):
        av = a[i] if i < len(a) else 0
        bv = b[i] if i < len(b) else 0
        out[i] = (av + bv) % p
    return out


def poly_from_roots(roots, p):
    c = [1]
    for r in roots:
        nc = [0] * (len(c) + 1)
        for i, ci in enumerate(c):
            nc[i] = (nc[i] - r * ci) % p
            nc[i + 1] = (nc[i + 1] + ci) % p
        c = nc
    return c


def poly_degree(c):
    d = len(c) - 1
    while d > 0 and c[d] % 1 == 0 and c[d] == 0:
        d -= 1
    return d


def eval_poly(c, x, p):
    acc = 0
    for coeff in reversed(c):
        acc = (acc * x + coeff) % p
    return acc


def main() -> None:
    p = 41
    n = 20
    S_AC = [2, 25, 37, 23, 39, 1]
    S_BC = [8, 18, 16, 10, 5, 36]
    S_AB = [4, 21, 33, 40, 31, 9]
    pts, w = mu_domain(n, p)
    assert pts is not None
    mu = set(pts)
    print("mu_20 in F_41:", sorted(pts))
    print("all supports in mu_20:", set(S_AC + S_BC + S_AB) <= mu)
    print("pairwise disjoint:", not (set(S_AC) & set(S_BC) or set(S_AC) & set(S_AB) or set(S_BC) & set(S_AB)))
    leftover = mu - set(S_AC) - set(S_BC) - set(S_AB)
    print("leftover T (size should be 2):", leftover, "card", len(leftover))

    omegas, rows = remaining_rows(pts, S_AC, S_BC, p)
    idx = [omegas.index(x) for x in S_AB]
    block = [rows[i] for i in idx]
    print("6x4 rank:", gf_rank(block, p))
    vec = kernel_one(block, p)
    print("kernel (u0,u1,v0,v1):", vec)
    assert vec is not None
    u0, u1, v0, v1 = vec
    sAC = [u0, u1]  # u0 + u1 X
    sBC = [v0, v1]
    print("s_AC degree", 0 if u1 == 0 else 1, "s_BC degree", 0 if v1 == 0 else 1)
    assert u1 or v1, "would be a constant pair"

    WAC = poly_from_roots(S_AC, p)
    WBC = poly_from_roots(S_BC, p)
    WAB = poly_from_roots(S_AB, p)
    P = poly_add(poly_mul(sAC, WAC, p), poly_mul(sBC, WBC, p), p)
    print("deg W_AC,W_BC,W_AB,P =", poly_degree(WAC), poly_degree(WBC), poly_degree(WAB), poly_degree(P))
    # P should vanish on S_AB
    zeros = [eval_poly(P, r, p) for r in S_AB]
    print("P on S_AB (want zeros):", zeros)
    # polynomial division P / W_AB should be exact of degree <= 1
    # evaluate P / W_AB at a point outside S_AB to get a sense; do synthetic via roots
    # Since W_AB is monic of deg 6 and P vanishes on its 6 roots, W_AB | P.
    assert all(z == 0 for z in zeros)
    # product degrees
    # s_AB is P / W_AB, degree deg P - 6
    sAB_deg = poly_degree(P) - 6
    print("implied s_AB degree", sAB_deg)
    print("slot products: AC", 6 + (0 if u1 == 0 else 1), "BC", 6 + (0 if v1 == 0 else 1), "AB", 6 + sAB_deg)
    print("max product-degree", max(6 + (0 if u1 == 0 else 1), 6 + (0 if v1 == 0 else 1), 6 + sAB_deg))
    # check a leftover T point is not a root of P (so S_AB is exactly the mu_20 roots of P among remaining)
    print("P on leftover T:", {t: eval_poly(P, t, p) for t in leftover})
    print("P on S_AC (should be s_AC(r)*0 + s_BC(r)*W_BC(r)):", [eval_poly(P, r, p) for r in S_AC])


if __name__ == "__main__":
    main()
