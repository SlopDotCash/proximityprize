#!/usr/bin/env python3
"""Third-pencil harvest cap via the ratio-collision / dimension-count mechanism.

Follow-up to probe_rate_quarter_p1_stall_band_census.py (issue #466, P1 rate-quarter
StallResidual).  The census showed extremal stall families are TWO-pencil covers at
capacity 2(N-T+1); three-pencil composites always harvested fewer.  This probe finds
and measures the mechanism, exactly.

Setup.  For pencils j with aligned sets A_j on a common stack (u0,u1), the pencil
differences d_ij = pencil_i - pencil_j are pairs of codewords (deg < k) that vanish
(BOTH rows) on A_i \\cap A_j, and they telescope: d_12 + d_23 = d_13.  Coverage of
[0,N) by three (T-1)-aligned regions forces sum of pairwise overlaps
  Sigma >= 3(T-1) - N,
while each overlap is <= k-1 (MDS).  The free parameters of (d_12, d_23) live in
V_12 x V_23 (codewords vanishing on the respective overlaps) subject to
(d_12 + d_23)|_{ov_13} = 0 — a linear system whose solution space has dimension
  >= 2k - Sigma   (and generically exactly max(0, 2k - Sigma)).
At the P1 ratios 3(T-1) - N > 2k (prize: 704643071 > 536870912), so fully-aligned
triples should be linearly IMPOSSIBLE except for degenerate geometries.  Sections:

  A. Exact solution-space dimension for the three-pencil row system, swept over
     alignment shortfall t (|A_j| = T-1-t), geometry (contiguous / spread / random),
     and overlap split — locate the feasibility threshold t*.
  B. Two FULL pencils + third: given a genuine two-pencil configuration (the dual
     construction), sweep the third pencil's aligned size |A_3| and solve the exact
     affine system (d_13 vanishing on ov_13, d_13 = d_12 on ov_23) — find the max
     feasible |A_3|, hence the FORCED margin D = T - |A_3| and the marginal harvest
     cap (N - |A_3|)/(T - |A_3|).
  C. Ledger: 2(N-T+1) + marginal third harvest vs N, per scale and at prize ratios
     (arithmetic, exact).

All exact (integer linear algebra mod q); all randomness seeded.
"""

import numpy as np

T_NUM = 592794966
T_DEN = 2 ** 30


def shape(N):
    T = -(-N * T_NUM // T_DEN)
    k = N // 4
    return T, k


def rref_rank(M, q):
    """Exact rank of integer matrix M over F_q (Gaussian elimination)."""
    M = [[int(x) % q for x in row] for row in M]
    rows, cols = len(M), len(M[0]) if M else 0
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i][c] % q != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], q - 2, q)
        M[r] = [(x * inv) % q for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c] % q != 0:
                f = M[i][c]
                M[i] = [(M[i][j] - f * M[r][j]) % q for j in range(cols)]
        r += 1
        if r == rows:
            break
    return r


def vanishing_basis(pts, k, q, N):
    """Basis (as eval-vectors on [0,N)) of {deg<k polys vanishing on pts}.
    dim = k - |pts| (pts distinct, |pts| <= k)."""
    z = np.ones(N, dtype=object)
    for p in pts:
        z = np.array([(int(z[i]) * (i - p)) % q for i in range(N)], dtype=object)
    m = k - len(pts)
    basis = []
    for d in range(m):
        vec = [(int(z[i]) * pow(i, d, q)) % q for i in range(N)]
        basis.append(vec)
    return basis  # list of length-N eval vectors


def solution_dim_three_full(N, q, k, ov12, ov23, ov13):
    """dim{(r,s) in V_12 x V_23 : (r+s)|_{ov13} = 0} (one row of the system)."""
    B12 = vanishing_basis(ov12, k, q, N)
    B23 = vanishing_basis(ov23, k, q, N)
    nv = len(B12) + len(B23)
    if nv == 0:
        return 0, nv
    rows = []
    for p in ov13:
        row = [B12[j][p] for j in range(len(B12))] + \
              [B23[j][p] for j in range(len(B23))]
        rows.append(row)
    rank = rref_rank(rows, q) if rows else 0
    return nv - rank, nv


print("=" * 78)
print("A. Three fully/nearly-aligned pencils: exact solution-space dimension")
print("   (|A_j| = T-1-t; nontrivial dim required for three DISTINCT pencils)")
print("=" * 78)
for N, q in ((128, 521), (256, 1031)):
    T, k = shape(N)
    print(f"\n  N={N} q={q} T={T} k={k}: coverage floor Sigma_min(t) = 3(T-1-t)-N;"
          f" 2k = {2 * k}")
    thr = (3 * (T - 1) - N - (2 * k - 1) + 2) // 3
    print(f"  predicted feasibility threshold (generic): t* ~ ceil((3(T-1)-N-(2k-1))/3)"
          f" = {-(-(3 * (T - 1) - N - (2 * k - 1)) // 3)}")
    rng = np.random.default_rng(2026)
    for t in (0, 5, 10, 12, 13, 14, 15, 20):
        a = T - 1 - t
        Sigma = 3 * a - N
        if Sigma < 0:
            print(f"    t={t:2d}: regions can be disjoint (Sigma floor < 0) — trivially feasible")
            continue
        s1 = min(k - 1, Sigma)
        s2 = min(k - 1, Sigma - s1)
        s3 = Sigma - s1 - s2
        splits = {"balanced": (Sigma // 3 + (Sigma % 3 > 0), Sigma // 3 + (Sigma % 3 > 1),
                               Sigma // 3),
                  "skewed": (s1, s2, s3)}
        line = f"    t={t:2d} (|A|={a}, Sigma_min={Sigma}):"
        for name, (o12, o23, o13) in splits.items():
            if max(o12, o23, o13) > k - 1 or min(o12, o23, o13) < 0:
                line += f" {name}: overlap>k-1 infeasible;"
                continue
            dims = []
            for trial, style in enumerate(("contig", "random")):
                if style == "contig":
                    ov12 = list(range(0, o12))
                    ov23 = list(range(o12, o12 + o23))
                    ov13 = list(range(o12 + o23, o12 + o23 + o13))
                else:
                    pts = rng.choice(N, size=o12 + o23 + o13, replace=False)
                    ov12 = list(map(int, pts[:o12]))
                    ov23 = list(map(int, pts[o12:o12 + o23]))
                    ov13 = list(map(int, pts[o12 + o23:]))
                dim, nv = solution_dim_three_full(N, q, k, ov12, ov23, ov13)
                dims.append(dim)
            line += f" {name}: dim={dims} (lower bd {max(0, 2 * k - Sigma)});"
        print(line)

print("\n" + "=" * 78)
print("B. Two FULL pencils + a third: max feasible |A_3| (exact affine system)")
print("=" * 78)
# Two full pencils: A1 = [0, T-1), A2 = [N-(T-1), N), ov12 = [N-T+1, T-1).
# d_12 = (x*d, d), d = z12 * c as in the census dual construction.
# Third pencil: choose ov13 c A1\ov12, ov23 c A2\ov12 (sizes f1, f2), plus
# possibly coords of ov12 (there d_12 = 0 so d_13 = d_23 must vanish there too:
# those coords act on BOTH constraint sets).  System for one row r = d_13
# (deg<k eval vector, k unknown coeffs):
#   r(p) = 0        for p in ov13
#   r(p) = d12(p)   for p in ov23
# Solvable iff rank([V|rhs]) == rank(V).  |A_3| = f1 + f2 (+ ov12 coords used).
for N, q in ((128, 521), (256, 1031)):
    T, k = shape(N)
    ov_lo, ov_hi = N - (T - 1), T - 1
    ov12 = list(range(ov_lo, ov_hi))
    A1priv = list(range(0, ov_lo))              # A1 \ ov12, size N-T+1
    A2priv = list(range(ov_hi, N))              # A2 \ ov12, size N-T+1
    # build d (row of d_12): z12 * c with no roots off ov12
    dvec = None
    for seed in range(50):
        rng = np.random.default_rng(555 + seed)
        deg_c = k - 2 - len(ov12)
        if deg_c < 0:
            break
        c = [int(x) for x in rng.integers(0, q, deg_c + 1)]
        c[-1] = max(1, c[-1])
        vec = []
        ok = True
        for i in range(N):
            zv = 1
            for r0 in ov12:
                zv = (zv * (i - r0)) % q
            cv = 0
            for coef in reversed(c):
                cv = (cv * i + coef) % q
            vec.append((zv * cv) % q)
            if i not in ov12 and vec[-1] == 0:
                ok = False
                break
        if ok:
            dvec = vec
            break
    assert dvec is not None
    V = [[pow(i, j, q) for j in range(k)] for i in range(N)]  # monomial evals
    print(f"\n  N={N} q={q} T={T} k={k}: |ov12|={len(ov12)}, private sizes"
          f" {len(A1priv)}/{len(A2priv)}")
    best = None
    for f1 in range(0, min(len(A1priv), k) + 1, max(1, k // 16)):
        for f2 in range(0, min(len(A2priv), k) + 1, max(1, k // 16)):
            ov13 = A1priv[:f1]
            ov23 = A2priv[:f2]
            rows = [[V[p][j] for j in range(k)] for p in ov13 + ov23]
            rhs = [0] * len(ov13) + [dvec[p] for p in ov23]
            if not rows:
                feas = True
            else:
                rk = rref_rank(rows, q)
                rk_aug = rref_rank([r + [b] for r, b in zip(rows, rhs)], q)
                feas = (rk == rk_aug)
            if feas:
                A3 = f1 + f2
                if best is None or A3 > best[0]:
                    best = (A3, f1, f2)
    A3, f1, f2 = best
    D = T - A3
    harv = (N - A3) // D if D > 0 else None
    print(f"    max feasible |A_3| (grid) = {A3} (f1={f1}, f2={f2})"
          f" -> forced margin D = T - |A_3| = {D}")
    print(f"    marginal third-pencil harvest cap (N-|A_3|)/D = {harv}")
    print(f"    ledger: 2(N-T+1) + {harv} = {2 * (N - T + 1) + harv} vs N = {N}"
          f"  (slack used: {harv} of {2 * T - N - 2})")

print("\n" + "=" * 78)
print("C. Prize-scale ledger (exact arithmetic)")
print("=" * 78)
N, T, k = 2 ** 30, 592794966, 2 ** 28
print(f"  3(T-1) - N = {3 * (T - 1) - N}  vs  2k = {2 * k}  "
      f"(> 2k: fully-aligned triples generically infeasible)")
print(f"  affine-system feasibility for third pencil needs |ov13|+|ov23| <= k"
      f" (generic): |A_3| <= k + (N - 2(T-1) + |ov12|) <= k + (N-2T+2) + (k-1)"
      f" = {k + (N - 2 * T + 2) + (k - 1)}")
A3max = k + (N - 2 * T + 2) + (k - 1)
D = T - A3max
print(f"  -> generic forced margin D >= T - {A3max} = {D}"
      f"; marginal harvest <= (N - A3)/D = {(N - A3max) // D}")
print(f"  Lean-formalized margin ledger (UNCONDITIONAL, margin hypothesis D >= 5):")
for D, mlab in ((5, "three-pencil, margin 5"), (9, "four-pencil, margins 9")):
    h = (N - T + D) // D
    print(f"    D={D}: per-extra-pencil harvest <= (N-T+D)/D = {h}")
print(f"    2*(N-T+1) + (N-T+5)//5 = {2 * (N - T + 1) + (N - T + 5) // 5}"
      f" <= N = {N}: {2 * (N - T + 1) + (N - T + 5) // 5 <= N}")
print(f"    2*(N-T+1) + 2*((N-T+9)//9) = {2 * (N - T + 1) + 2 * ((N - T + 9) // 9)}"
      f" <= N: {2 * (N - T + 1) + 2 * ((N - T + 9) // 9) <= N}")
print(f"    margin-4 FAILS: 2*(N-T+1) + (N-T+4)//4 = "
      f"{2 * (N - T + 1) + (N - T + 4) // 4} > N: "
      f"{2 * (N - T + 1) + (N - T + 4) // 4 > N}")
