#!/usr/bin/env python3
"""G286 probe: is 0 in the convex hull of the realizable sponsor centered-profile cone? (#466)

Frontier context.  G280 proved the CORE covariance B(W,R) is a real signed inner product and that
the sponsor centered-profile cone is ANTIPODE-FREE (does not contain -R).  G284 then proved the
pure implication `antipode-free => strictly separable` is FALSE via an abstract countermodel whose
barycenter is 0, and explicitly LEFT OPEN the arithmetic question: does the ACTUAL sponsor cone put
0 in its convex hull?  The surviving admissible #466 certificate (G56/formalizer handoffs) is one
predeclared row-labelled odd arithmetic normal `phi` with an independently PROVED positive margin
over the whole realizable sponsor cone.  By Gordan / separating-hyperplane duality over Q:

    a strictly separating phi EXISTS  <=>  0 is NOT in the convex hull of the realizable centered
    sponsor profiles.

So this probe DECIDES whether the surviving linear-certificate route is even alive per cell, and
when it is, EXHIBITS an exact rational separator (a concrete construction target).

Generating set = realizable centered sponsor profiles  c^{(r,a)} = (p*R_r(x) - SR)_x,
r = 1..n, a in G (multiplicative dilations; a=-1 in G is the coordinate antipode for 2-power n).
Exactly G280's realizable family, conventions match G280/G269 (double-shift, R_r = dp_r * dp_{r-1}).
Pure exact rational (Fraction), no floats.

Exact decision pipeline per cell (deduplicated realizable set V, dim = p):
  1. AFFINE-HULL test (informational).  Solve  V^T lambda = 0, sum lambda = 1  (exact rref).
     If INCONSISTENT, 0 is not even in the affine hull, so 0 is strictly OUT of conv(V).
  2. CONVEX-HULL test.  Exact Phase-I simplex (Bland's rule) for
        V^T lambda = 0, sum lambda = 1, lambda >= 0.
     Feasible => 0 in conv(V) (route DEAD at that cell, G284 barycenter realized arithmetically);
     the convex combination is re-verified exactly.  Infeasible (Phase-I optimum with positive
     artificial objective) => 0 out of conv(V).  Hitting the iteration cap => UNKNOWN, never
     "infeasible".
  3. SEPARATOR certificate.  When 0 is out of conv(V), solve the exact LP  K mu >= 1  (K = Gram
     matrix of V) and set w = V^T mu, phi(v) = <w, v>.  By Gordan this LP is feasible iff
     0 notin conv(V), so the separator is an independent certificate of step 2.

Correction (audit L104, 2026-10-28): an earlier version claimed that when 0 is in aff(V) but not
in conv(V) there is NO nontrivial linear separator.  That is false: a finite convex hull missing 0
is always strictly linearly separated from 0 (e.g. V = {1, 2} in Q: 0 = 2*1 - 1*2 is affine, yet
w = 1 has margins 1, 2 > 0 = w(0)).  The min-norm point of aff(V) can be 0 while the min-norm point
of conv(V) is not; the old code substituted the former for the latter and then "repaired" the
nonpositive margins by adding a constant, which takes the same value at 0 and separates nothing.

Every separator is re-verified exactly: w != 0 and min_v phi(v) > phi(0) = 0.
SystemExit(1) on any internal inconsistency or failed gate.
"""
from __future__ import annotations
from fractions import Fraction as F
import sys

sys.path.insert(0, 'scripts/probes')
from g280_sponsor_cone_antipode_probe import (  # noqa: E402
    subgroup, R_profile, centered, dilate,
)


def realizable_profiles(p: int, n: int):
    G = subgroup(p, n)
    assert (p - 1) in G, "need -1 in G (2-power thinness)"
    seen = set()
    V, L = [], []
    for r in range(1, n + 1):
        R = R_profile(G, r, p)
        c0 = centered(R, p)
        if not any(c0):
            continue
        for a in G:
            c = tuple(dilate(c0, a, p))
            if c not in seen:
                seen.add(c)
                V.append([F(x) for x in c])
                L.append((r, a))
    return V, L, G


def rref_augmented(A):
    """In-place rational rref of augmented matrix A (list of lists, last col = rhs).
    Returns (pivot_cols, num_data_cols)."""
    R = len(A)
    C = len(A[0]) - 1
    piv = []
    pr = 0
    for c in range(C):
        sel = None
        for r in range(pr, R):
            if A[r][c] != 0:
                sel = r
                break
        if sel is None:
            continue
        A[pr], A[sel] = A[sel], A[pr]
        pv = A[pr][c]
        A[pr] = [v / pv for v in A[pr]]
        for r in range(R):
            if r != pr and A[r][c] != 0:
                f = A[r][c]
                A[r] = [A[r][k] - f * A[pr][k] for k in range(C + 1)]
        piv.append(c)
        pr += 1
        if pr == R:
            break
    return piv, C


def affine_separator(V):
    """If 0 not in affine hull of V, return an exact affine functional (w, b) with
    w . v + b == 0 for all v in V but the constant -b != 0 encodes 0 not being an affine
    combination.  Concretely: 0 in affine hull  <=>  system [V^T; 1..1] lambda = [0;1] is
    consistent.  If inconsistent, an inconsistent row gives a Farkas vector y in R^{dim+1}
    with y.(V-column augmented) = 0 for structural part but y.[0;1] != 0, i.e. an affine
    functional constant on V with value != value-at-0.  Returns (consistent, funcs)."""
    m = len(V)
    dim = len(V[0])
    # rows: dim coordinate rows + 1 all-ones row; cols: m lambdas; rhs.
    rows = [[V[i][x] for i in range(m)] for x in range(dim)]
    rows.append([F(1)] * m)
    rhs = [F(0)] * dim + [F(1)]
    A = [rows[k] + [rhs[k]] for k in range(len(rows))]
    piv, C = rref_augmented(A)
    R = len(A)
    pr = len(piv)
    for r in range(pr, R):
        if all(A[r][k] == 0 for k in range(C)) and A[r][C] != 0:
            return False  # inconsistent -> 0 NOT in affine hull -> strictly OUT
    return True  # 0 in affine hull; convexity undecided here


MAX_SIMPLEX_ITER = 50000


def phase1(A, b, max_iter=MAX_SIMPLEX_ITER):
    """Exact Phase-I simplex (Bland's rule) for  A x = b, x >= 0  over Q.

    Returns ("feasible", x), ("infeasible", None) or ("unknown", None).  "infeasible" is reported
    only at a Phase-I optimum (no improving column) with positive artificial objective, which is
    an LP optimality certificate; hitting `max_iter` returns "unknown"."""
    rows = len(A)
    m = len(A[0])
    A = [row[:] for row in A]
    b = list(b)
    for x in range(rows):
        if b[x] < 0:
            b[x] = -b[x]
            A[x] = [-v for v in A[x]]
    ncol = m + rows
    T = [A[x][:] + [F(1) if j == x else F(0) for j in range(rows)] + [b[x]] for x in range(rows)]
    cost = [F(0)] * m + [F(1)] * rows + [F(0)]
    basis = [m + x for x in range(rows)]

    def reduced_costs():
        rc = [F(0)] * (ncol + 1)
        for j in range(ncol + 1):
            s = F(0)
            for x in range(rows):
                s += cost[basis[x]] * T[x][j]
            rc[j] = s - cost[j]
        return rc

    for _ in range(max_iter):
        rc = reduced_costs()
        enter = -1
        for j in range(ncol):
            if rc[j] > 0:
                enter = j
                break
        if enter == -1:
            break
        leave = -1
        best = None
        for x in range(rows):
            a = T[x][enter]
            if a > 0:
                ratio = T[x][ncol] / a
                if best is None or ratio < best or (ratio == best and basis[x] < basis[leave]):
                    best = ratio
                    leave = x
        if leave == -1:
            # Phase-I objective is bounded below by 0, so this cannot happen for valid input.
            return "unknown", None
        piv = T[leave][enter]
        T[leave] = [v / piv for v in T[leave]]
        for x in range(rows):
            if x != leave and T[x][enter] != 0:
                f = T[x][enter]
                T[x] = [T[x][k] - f * T[leave][k] for k in range(ncol + 1)]
        basis[leave] = enter
    else:
        return "unknown", None  # iteration cap hit: no optimality certificate

    obj = F(0)
    for x in range(rows):
        obj += cost[basis[x]] * T[x][ncol]
    if obj == 0:
        sol = [F(0)] * m
        for x in range(rows):
            if basis[x] < m:
                sol[basis[x]] = T[x][ncol]
        return "feasible", sol
    return "infeasible", None


def zero_in_convex_hull(V, max_iter=MAX_SIMPLEX_ITER):
    """Exact Phase-I simplex: feasibility of V^T lambda = 0, sum lambda = 1, lambda >= 0.

    Returns (True, lam) when 0 is in conv(V), (False, None) when the Phase-I optimum proves it is
    not, and (None, "unknown") when the iteration cap is hit."""
    m = len(V)
    dim = len(V[0])
    A = [[V[i][x] for i in range(m)] for x in range(dim)]
    A.append([F(1)] * m)
    b = [F(0)] * dim + [F(1)]
    status, sol = phase1(A, b, max_iter)
    if status == "feasible":
        return True, sol
    if status == "infeasible":
        return False, None
    return None, "unknown"


def strict_linear_separator(V, max_iter=MAX_SIMPLEX_ITER):
    """Exact strict LINEAR separator of conv(V) from 0, as a dual certificate.

    Solves  K mu >= 1  (K[i][j] = <V_i, V_j>) by exact Phase-I and returns (w, margin) with
    w = sum_i mu_i V_i, after verifying w != 0 and min_v <w, v> = margin >= 1 > 0 = <w, 0>.
    By Gordan's theorem the LP is feasible iff 0 notin conv(V) (a separator may be projected into
    span(V) without changing its values on V).  Returns None when the LP is infeasible (0 in
    conv(V)) and "unknown" when the iteration cap is hit."""
    m = len(V)
    dim = len(V[0])
    K = [[sum(V[i][x] * V[j][x] for x in range(dim)) for j in range(m)] for i in range(m)]
    # variables: mu_plus (m), mu_minus (m), surplus s (m);  K mu+ - K mu- - s = 1.
    A = [K[i][:] + [-v for v in K[i]] + [F(-1) if j == i else F(0) for j in range(m)]
         for i in range(m)]
    status, sol = phase1(A, [F(1)] * m, max_iter)
    if status == "unknown":
        return "unknown"
    if status == "infeasible":
        return None
    mu = [sol[i] - sol[m + i] for i in range(m)]
    w = [sum(mu[i] * V[i][x] for i in range(m)) for x in range(dim)]
    margins = [sum(w[x] * v[x] for x in range(dim)) for v in V]
    if not any(w) or min(margins) <= 0:
        raise AssertionError("separator LP returned an invalid certificate")
    return w, min(margins)


def build_and_verify_separator(V, max_iter=MAX_SIMPLEX_ITER):
    """Return ((w, margin), None) with an exact verified strict linear separator, or
    (None, lam) if 0 is in conv(V), or (None, "unknown") if the simplex cap was hit."""
    feasible, cert = zero_in_convex_hull(V, max_iter)
    if feasible:
        return None, cert  # 0 in hull
    if feasible is None:
        return None, "unknown"
    sep = strict_linear_separator(V, max_iter)
    if sep is None:
        raise AssertionError("Phase-I says 0 notin conv(V) but the separator LP is infeasible")
    if sep == "unknown":
        return None, "unknown"
    return sep, None


def exact_max_margin_separator(V):
    """Affine-hull separator, valid ONLY when 0 is not in aff(V).

    Uses the exact orthogonal projection p* of 0 onto aff(V); when 0 notin aff(V), p* != 0 is
    orthogonal to the affine directions, so <p*, v> = ||p*||^2 > 0 = <p*, 0> for every v in V.
    When 0 IS in aff(V) the projection is 0 and this returns None: that says nothing about
    conv(V), for which `strict_linear_separator` is the correct test.  (Despite the historical
    name, no max-margin optimisation is performed.)"""
    dim = len(V[0])
    v0 = V[0]
    # affine hull directions
    D = [[V[i][x] - v0[x] for x in range(dim)] for i in range(1, len(V))]
    # Solve for projection p* = v0 + D^T alpha minimizing ||v0 + D^T alpha||^2  =>
    # normal equations (D D^T) alpha = -D v0.
    k = len(D)
    if k == 0:
        # single point v0 != 0: w = v0 has margin ||v0||^2 > 0 (checked below)
        return normalize_and_check(v0[:], F(0), V)
    G = [[sum(D[i][x] * D[j][x] for x in range(dim)) for j in range(k)] for i in range(k)]
    rhs = [-sum(D[i][x] * v0[x] for x in range(dim)) for i in range(k)]
    Aug = [G[i][:] + [rhs[i]] for i in range(k)]
    piv, _ = rref_augmented(Aug)
    alpha = [F(0)] * k
    for i, c in enumerate(piv):
        alpha[c] = Aug[i][k]
    pstar = [v0[x] + sum(D[i][x] * alpha[i] for i in range(k)) for x in range(dim)]
    # separator normal w = pstar (direction from 0 to closest affine point).
    w = pstar
    return normalize_and_check(w, F(0), V)


def normalize_and_check(w, c0, V):
    """Check that phi(v) = <w, v> + c0 strictly separates V from 0: w != 0 and
    min_v phi(v) > phi(0) = c0.  Returns (w, c0, min_v phi(v) - phi(0)) or None.

    No constant shift is applied: a constant takes the same value at 0 and on V, so it can never
    create separation (the pre-L104 version added one and reported w = 0, c = 1 as a separator)."""
    dim = len(V[0])
    if not any(w):
        return None
    margins = [sum(w[x] * v[x] for x in range(dim)) for v in V]  # phi(v) - phi(0)
    mnm = min(margins)
    if mnm <= 0:
        return None
    return (w, c0, mnm)


def main():
    cells = [(8, 113), (8, 257), (16, 97), (16, 113), (16, 257), (16, 433), (16, 977), (16, 1153)]
    print("G286 : is 0 in the convex hull of the realizable sponsor centered-profile cone?")
    print("=" * 80)
    in_hull_cells, sep_cells, unknown_cells = [], [], []
    separators = {}
    for (n, p) in cells:
        V, L, G = realizable_profiles(p, n)
        aff = affine_separator(V)
        if not aff:
            # 0 not in affine hull => strictly separated by the affine projection.
            sep = exact_max_margin_separator(V)
            if sep is None:
                print(f"INTERNAL: affine-out but no separator n={n} p={p}"); raise SystemExit(1)
            w, c, mnm = sep
            print(f"n={n:3d} p={p:5d}: 0 NOT in AFFINE hull -> strictly OUT (|V|={len(V):2d}); "
                  f"linear separator margin={mnm} > 0 = phi(0)")
            sep_cells.append((n, p, "AFFINE_OUT", mnm))
            separators[(n, p)] = w
            continue
        feasible, cert = zero_in_convex_hull(V)
        if feasible is None:
            print(f"n={n:3d} p={p:5d}: UNKNOWN (simplex iteration cap hit; no certificate)")
            unknown_cells.append((n, p))
            continue
        if feasible:
            dim = len(V[0])
            acc = [F(0)] * dim
            ssum = F(0)
            for i, lam in enumerate(cert):
                if lam < 0:
                    print("INTERNAL neg lambda"); raise SystemExit(1)
                ssum += lam
                if lam:
                    for x in range(dim):
                        acc[x] += lam * V[i][x]
            if ssum != 1 or any(a != 0 for a in acc):
                print(f"INTERNAL bad convex cert n={n} p={p}"); raise SystemExit(1)
            sup = [L[i] for i, lam in enumerate(cert) if lam != 0]
            print(f"n={n:3d} p={p:5d}: 0 IN CONVEX HULL (|V|={len(V):2d}); convex support "
                  f"size={len(sup)} labels={sup}")
            in_hull_cells.append((n, p, sup))
        else:
            # 0 is in the AFFINE hull but out of the CONVEX hull.  A finite convex hull missing 0
            # is always strictly LINEARLY separated from 0 (Gordan); the affine projection is 0
            # here, so solve the exact separator LP instead and verify the strict gap.
            res, why = build_and_verify_separator(V)
            if res is None:
                if why == "unknown":
                    print(f"n={n:3d} p={p:5d}: UNKNOWN (separator LP iteration cap hit)")
                    unknown_cells.append((n, p))
                    continue
                print(f"INTERNAL: convex-out but separator says in hull n={n} p={p}")
                raise SystemExit(1)
            w, mnm = res
            print(f"n={n:3d} p={p:5d}: 0 in AFFINE hull but OUT of CONVEX hull (|V|={len(V):2d}); "
                  f"exact nonzero linear separator, min margin={mnm} > 0 = phi(0)")
            sep_cells.append((n, p, "CONVEX_OUT", mnm))
            separators[(n, p)] = w
    print("=" * 80)
    if in_hull_cells:
        print("VERDICT: 0 lies in the CONVEX HULL for at least one sponsor cell:")
        for (n, p, sup) in in_hull_cells:
            print(f"   n={n} p={p}  convex-combination support {sup}")
        print("=> At those cells NO row-labelled odd linear normal strictly separates the whole")
        print("   realizable sponsor cone from 0.  The predeclared-odd-normal certificate route")
        print("   (G56/formalizer surviving hatch) is DEAD there: G284's barycenter mechanism is")
        print("   realized by the ACTUAL sponsor arithmetic, not merely an abstract countermodel.")
        print("   At those finite cells a certificate cannot be a linear normal on these")
        print("   profiles; nothing here classifies the possible non-linear certificates.")
    elif unknown_cells:
        print("VERDICT: no tested cell has 0 in the convex hull, but some cells are UNKNOWN")
        print(f"   (iteration cap): {unknown_cells}.  No all-cell conclusion is drawn.")
    else:
        print("VERDICT: 0 is OUTSIDE the CONVEX hull for EVERY tested cell (no barycenter), and")
        print("   every tested cell has an EXACT, verified, nonzero LINEAR separator w with")
        print("   min_v <w,v> > 0 = <w,0> (including cells where 0 lies in the affine hull).")
        print("   These separators lie in span(V), hence are coordinate-EVEN.  Separately, the")
        print("   realizable cone is coordinate-EVEN, so every coordinate-ODD linear normal")
        print("   annihilates it (gate B) and carries no margin at these cells.  This rules out")
        print("   coordinate-odd LINEAR normals on the tested finite cells only; it does not show")
        print("   that a surviving certificate must be non-linear, and whether the certificate's")
        print("   'odd' requirement means coordinate reflection or global polarity is a separate")
        print("   question outside this probe (see audit crosslink R-253).")
    print("summary sep_cells:", [(n, p, t) for (n, p, t, *_) in sep_cells])
    print("summary in_hull:", [(n, p) for (n, p, _) in in_hull_cells])
    print("summary unknown:", unknown_cells)

    # ---- Hard gates (SystemExit(1) on any failure) ----
    # GATE A: every realizable centered profile is coordinate-even (G280 Fact 1, thinness).
    # GATE B: any coordinate-ODD functional annihilates the whole cone (margin 0).
    # GATE C: an EVEN functional gives a nonzero pairing (separation lives in the even part).
    # GATE E: every recorded separator is nonzero, coordinate-even and strictly positive on V.
    for (n, p) in cells:
        V, L, G = realizable_profiles(p, n)
        for v in V:
            if not all(v[x] == v[(-x) % p] for x in range(p)):
                print(f"GATE A FAIL: profile not coord-even n={n} p={p}")
                raise SystemExit(1)
        # odd functional supported on {1,-1}: w[1]=1, w[-1]=-1
        w = [F(0)] * p
        w[1] = F(1); w[(-1) % p] = F(-1)
        for v in V:
            if sum(w[x] * v[x] for x in range(p)) != 0:
                print(f"GATE B FAIL: odd functional not annihilating n={n} p={p}")
                raise SystemExit(1)
        # even functional supported on {1,-1}: u[1]=1, u[-1]=1 ; must be nonzero on some profile
        u = [F(0)] * p
        u[1] = F(1); u[(-1) % p] = F(1)
        if all(sum(u[x] * v[x] for x in range(p)) == 0 for v in V):
            # some cells may have c[1] = 0: fall back to the full even pairing check, using
            # each (coordinate-even, by gate A) profile v itself as the even functional.
            if not any(sum(vx * vx for vx in v) != 0 for v in V):
                print(f"GATE C FAIL: no even functional pairs nonzero n={n} p={p}")
                raise SystemExit(1)
        w = separators.get((n, p))
        if w is not None:
            if (not any(w) or not all(w[x] == w[(-x) % p] for x in range(p))
                    or min(sum(w[x] * v[x] for x in range(p)) for v in V) <= 0):
                print(f"GATE E FAIL: invalid or non-even separator n={n} p={p}")
                raise SystemExit(1)
    # GATE D: zero must be OUT of the convex hull for every cell (no barycenter), with a
    # recorded certificate (unknown cells fail the gate).
    if in_hull_cells or unknown_cells or len(separators) != len(cells):
        print("GATE D FAIL: zero in convex hull, or no separator certificate, at some cell")
        raise SystemExit(1)
    print("GATES A-E PASS: even cone, odd-annihilation, even-nonzero pairing, zero out of hull,")
    print("  verified nonzero even linear separators.")


if __name__ == "__main__":
    main()
