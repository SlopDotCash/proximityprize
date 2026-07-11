#!/usr/bin/env python3
"""Exact clique-to-pencil structure census for the P1 rate-quarter overlap graph.

Thread rq:turan-extraction (#466).  The agreement-overlap graph at the P1
rate-quarter predecessor (N = 2^30, K = 2^28, T = 592794966) has independence
number at most five, so Ramsey extraction yields large cliques (pairwise
agreement overlap >= K) inside any over-budget family.  The consolidation
question is what a clique FORCES geometrically:

  Q1. Does a 3-clique force its three explanations onto one polynomial source
      pencil?  (Expected NO: triangle-of-pencils construction.)
  Q2. Does a 4-clique force at least one collinear triple?  (Expected NO:
      near-pencil sunflower with common core of size k-1.)
  Q3. For m >= 5, are general-position m-cliques (no 3 collinear) realizable?
      Exact rank census of the concurrency linear systems over F_p.  The
      solution space always contains the 2k-dimensional single-pencil locus;
      general position is possible iff the space is strictly larger AND a
      sampled point avoids all collinearity loci.
  Q4. Single-line clique capacity: a line at threshold t carries at most
      n - t + 1 points (fresh-fibre packing), realized exactly.

Toy scale mirrors the prize ratios: n = 32, k = 8 (rate 1/4), edge threshold
K = k = 8 = n/4, vertex threshold t = 18 (ceil of T/N * 32 = 17.67).  All
arithmetic is exact over F_p, p = 10007.  Exit 0 iff every verdict matches
the recorded expectation.
"""

from __future__ import annotations

import itertools
import random

P = 10007
N = 32
KDIM = 8          # RS dimension (rate 1/4)
KEDGE = 8         # overlap-graph edge threshold (= KDIM at the prize)
TVERT = 18        # vertex agreement threshold, ceil(592794966/2^30 * 32)
XS = list(range(1, N + 1))

random.seed(466)


# ----------------------------------------------------------------------------
# exact F_p polynomial helpers
# ----------------------------------------------------------------------------

def inv(a: int) -> int:
    return pow(a % P, P - 2, P)


def poly_eval(coeffs: list[int], x: int) -> int:
    acc = 0
    for c in reversed(coeffs):
        acc = (acc * x + c) % P
    return acc


def interpolate(points: list[tuple[int, int]]) -> list[int]:
    """Lagrange interpolation; returns coefficient list of length len(points)."""
    npts = len(points)
    coeffs = [0] * npts
    for i, (xi, yi) in enumerate(points):
        # numerator polynomial prod_{j != i} (X - xj)
        num = [1]
        denom = 1
        for j, (xj, _) in enumerate(points):
            if j == i:
                continue
            new = [0] * (len(num) + 1)
            for d, c in enumerate(num):
                new[d + 1] = (new[d + 1] + c) % P
                new[d] = (new[d] - c * xj) % P
            num = new
            denom = denom * (xi - xj) % P
        scale = yi * inv(denom) % P
        for d, c in enumerate(num):
            coeffs[d] = (coeffs[d] + c * scale) % P
    return coeffs


def poly_sub(a: list[int], b: list[int]) -> list[int]:
    n = max(len(a), len(b))
    return [((a[d] if d < len(a) else 0) - (b[d] if d < len(b) else 0)) % P
            for d in range(n)]


def poly_scale(a: list[int], s: int) -> list[int]:
    return [c * s % P for c in a]


def poly_is_zero(a: list[int]) -> bool:
    return all(c % P == 0 for c in a)


def slope_poly(ga: int, pa: list[int], gb: int, pb: list[int]) -> list[int]:
    return poly_scale(poly_sub(pa, pb), inv(ga - gb))


def secant(ga: int, pa: list[int], gb: int, pb: list[int]):
    r = slope_poly(ga, pa, gb, pb)
    a = poly_sub(pa, poly_scale(r, ga))
    return a, r


def full_agreement(u0: list[int], u1: list[int], gamma: int,
                   p: list[int]) -> set[int]:
    return {i for i, x in enumerate(XS)
            if poly_eval(p, x) == (u0[i] + gamma * u1[i]) % P}


def joint_core(u0: list[int], u1: list[int], a: list[int],
               r: list[int]) -> set[int]:
    return {i for i, x in enumerate(XS)
            if poly_eval(a, x) == u0[i] and poly_eval(r, x) == u1[i]}


def row_is_deg_lt_k(row: list[int], support: set[int]) -> bool:
    pts = sorted(support)
    if len(pts) <= KDIM:
        return True
    base = [(XS[i], row[i]) for i in pts[:KDIM]]
    q = interpolate(base)
    return all(poly_eval(q, XS[i]) == row[i] for i in pts)


def no_joint(u0: list[int], u1: list[int], support: set[int]) -> bool:
    """True iff the support is NOT jointly explained by two RS codewords."""
    return not (row_is_deg_lt_k(u0, support) and row_is_deg_lt_k(u1, support))


def collinear_triple(gammas: list[int], polys: list[list[int]],
                     i: int, j: int, l: int) -> bool:
    """Three lifted points are collinear iff the two slopes from i agree."""
    s_ij = slope_poly(gammas[i], polys[i], gammas[j], polys[j])
    s_il = slope_poly(gammas[i], polys[i], gammas[l], polys[l])
    return poly_is_zero(poly_sub(s_ij, s_il))


def verify_clique(tag: str, gammas: list[int], polys: list[list[int]],
                  u0: list[int], u1: list[int],
                  expect_no3collinear: bool) -> dict:
    m = len(gammas)
    agreements = [full_agreement(u0, u1, gammas[i], polys[i])
                  for i in range(m)]
    vertex_ok = all(len(A) >= TVERT for A in agreements)
    overlaps_ok = all(
        len(agreements[i] & agreements[j]) >= KEDGE
        for i, j in itertools.combinations(range(m), 2))
    core_identity_ok = True
    for i, j in itertools.combinations(range(m), 2):
        a, r = secant(gammas[i], polys[i], gammas[j], polys[j])
        if agreements[i] & agreements[j] != joint_core(u0, u1, a, r):
            core_identity_ok = False
    triples_collinear = [
        (i, j, l) for i, j, l in itertools.combinations(range(m), 3)
        if collinear_triple(gammas, polys, i, j, l)]
    no_joint_ok = all(no_joint(u0, u1, A) for A in agreements)
    distinct_ok = len({tuple(p) for p in polys}) == m and len(set(gammas)) == m
    result = {
        "tag": tag,
        "m": m,
        "vertex_threshold_ok": vertex_ok,
        "edge_overlaps_ok": overlaps_ok,
        "core_identity_ok": core_identity_ok,
        "collinear_triples": triples_collinear,
        "no3collinear": not triples_collinear,
        "no_joint_ok": no_joint_ok,
        "distinct_ok": distinct_ok,
    }
    result["is_valid_clique"] = (vertex_ok and overlaps_ok and no_joint_ok
                                 and distinct_ok)
    result["matches_expectation"] = (
        result["is_valid_clique"]
        and result["no3collinear"] == expect_no3collinear
        and core_identity_ok)
    return result


# ----------------------------------------------------------------------------
# Q1: triangle of three distinct pencils
# ----------------------------------------------------------------------------

def build_triangle() -> dict:
    g1, g2, g3 = 3, 5, 11
    # pencil L1 = (a1, b1); L2 meets L1 at scalar g3; L3 meets L1 at g2 and
    # L2 at g1 (triangle of lines in the pencil plane).
    a1 = [random.randrange(P) for _ in range(KDIM)]
    b1 = [random.randrange(P) for _ in range(KDIM)]
    d = [(b1[c] + random.randrange(1, P)) % P for c in range(KDIM)]
    c_ = poly_sub([(a1[i] + g3 * b1[i]) % P for i in range(KDIM)],
                  poly_scale(d, g3))
    # L3 = (e, f): e + g2 f = a1 + g2 b1 ; e + g1 f = c + g1 d
    rhs1 = [(a1[i] + g2 * b1[i]) % P for i in range(KDIM)]
    rhs2 = [(c_[i] + g1 * d[i]) % P for i in range(KDIM)]
    f = poly_scale(poly_sub(rhs1, rhs2), inv(g2 - g1))
    e = poly_sub(rhs1, poly_scale(f, g2))
    # blocks: u follows L1 on D1, L2 on D2, L3 on D3
    D1, D2, D3 = range(0, 11), range(11, 22), range(22, 32)
    u0, u1 = [0] * N, [0] * N
    for i in D1:
        u0[i], u1[i] = poly_eval(a1, XS[i]), poly_eval(b1, XS[i])
    for i in D2:
        u0[i], u1[i] = poly_eval(c_, XS[i]), poly_eval(d, XS[i])
    for i in D3:
        u0[i], u1[i] = poly_eval(e, XS[i]), poly_eval(f, XS[i])
    # explanations: scalar g1 rides L2/L3 (agrees on D2 u D3), etc.
    p_g1 = [(c_[i] + g1 * d[i]) % P for i in range(KDIM)]
    p_g2 = [(a1[i] + g2 * b1[i]) % P for i in range(KDIM)]
    p_g3 = [(a1[i] + g3 * b1[i]) % P for i in range(KDIM)]
    return verify_clique("Q1_triangle_three_pencils",
                         [g1, g2, g3], [p_g1, p_g2, p_g3], u0, u1,
                         expect_no3collinear=True)


# ----------------------------------------------------------------------------
# Q2: 4-clique in general position via a (k-1)-core sunflower
# ----------------------------------------------------------------------------

def build_sunflower_four() -> dict:
    gammas = [3, 5, 11, 17]
    W = list(range(0, KDIM - 1))               # 7 common-core coordinates
    w0 = [random.randrange(P) for _ in W]
    w1 = [random.randrange(P) for _ in W]
    xfree = XS[KDIM - 1]                       # 8th interpolation node
    polys = []
    for g in gammas:
        pts = [(XS[i], (w0[j] + g * w1[j]) % P) for j, i in enumerate(W)]
        pts.append((xfree, random.randrange(P)))
        polys.append(interpolate(pts))
    u0, u1 = [0] * N, [0] * N
    for j, i in enumerate(W):
        u0[i], u1[i] = w0[j], w1[j]
    # six pair blocks of size 4 in coordinates 7..30; coordinate 31 garbage
    pairs = list(itertools.combinations(range(4), 2))
    for b, (i, j) in enumerate(pairs):
        a, r = secant(gammas[i], polys[i], gammas[j], polys[j])
        for i_coord in range(7 + 4 * b, 7 + 4 * (b + 1)):
            u0[i_coord] = poly_eval(a, XS[i_coord])
            u1[i_coord] = poly_eval(r, XS[i_coord])
    u0[31], u1[31] = 1, 0   # garbage unless accidentally on a dual line
    return verify_clique("Q2_sunflower_four_general_position",
                         gammas, polys, u0, u1, expect_no3collinear=True)


# ----------------------------------------------------------------------------
# Q3: concurrency-design rank census for m >= 5 general-position cliques
# ----------------------------------------------------------------------------

def rref_mod_p(rows: list[list[int]]) -> tuple[int, list[list[int]]]:
    """Row-reduce; returns (rank, basis of solution space) for A x = 0."""
    if not rows:
        rows = []
    ncols = len(rows[0]) if rows else 0
    mat = [r[:] for r in rows]
    pivots = []
    rank = 0
    for col in range(ncols):
        piv = None
        for r in range(rank, len(mat)):
            if mat[r][col] % P:
                piv = r
                break
        if piv is None:
            continue
        mat[rank], mat[piv] = mat[piv], mat[rank]
        s = inv(mat[rank][col])
        mat[rank] = [c * s % P for c in mat[rank]]
        for r in range(len(mat)):
            if r != rank and mat[r][col] % P:
                f = mat[r][col]
                mat[r] = [(mat[r][cc] - f * mat[rank][cc]) % P
                          for cc in range(ncols)]
        pivots.append(col)
        rank += 1
        if rank == len(mat):
            break
    free = [c for c in range(ncols) if c not in pivots]
    basis = []
    for fc in free:
        vec = [0] * ncols
        vec[fc] = 1
        for r, pc in enumerate(pivots):
            vec[pc] = (-mat[r][fc]) % P
        basis.append(vec)
    return rank, basis


def concurrency_system(m: int, gammas: list[int],
                       design: list[tuple[int, tuple[int, ...]]]):
    """Linear system in the m*KDIM coefficients: for each design coordinate
    (coord, subset) the lifted values {(gamma_i, p_i(x))}_{i in subset} must be
    collinear in the value plane."""
    ncols = m * KDIM
    rows = []
    for coord, subset in design:
        x = XS[coord]
        xpow = [pow(x, dd, P) for dd in range(KDIM)]
        s = list(subset)
        i0, i1 = s[0], s[1]
        for ij in s[2:]:
            # (p_ij - p_i0)(g_i1 - g_i0) - (p_i1 - p_i0)(g_ij - g_i0) = 0
            row = [0] * ncols
            c1 = (gammas[i1] - gammas[i0]) % P
            c2 = (gammas[ij] - gammas[i0]) % P
            for dd in range(KDIM):
                row[ij * KDIM + dd] = (row[ij * KDIM + dd] + c1 * xpow[dd]) % P
                row[i0 * KDIM + dd] = (row[i0 * KDIM + dd] - c1 * xpow[dd]) % P
                row[i1 * KDIM + dd] = (row[i1 * KDIM + dd] - c2 * xpow[dd]) % P
                row[i0 * KDIM + dd] = (row[i0 * KDIM + dd] + c2 * xpow[dd]) % P
            rows.append(row)
    return rows


def design_counts_ok(m: int,
                     design: list[tuple[int, tuple[int, ...]]]) -> bool:
    vertex = [0] * m
    pair: dict[tuple[int, int], int] = {}
    triple: dict[tuple[int, int, int], int] = {}
    for _, subset in design:
        for i in subset:
            vertex[i] += 1
        for pr in itertools.combinations(sorted(subset), 2):
            pair[pr] = pair.get(pr, 0) + 1
        for tr in itertools.combinations(sorted(subset), 3):
            triple[tr] = triple.get(tr, 0) + 1
    if any(v < TVERT for v in vertex):
        return False
    for pr in itertools.combinations(range(m), 2):
        if pair.get(pr, 0) < KEDGE:
            return False
    # non-collinear triples concur on <= KDIM-1 coordinates (distinct-pencil
    # agreement cap); designs violating it are unrealizable in general position
    if any(v > KDIM - 1 for v in triple.values()):
        return False
    return True


def sample_design(m: int, size: int, tries: int = 4000):
    """Randomized search for a size-uniform design meeting all exact counts."""
    subsets = list(itertools.combinations(range(m), size))
    for _ in range(tries):
        choice = [random.choice(subsets) for _ in range(N)]
        design = list(enumerate(choice))
        if design_counts_ok(m, design):
            return design
    return None


def deterministic_design(m: int):
    """Hand-balanced admissible designs where random sampling is too crude."""
    if m == 5:
        # 26 triple coordinates (minimum possible collinearity-constraint
        # count) + 6 pair coordinates: per-vertex 90/soft, per-pair >= 8.
        triples = list(itertools.combinations(range(5), 3))  # 10 triples
        mults = {t: 2 for t in triples}
        # add 6 more spread so each vertex gains >= 2: (each vertex is in 6
        # of the 10 triples; base per-vertex = 2*6 = 12; need 18)
        for t in [(0, 1, 2), (0, 3, 4), (1, 3, 4), (2, 3, 4), (0, 1, 3),
                  (1, 2, 4)]:
            mults[t] += 1
        design = []
        coord = 0
        for t, k in mults.items():
            for _ in range(k):
                design.append((coord, t))
                coord += 1
        # 6 pair coordinates topping every vertex to 18 and every pair to 8
        pair_cover = [(0, 2), (0, 4), (2, 3), (0, 2), (1, 3), (1, 4)]
        for pr in pair_cover:
            design.append((coord, pr))
            coord += 1
        assert coord <= N
        return design if design_counts_ok(m, design) else None
    if m == 6:
        # all 15 4-subsets twice (30 coords) + 2 extra vertex-disjoint ones
        subsets = list(itertools.combinations(range(6), 4))
        design = []
        coord = 0
        for s in subsets:
            for _ in range(2):
                design.append((coord, s))
                coord += 1
        for s in [(0, 1, 2, 3), (0, 1, 4, 5)]:
            design.append((coord, s))
            coord += 1
        assert coord == N
        return design if design_counts_ok(m, design) else None
    if m == 7:
        # all C(7,4) = 35 4-subsets minus 3 (chosen so no vertex is dropped
        # more than twice): 32 coordinates exactly.
        drop = {(0, 1, 2, 3), (0, 4, 5, 6), (1, 2, 4, 5)}
        design = []
        coord = 0
        for s in itertools.combinations(range(7), 4):
            if s in drop:
                continue
            design.append((coord, s))
            coord += 1
        assert coord == N
        return design if design_counts_ok(m, design) else None
    if m == 8:
        # local-search repair over 5-subsets of [8]
        subsets = list(itertools.combinations(range(8), 5))
        choice = [random.choice(subsets) for _ in range(N)]
        for _ in range(20000):
            design = list(enumerate(choice))
            if design_counts_ok(m, design):
                return design
            # find a violated count and repair with a targeted swap
            vertex = [0] * m
            pair: dict[tuple[int, int], int] = {}
            triple: dict[tuple[int, ...], int] = {}
            for s in choice:
                for i in s:
                    vertex[i] += 1
                for pr in itertools.combinations(s, 2):
                    pair[pr] = pair.get(pr, 0) + 1
                for tr in itertools.combinations(s, 3):
                    triple[tr] = triple.get(tr, 0) + 1
            over = [t for t, v in triple.items() if v > KDIM - 1]
            under_v = [v for v in range(m) if vertex[v] < TVERT]
            under_p = [pr for pr in itertools.combinations(range(m), 2)
                       if pair.get(pr, 0) < KEDGE]
            idx = random.randrange(N)
            if over:
                t = random.choice(over)
                cands = [i for i, s in enumerate(choice)
                         if set(t) <= set(s)]
                idx = random.choice(cands)
                repl = [s for s in subsets if not set(t) <= set(s)]
            elif under_v:
                v = random.choice(under_v)
                repl = [s for s in subsets if v in s]
            elif under_p:
                pr = random.choice(under_p)
                repl = [s for s in subsets if set(pr) <= set(s)]
            else:
                repl = subsets
            choice[idx] = random.choice(repl)
        return None
    return None


def try_general_position(m: int, size: int, samples: int = 200,
                         design=None, tag_suffix: str = "") -> dict:
    gammas = [3 + 6 * i for i in range(m)]
    if design is None:
        design = sample_design(m, size)
    out = {
        "tag": f"Q3_general_position_m{m}_s{size}{tag_suffix}",
        "m": m,
        "subset_size": size,
        "design_found": design is not None,
    }
    if design is None:
        return out
    # sanity: the single-pencil locus lies in the kernel of the system
    a_test = [random.randrange(P) for _ in range(KDIM)]
    r_test = [random.randrange(P) for _ in range(KDIM)]
    pencil_vec = []
    for g in gammas:
        pencil_vec.extend([(a_test[c] + g * r_test[c]) % P
                           for c in range(KDIM)])
    rows_check = concurrency_system(m, gammas, design)
    assert all(sum(rr[c] * pencil_vec[c] for c in range(m * KDIM)) % P == 0
               for rr in rows_check), "pencil locus not in kernel"
    rows = concurrency_system(m, gammas, design)
    rank, basis = rref_mod_p(rows)
    dim = m * KDIM - rank
    out["constraints"] = len(rows)
    out["rank"] = rank
    out["solution_dim"] = dim
    out["pencil_locus_dim"] = 2 * KDIM      # single-pencil solutions a+g r
    found = None
    for _ in range(samples):
        coeffvec = [0] * (m * KDIM)
        for vec in basis:
            s = random.randrange(P)
            for c in range(m * KDIM):
                coeffvec[c] = (coeffvec[c] + s * vec[c]) % P
        polys = [coeffvec[i * KDIM:(i + 1) * KDIM] for i in range(m)]
        if len({tuple(p) for p in polys}) < m:
            continue
        bad = False
        for i, j, l in itertools.combinations(range(m), 3):
            if collinear_triple(gammas, polys, i, j, l):
                bad = True
                break
        if not bad:
            found = polys
            break
    out["general_position_sample_found"] = found is not None
    if found is None:
        return out
    # realize u from the design and run the full clique verification
    u0, u1 = [1] * N, [0] * N
    for coord, subset in design:
        s = list(subset)
        i0, i1 = s[0], s[1]
        x = XS[coord]
        v0 = poly_eval(found[i0], x)
        v1 = poly_eval(found[i1], x)
        slope = (v1 - v0) * inv(gammas[i1] - gammas[i0]) % P
        u1[coord] = slope
        u0[coord] = (v0 - gammas[i0] * slope) % P
    ver = verify_clique(out["tag"] + "_realized", gammas, found, u0, u1,
                        expect_no3collinear=True)
    out["realized_clique_valid"] = ver["is_valid_clique"]
    out["realized_no3collinear"] = ver["no3collinear"]
    out["realized"] = ver
    return out


# ----------------------------------------------------------------------------
# Q4: single-line clique capacity n - t + 1
# ----------------------------------------------------------------------------

def build_single_line_clique(m: int) -> dict:
    """m collinear points on one pencil, core z = t - 1, one fresh petal each."""
    a = [random.randrange(P) for _ in range(KDIM)]
    r = [random.randrange(P) for _ in range(KDIM)]
    gammas = [3 + 2 * i for i in range(m)]
    polys = [poly_sub([0] * KDIM, poly_sub([0] * KDIM,
             [(a[c] + g * r[c]) % P for c in range(KDIM)])) for g in gammas]
    z = TVERT - 1
    u0, u1 = [0] * N, [0] * N
    for i in range(z):
        u0[i], u1[i] = poly_eval(a, XS[i]), poly_eval(r, XS[i])
    # fresh petal coordinate for scalar i at position z+i: on gamma_i's dual
    # line but off the pencil core (perturb u1 so only gamma_i matches)
    for idx, g in enumerate(gammas):
        i = z + idx
        if i >= N:
            return {"tag": f"Q4_single_line_m{m}", "m": m,
                    "fits_domain": False}
        val = (poly_eval(a, XS[i]) + g * poly_eval(r, XS[i])) % P
        u1[i] = (poly_eval(r, XS[i]) + 1) % P
        u0[i] = (val - g * u1[i]) % P
    ver = verify_clique(f"Q4_single_line_m{m}", gammas, polys, u0, u1,
                        expect_no3collinear=False)
    ver["fits_domain"] = True
    return ver


# ----------------------------------------------------------------------------
# main
# ----------------------------------------------------------------------------

def main() -> None:
    verdicts = []

    q1 = build_triangle()
    print(f"[Q1] triangle of pencils: valid_clique={q1['is_valid_clique']} "
          f"no3collinear={q1['no3collinear']} "
          f"core_identity={q1['core_identity_ok']}")
    verdicts.append(("Q1 3-clique with THREE DISTINCT pencils realizable "
                     "(refutes clique->single-pencil transitivity)",
                     q1["matches_expectation"]))

    q2 = build_sunflower_four()
    print(f"[Q2] sunflower 4-clique:  valid_clique={q2['is_valid_clique']} "
          f"no3collinear={q2['no3collinear']} "
          f"core_identity={q2['core_identity_ok']}")
    verdicts.append(("Q2 4-clique in GENERAL POSITION realizable "
                     "(refutes 4-clique->collinear-triple)",
                     q2["matches_expectation"]))

    print("[Q3] general-position rank census (unknowns = m*k, pencil locus "
          f"dim = {2 * KDIM}):")
    census = []
    cases = [
        ("random", 5, 3, None),
        ("random", 5, 3, None),
        ("random", 5, 3, None),
        ("det-minimal", 5, 0, deterministic_design(5)),
        ("det-balanced", 6, 4, deterministic_design(6)),
        ("det-balanced", 7, 4, deterministic_design(7)),
        ("local-search", 8, 5, deterministic_design(8)),
    ]
    for kind, m, size, design in cases:
        res = try_general_position(m, size, design=design,
                                   tag_suffix=f"_{kind}")
        res["kind"] = kind
        census.append(res)
        if not res["design_found"]:
            print(f"  m={m} {kind}: NO admissible design found")
            continue
        line = (f"  m={m} {kind}: constraints={res['constraints']} "
                f"rank={res['rank']} dim={res['solution_dim']} "
                f"genpos_sample={res['general_position_sample_found']}")
        if res.get("realized"):
            line += (f" realized_valid={res['realized_clique_valid']} "
                     f"realized_genpos={res['realized_no3collinear']}")
        print(line)
    pencil_only = [(r["m"], r["kind"]) for r in census
                   if r.get("solution_dim") == 2 * KDIM]
    genpos_success = [(r["m"], r["kind"]) for r in census
                      if r.get("realized_clique_valid")
                      and r.get("realized_no3collinear")]
    print(f"  pencil-only designs (dim = {2 * KDIM}): {pencil_only}")
    print(f"  general-position cliques realized: {genpos_success}")
    # honest census: report, no fixed expectation on individual m
    verdicts.append(("Q3 census ran on all cases",
                     len(census) == len(cases)))

    q4_max = build_single_line_clique(N - TVERT + 1)
    q4_over = build_single_line_clique(N - TVERT + 2)
    cap_realized = q4_max.get("is_valid_clique", False)
    over_fits = q4_over.get("fits_domain", True) and \
        q4_over.get("is_valid_clique", False)
    print(f"[Q4] single-line capacity: m={N - TVERT + 1} realized="
          f"{cap_realized}; m={N - TVERT + 2} realizable_this_way={over_fits} "
          "(packing law forbids exceeding n-t+1)")
    verdicts.append((f"Q4 single line carries n-t+1={N - TVERT + 1} points",
                     cap_realized))

    print("\n=== VERDICTS ===")
    ok = True
    for msg, good in verdicts:
        print(f"  {'PASS' if good else 'FAIL'}: {msg}")
        ok = ok and good
    if not ok:
        raise SystemExit(1)
    print("probe_w4_clique_pencil_structure: all recorded expectations hold")


if __name__ == "__main__":
    main()
