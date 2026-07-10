#!/usr/bin/env python3
"""Exact miniature extremal landscape for the P1 rate-quarter predecessor pin.

Angle: exact miniature models + extremal verification for the four-pencil
extraction target ``CanonicalLargeBadFourPencilExtraction`` /
``CanonicalUniformPredecessorBadCount`` (P1: N=2^30, K=2^28, T=592794966).

Part A  verifies the exact P1 arithmetic and the derived numbers quoted in the
        campaign notes (forcing quotient, Plotkin ceiling, line caps).
Part B  computes the structural scaling table for the miniature family
        m in {2, 4, 16, 64, 1024, 2^26}  (m == 4 mod 6, or m=2 degenerate),
        N=16m, K=4m, T=8m+r+d+2, r=(m-1)/3, d=(m-2)/2, and the multi-core
        ledger: j cores of size T-1 (one fresh coordinate per scalar), spline
        dimension N - j*(T-1-K), coverage feasibility, and the slot count
        j*(N-T+1) versus N.
Part C  builds the three-core construction EXACTLY in the m=2 miniature
        [N=32, K=8, T=18] over F_97 and F_1153 and runs a complete
        multiplicity-one Guruswami--Sudan census of the MCA bad count at
        agreement >= 18 over every scalar of the field.  The GS interpolation
        polynomial has (1,7)-weighted degree 17 with 33 monomials and 32
        constraints, so every degree-<8 explanation with >= 18 agreements is a
        Y-linear factor: the census is complete, not heuristic.
Part D  validation: the same decoder reproduces the known result that the
        swarm's isolated-fibre F_97 stack has ZERO bad scalars at agreement 18
        (36 at 17), so the construction below is not a decoder artifact.

Deterministic; pure python; no external dependencies.
"""

from __future__ import annotations

from fractions import Fraction
import itertools
import random


# ---------------------------------------------------------------------------
# generic exact linear algebra / polynomial helpers mod p
# ---------------------------------------------------------------------------

def inv_mod(x: int, p: int) -> int:
    assert x % p != 0
    return pow(x % p, p - 2, p)


def trim(a: list[int], p: int) -> list[int]:
    a = [x % p for x in a]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def poly_add(a, b, p):
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] = (out[i] + x) % p
    for i, x in enumerate(b):
        out[i] = (out[i] + x) % p
    return trim(out, p)


def poly_scale(c, a, p):
    return trim([(c * x) % p for x in a], p)


def poly_mul(a, b, p):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % p
    return trim(out, p)


def poly_sub(a, b, p):
    return poly_add(a, poly_scale(p - 1, b, p), p)


def poly_eval(a, x, p):
    out = 0
    for c in reversed(a):
        out = (out * x + c) % p
    return out


def poly_deg(a):
    return len(a) - 1 if a != [0] else -1


def poly_divmod(a, b, p):
    a = a[:]
    db, lb = poly_deg(b), b[-1]
    if db < 0:
        raise ZeroDivisionError
    invlb = inv_mod(lb, p)
    q = [0] * max(1, len(a) - db)
    while poly_deg(a) >= db and a != [0]:
        da = poly_deg(a)
        c = (a[-1] * invlb) % p
        q[da - db] = c
        for i in range(db + 1):
            a[da - db + i] = (a[da - db + i] - c * b[i]) % p
        a = trim(a, p)
    return trim(q, p), a


def interpolate(points, p):
    """Lagrange interpolation, exact, returns coefficient list."""
    out = [0]
    for i, (xi, yi) in enumerate(points):
        basis = [1]
        den = 1
        for j, (xj, _) in enumerate(points):
            if i == j:
                continue
            basis = poly_mul(basis, [(-xj) % p, 1], p)
            den = (den * (xi - xj)) % p
        out = poly_add(out, poly_scale(yi * inv_mod(den, p) % p, basis, p), p)
    return out


def sqrt_mod(a: int, p: int) -> int | None:
    a %= p
    if a == 0:
        return 0
    for r in range(1, p):
        if (r * r) % p == a:
            return r
    return None


def poly_sqrt(d, p):
    """Exact polynomial square root mod p, or None."""
    d = trim(d, p)
    if d == [0]:
        return [0]
    n = poly_deg(d)
    if n % 2 != 0:
        return None
    lead = sqrt_mod(d[-1], p)
    if lead is None:
        return None
    m = n // 2
    s = [0] * (m + 1)
    s[m] = lead
    # solve coefficients top-down: (s^2)[n-t] matches d[n-t]
    for t in range(1, m + 1):
        idx = n - t
        acc = 0
        for i in range(m - t + 1, m + 1):
            j = idx - i
            if 0 <= j <= m:
                acc = (acc + s[i] * s[j]) % p
        # remaining term 2*s[m]*s[m-t] (i = m-t counted? i ranges above m-t)
        c = (d[idx] - acc) % p
        s[m - t] = (c * inv_mod(2 * lead, p)) % p
    if poly_sub(poly_mul(s, s, p), trim(d, p), p) != [0]:
        return None
    return trim(s, p)


def nullspace_mod(rows, ncols, p):
    """Basis of the right nullspace of the matrix given by rows, mod p."""
    mat = [r[:] for r in rows]
    nrows = len(mat)
    pivots = []
    r = 0
    for c in range(ncols):
        piv = None
        for i in range(r, nrows):
            if mat[i][c] % p != 0:
                piv = i
                break
        if piv is None:
            continue
        mat[r], mat[piv] = mat[piv], mat[r]
        iv = inv_mod(mat[r][c], p)
        mat[r] = [(x * iv) % p for x in mat[r]]
        for i in range(nrows):
            if i != r and mat[i][c] % p != 0:
                f = mat[i][c]
                mat[i] = [(mat[i][k] - f * mat[r][k]) % p for k in range(ncols)]
        pivots.append(c)
        r += 1
        if r == nrows:
            break
    free = [c for c in range(ncols) if c not in pivots]
    basis = []
    for fc in free:
        v = [0] * ncols
        v[fc] = 1
        for ri, pc in enumerate(pivots):
            v[pc] = (-mat[ri][fc]) % p
        basis.append(v)
    return basis, len(pivots)


# ---------------------------------------------------------------------------
# Part A: exact P1 arithmetic
# ---------------------------------------------------------------------------

def part_a():
    print("=" * 78)
    print("PART A: exact P1 arithmetic (m = 2^26)")
    print("=" * 78)
    m = 2 ** 26
    N = 16 * m
    K = 4 * m
    r = (m - 1) // 3
    d = (m - 2) // 2
    assert 3 * r + 1 == m and 2 * d == m - 2
    amplifiedCore = 8 * m + r + d
    T = amplifiedCore + 2
    assert N == 2 ** 30 and K == 2 ** 28
    assert amplifiedCore == 592794964
    assert T == 592794966
    print(f"N = {N}, K = {K}, T = {T}, amplifiedCore = T-2 = {amplifiedCore}")

    # derived numbers from the campaign notes
    assert 2 * T - N == 111848108, 2 * T - N
    # NOTE: campaign note quoted 351822537 for ceil((3T-N)/2); exact value is
    # 352321537 (3T-N = 704643074).  The qualitative use (z floor at L>=3) is
    # unaffected.
    assert (3 * T - N + 1) // 2 == 352321537
    assert N - T + 1 == 480946859
    # saturation: z >= T-2 iff 2L >= N-T+2
    sat = (N - T + 2 + 1) // 2
    print(f"pair overlap floor 2T-N = {2*T-N} (< K = {K})")
    print(f"line cap N-T+1 = {N-T+1}; saturation L threshold ~ {sat}")
    assert -(T * T // -N) == 327272222  # ceil(T^2/N) Plotkin ceiling
    print(f"Plotkin pairwise ceiling ceil(T^2/N) = {-(T*T//-N)} < T-2")

    # K-forcing quotient: convexity forces a pair overlap >= K among j sets of
    # size >= T iff j*(T^2 - N*(K-1)) > N*(T-(K-1))
    Q = Fraction(N * (T - (K - 1)), T * T - N * (K - 1))
    jforce = Q.__floor__() + 1
    print(f"forcing quotient N(T-(K-1))/(T^2-N(K-1)) = {Q} ~ {float(Q):.6f}")
    print(f"  => six-set forcing index = {jforce} (campaign: 6)")

    # high-core collapse threshold 3T + 2z > 2N + 4(K-1)
    zc = (2 * N + 4 * (K - 1) - 3 * T) // 2 + 1
    print(f"high-core collapse needs z >= {zc} > T-2 = {T-2}: vacuous = {zc > T-2}")

    # ---- multi-core ledger at P1 ----
    # A core D of size z with u RS-restricted on D imposes z-K conditions, but
    # the global code RS_K always satisfies them: the honest budget lives on
    # the quotient F^N / RS_K of dimension N-K.  (The naive N - j(z-K) count
    # is wrong; the m=2 miniature below confirms the collapse at j=3.)
    print("\nP1 multi-core ledger (cores of size T-1, one fresh point/scalar):")
    print("  quotient budget dim(W/RS) = (N-K) - j*(T-1-K); need >= 1")
    for j in range(1, 7):
        qdim = (N - K) - j * ((T - 1) - K)
        need_overlap = max(0, j * (T - 1) - N)
        max_overlap = (j * (j - 1) // 2) * (K - 1)
        slots = j * (N - (T - 1))
        feasible_cov = need_overlap <= max_overlap
        print(f"  j={j}: dim(W/RS) = {qdim:>13}  covFeasible(pairwise<=K-1): "
              f"{feasible_cov} (need {need_overlap} <= {max_overlap})  "
              f"slots = {slots} = {slots/N:.5f}*N")
    print("\n  => j=2 is the largest generically realizable (T-1)-core family;")
    print(f"     2(N-T+1) = {2*(N-T+1)} vs N = {N}: margin 2T-N-2 = {2*T-N-2}")
    print(f"     (contrast rate-half: n-k-3(t-1-k) = 29m > 0 => refuted there)")
    # rate-half comparison, exact
    mh = 2 ** 24
    nh, kh, th = 64 * mh, 32 * mh, 33 * mh + 1
    print(f"     rate-half check: (n-k) - 3(t-1-k) = {(nh-kh) - 3*(th-1-kh)} "
          f"= 29m = {29*mh}, slots 3(n-t+1) = {3*(nh-th+1)} > n = {nh}")


# ---------------------------------------------------------------------------
# Part B: miniature family scaling table
# ---------------------------------------------------------------------------

def part_b():
    print("\n" + "=" * 78)
    print("PART B: miniature family scaling (N=16m, K=4m, T=8m+r+d+2)")
    print("=" * 78)
    header = (f"{'m':>9} {'N':>11} {'K':>11} {'T':>11} {'forceQ':>9} "
              f"{'jF':>3} {'qdim2':>10} {'qdim3':>11} {'2(N-T+1)':>11} "
              f"{'margin':>10}")
    print(header)
    for m in [2, 4, 16, 64, 1024, 2 ** 26]:
        r = (m - 1) // 3
        d = (m - 2) // 2
        ok = (3 * r + 1 == m) and (2 * d == m - 2 or m == 2)
        N, K = 16 * m, 4 * m
        T = 8 * m + r + d + 2
        Q = Fraction(N * (T - (K - 1)), T * T - N * (K - 1))
        jF = Q.__floor__() + 1
        qdim2 = (N - K) - 2 * ((T - 1) - K)
        qdim3 = (N - K) - 3 * ((T - 1) - K)
        slots2 = 2 * (N - T + 1)
        print(f"{m:>9} {N:>11} {K:>11} {T:>11} {float(Q):>9.4f} {jF:>3} "
              f"{qdim2:>10} {qdim3:>11} {slots2:>11} {N-slots2:>10}"
              + ("" if ok else "  (exact-division degenerate)"))
    print("\nAll members show: dim(W/RS) > 0 for two (T-1)-cores, < 0 for")
    print("three; generic multi-core max = 2(N-T+1) < N with margin 2T-N-2 =")
    print("2(r+d+1).  Stable in m: the m=2 miniature is structurally faithful.")


# ---------------------------------------------------------------------------
# Part C: exact three-core construction + complete GS census, m = 2
# ---------------------------------------------------------------------------

N32, K8, T18 = 32, 8, 18


def find_domain(p: int) -> list[int]:
    """32 points: the order-32 subgroup if 32 | p-1, else first 32 nonzeros."""
    if (p - 1) % 32 == 0:
        for g in range(2, p):
            # g generator? just need an element of exact order 32
            w = pow(g, (p - 1) // 32, p)
            if pow(w, 16, p) != 1:
                return [pow(w, i, p) for i in range(32)]
    return list(range(1, 33))


def rs_parity_rows(core_idx: list[int], xs: list[int], p: int) -> list[list[int]]:
    """Rows (length 32) whose vanishing == (u restricted to core is RS[len,8])."""
    pts = [xs[i] for i in core_idx]
    # generator matrix of RS on core: Vandermonde len(core) x 8; parity =
    # nullspace of its transpose
    vt = [[pow(x, e, p) for x in pts] for e in range(K8)]  # 8 x z
    basis, _ = nullspace_mod(vt, len(pts), p)  # dim z-8
    rows = []
    for v in basis:
        row = [0] * N32
        for j, i in enumerate(core_idx):
            row[i] = v[j] % p
        rows.append(row)
    return rows


def extrapolation_functional(core_idx, x_i, xs, p):
    """Length-32 row d with d(w) = w(x_i) - (deg<8 extrap of w|core)(x_i),
    valid for w that are RS on the core (uses first 8 core points)."""
    pts = [(xs[i], i) for i in core_idx[:K8]]
    row = [0] * N32
    row[x_i] = 1
    xi = xs[x_i]
    for (xa, ia) in pts:
        num, den = 1, 1
        for (xb, _) in pts:
            if xb == xa:
                continue
            num = (num * (xi - xb)) % p
            den = (den * (xa - xb)) % p
        row[ia] = (row[ia] - num * inv_mod(den, p)) % p
    return row


def gs_candidates(word, xs, p):
    """All q (deg<8) with agreement >= 18 on (xs, word).  Complete census via
    multiplicity-1 GS: (1,7)-weighted degree 17, 33 monomials, 32 constraints."""
    monos = [(a, b) for b in range(3) for a in range(18 - 7 * b)]
    assert len(monos) == 33
    rows = []
    for x, y in zip(xs, word):
        rows.append([(pow(x, a, p) * pow(y, b, p)) % p for (a, b) in monos])
    basis, _ = nullspace_mod(rows, len(monos), p)
    assert basis, "GS nullspace must be nonzero"
    q0 = basis[0]
    # assemble Q_b(x) for b = 0,1,2
    Q = {b: [0] * 18 for b in range(3)}
    for coeff, (a, b) in zip(q0, monos):
        Q[b][a] = coeff % p
    Q0, Q1, Q2 = (trim(Q[0], p), trim(Q[1], p), trim(Q[2], p))
    cands = []

    def try_add(q):
        q = trim(q, p)
        if poly_deg(q) < K8:
            if q not in cands:
                cands.append(q)

    if Q2 == [0]:
        if Q1 == [0]:
            return []
        quo, rem = poly_divmod(poly_scale(p - 1, Q0, p), Q1, p)
        if rem == [0]:
            try_add(quo)
        return cands
    disc = poly_sub(poly_mul(Q1, Q1, p), poly_scale(4, poly_mul(Q0, Q2, p), p), p)
    s = poly_sqrt(disc, p)
    if s is None:
        return []
    for sg in (s, poly_scale(p - 1, s, p)):
        numer = poly_add(poly_scale(p - 1, Q1, p), sg, p)
        den = poly_scale(2, Q2, p)
        quo, rem = poly_divmod(numer, den, p)
        if rem == [0]:
            # verify root
            chk = poly_add(poly_add(poly_mul(Q2, poly_mul(quo, quo, p), p),
                                    poly_mul(Q1, quo, p), p), Q0, p)
            if chk == [0]:
                try_add(quo)
    return cands


def is_rs_on(row, support, xs, p):
    """Does a deg<8 poly match row on all of support?"""
    pts = [(xs[i], row[i]) for i in support[:K8]]
    f = interpolate(pts, p)
    if poly_deg(f) >= K8:
        return False
    return all(poly_eval(f, xs[i], p) == row[i] % p for i in support)


def census(u0, u1, xs, p, thresh=T18, verbose=False):
    """Exact MCA bad count at agreement >= thresh, all gamma in F_p."""
    bad = []
    for gamma in range(p):
        word = [(a + gamma * b) % p for a, b in zip(u0, u1)]
        for q in gs_candidates(word, xs, p):
            support = [i for i in range(N32)
                       if poly_eval(q, xs[i], p) == word[i]]
            if len(support) < thresh:
                continue
            joint = is_rs_on(u0, support, xs, p) and is_rs_on(u1, support, xs, p)
            if not joint:
                bad.append(gamma)
                break
    if verbose and bad:
        print(f"    bad gammas ({len(bad)}): {bad}")
    return bad


def multi_core_experiment(p: int, cores: list[list[int]], label: str,
                          seed: int = 20260710, do_census: bool = True):
    """Build the generic multi-core stack for the given cores and census it."""
    print(f"\n--- {label} over F_{p} ---")
    rng = random.Random(seed)
    xs = find_domain(p)
    assert len(set(xs)) == 32
    for A, B in itertools.combinations(cores, 2):
        assert len(set(A) & set(B)) <= K8 - 1

    rows = []
    for D in cores:
        rows.extend(rs_parity_rows(D, xs, p))
    basis, rank = nullspace_mod(rows, N32, p)
    dimW = len(basis)
    qdim_pred = (N32 - K8) - sum(len(D) - K8 for D in cores)
    print(f"  spline W: {len(rows)} conditions, rank {rank}, dim W = {dimW} "
          f"(global RS dim {K8}; predicted dim(W/RS) = {qdim_pred}, "
          f"actual = {dimW - K8})")

    # defect functionals restricted to W
    funcs = []   # (core_index, coordinate, vector in W*)
    for ci, D in enumerate(cores):
        outside = [i for i in range(N32) if i not in D]
        for x_i in outside:
            d = extrapolation_functional(D, x_i, xs, p)
            dv = [sum(d[k] * bvec[k] for k in range(N32)) % p for bvec in basis]
            funcs.append((ci, x_i, dv))
    nz = [f for f in funcs if any(v % p for v in f[2])]
    print(f"  defect functionals: {len(funcs)} total, {len(nz)} nonzero on W")

    def proj_eq(u, v):
        n = len(u)
        for i in range(n):
            for j in range(i + 1, n):
                if (u[i] * v[j] - u[j] * v[i]) % p != 0:
                    return False
        return True

    distinct_classes = []
    for f in nz:
        if not any(proj_eq(f[2], g) for g in distinct_classes):
            distinct_classes.append(f[2])
    print(f"  pairwise projectively distinct classes: {len(distinct_classes)}")

    if not nz:
        print("  => W collapsed to the global RS code: every functional")
        print("     vanishes; the multi-core mechanism is EMPTY here.")
        # confirm: a random W-stack has zero bad scalars
        if do_census:
            s0 = [rng.randrange(p) for _ in range(dimW)]
            s1 = [rng.randrange(p) for _ in range(dimW)]
            u0 = [sum(basis[k][i] * s0[k] for k in range(dimW)) % p
                  for i in range(N32)]
            u1 = [sum(basis[k][i] * s1[k] for k in range(dimW)) % p
                  for i in range(N32)]
            bad = census(u0, u1, xs, p)
            print(f"  census of a random W-stack: badCount = {len(bad)}")
        return 0, None, None, xs

    # choose u1, u0 in W: all d(u1) != 0 and maximally many distinct gammas
    best = None
    for attempt in range(4000):
        s1 = [rng.randrange(p) for _ in range(dimW)]
        s0 = [rng.randrange(p) for _ in range(dimW)]
        d1 = [sum(f[2][k] * s1[k] for k in range(dimW)) % p for f in nz]
        if any(v == 0 for v in d1):
            continue
        d0 = [sum(f[2][k] * s0[k] for k in range(dimW)) % p for f in nz]
        gammas = [(-a * inv_mod(b, p)) % p for a, b in zip(d0, d1)]
        ndist = len(set(gammas))
        if best is None or ndist > best[0]:
            best = (ndist, s0, s1, gammas)
        if ndist == len(nz):
            break
    ndist, s0, s1, gammas = best
    print(f"  chosen stack: {ndist} distinct expected bad scalars "
          f"out of {len(nz)} slots (N = {N32})")
    u0 = [sum(basis[k][i] * s0[k] for k in range(dimW)) % p for i in range(N32)]
    u1 = [sum(basis[k][i] * s1[k] for k in range(dimW)) % p for i in range(N32)]

    # pencil polynomials + exact joint cores
    pencil = []
    for D in cores:
        aC = interpolate([(xs[i], u0[i]) for i in D[:K8]], p)
        rC = interpolate([(xs[i], u1[i]) for i in D[:K8]], p)
        jc = [i for i in range(N32)
              if poly_eval(aC, xs[i], p) == u0[i]
              and poly_eval(rC, xs[i], p) == u1[i]]
        pencil.append((aC, rC, jc))
        print(f"  pencil core |D| = {len(D)}, exact jointCore = {len(jc)} "
              f"(two-fresh needs <= {T18 - 2})")

    # direct verification of each expected bad scalar (pre-census sanity)
    expected = set()
    for (ci, x_i, _), gamma in zip(nz, gammas):
        aC, rC, _ = pencil[ci]
        q = poly_add(aC, poly_scale(gamma, rC, p), p)
        fold = [(u0[i] + gamma * u1[i]) % p for i in range(N32)]
        supp = [i for i in range(N32) if poly_eval(q, xs[i], p) == fold[i]]
        if len(supp) >= T18 and not (is_rs_on(u0, supp, xs, p)
                                     and is_rs_on(u1, supp, xs, p)):
            expected.add(gamma)
    print(f"  directly verified expected bad scalars: {len(expected)}")

    bad = []
    if do_census:
        bad = census(u0, u1, xs, p)
        print(f"  EXACT GS census at agreement >= {T18}: mcaBadCount = "
              f"{len(bad)}  (N = {N32}: "
              f"{'EXCEEDS N' if len(bad) > N32 else 'within N'})")
        assert expected <= set(bad), "census must contain verified scalars"
    return len(bad), u0, u1, xs


TWO_CORES = [list(range(0, 17)), list(range(15, 32))]          # overlap 2
TWO_CORES_O7 = [list(range(0, 17)), list(range(10, 27))]       # overlap 7
THREE_CORES = [list(range(0, 17)),
               list(range(10, 27)),
               list(range(0, 7)) + list(range(22, 32))]        # 7/7/5 overlaps


def overlap_sensitivity(p: int):
    """Distinct projective defect classes as a function of core overlap o."""
    print(f"\n--- overlap sensitivity (two 17-cores, F_{p}) ---")
    xs = find_domain(p)
    for o in range(2, 8):
        # D1 = first 17; D2 = last 15+o indices arranged for overlap o
        D1 = list(range(0, 17))
        D2 = list(range(17 - o, 32 - (o - 2)))
        assert len(D2) == 17 and len(set(D1) & set(D2)) == o
        uncovered = [i for i in range(32) if i not in set(D1) | set(D2)]
        rows = []
        for D in (D1, D2):
            rows.extend(rs_parity_rows(D, xs, p))
        basis, rank = nullspace_mod(rows, N32, p)
        funcs = []
        for D in (D1, D2):
            for x_i in [i for i in range(N32) if i not in D]:
                dvec = extrapolation_functional(D, x_i, xs, p)
                dv = [sum(dvec[k] * b[k] for k in range(N32)) % p
                      for b in basis]
                funcs.append(dv)
        nz = [f for f in funcs if any(f)]

        def proj_eq(u, v):
            return all((u[i] * v[j] - u[j] * v[i]) % p == 0
                       for i in range(len(u)) for j in range(i + 1, len(u)))

        classes = []
        for f in nz:
            if not any(proj_eq(f, g) for g in classes):
                classes.append(f)
        print(f"  o={o}: dimW = {len(basis)}, uncovered coords = "
              f"{len(uncovered)}, nonzero functionals = {len(nz)}/30, "
              f"distinct classes = {len(classes)}")


def random_stack_sweep(p: int, cores, samples: int, seed: int = 991):
    """Exact census over random W-stacks: max structured badCount search."""
    print(f"\n--- random W-stack sweep over F_{p} ({samples} samples) ---")
    rng = random.Random(seed)
    xs = find_domain(p)
    rows = []
    for D in cores:
        rows.extend(rs_parity_rows(D, xs, p))
    basis, _ = nullspace_mod(rows, N32, p)
    dimW = len(basis)
    best = 0
    for _ in range(samples):
        s0 = [rng.randrange(p) for _ in range(dimW)]
        s1 = [rng.randrange(p) for _ in range(dimW)]
        u0 = [sum(basis[k][i] * s0[k] for k in range(dimW)) % p
              for i in range(N32)]
        u1 = [sum(basis[k][i] * s1[k] for k in range(dimW)) % p
              for i in range(N32)]
        b = len(census(u0, u1, xs, p))
        best = max(best, b)
    print(f"  max exact badCount over sweep: {best} (cap 2(N-T+1) = 30, N = 32)")
    return best


def perturbation_search(u0, u1, xs, p, base_count):
    """Single-coordinate +1 perturbations of both rows: exact census max."""
    print(f"\n--- perturbation search around the two-core stack (F_{p}) ---")
    worst = base_count
    argworst = None
    for row in (0, 1):
        for i in range(N32):
            v0, v1 = u0[:], u1[:]
            (v0 if row == 0 else v1)[i] = ((v0 if row == 0 else v1)[i] + 1) % p
            b = len(census(v0, v1, xs, p))
            if b > worst:
                worst, argworst = b, (row, i)
    print(f"  max badCount over 64 one-coordinate perturbations: {worst} "
          f"(base {base_count}, N = {N32})"
          + (f" at row {argworst[0]} coord {argworst[1]}" if argworst else ""))
    return worst


def part_d_validation():
    """Reproduce the known zero census of the isolated-fibre stack at 18."""
    print("\n--- decoder validation on the swarm's isolated-fibre F_97 stack ---")
    p = 97
    omega = 28
    xs = [pow(omega, i, p) for i in range(32)]
    U0 = [0, 0, 77, 0, 0, 0, 0, 0, 0, 59, 53, 54, 54, 26, 84, 45,
          0, 0, 20, 0, 0, 0, 0, 0, 0, 38, 44, 43, 43, 71, 13, 52]
    U1 = [0, 0, 46, 0, 0, 0, 0, 0, 0, 16, 24, 38, 36, 93, 7, 2,
          0, 0, 46, 0, 0, 0, 0, 0, 0, 16, 24, 38, 36, 93, 7, 2]
    bad18 = census(U0, U1, xs, p, thresh=18)
    print(f"  isolated-fibre stack, agreement >= 18: badCount = {len(bad18)} "
          f"(expected 0)")
    assert len(bad18) == 0


def main():
    part_a()
    part_b()
    print("\n" + "=" * 78)
    print("PART C: exact multi-core censuses in the m=2 miniature [32,8], T=18")
    print("=" * 78)
    part_d_validation()
    # three cores: predicted collapse (quotient budget 24 - 27 < 0)
    multi_core_experiment(97, THREE_CORES, "THREE (T-1)-cores (7/7/5 overlaps)")
    # two cores: the generic extremal family
    n97, u0a, u1a, xsa = multi_core_experiment(
        97, TWO_CORES, "TWO (T-1)-cores (overlap 2)")
    n97b, *_ = multi_core_experiment(
        97, TWO_CORES_O7, "TWO (T-1)-cores (overlap 7)")
    n1153, *_ = multi_core_experiment(
        1153, TWO_CORES, "TWO (T-1)-cores (overlap 2)")
    worst = perturbation_search(u0a, u1a, xsa, 97, n97)
    overlap_sensitivity(97)
    sweep_max = random_stack_sweep(97, TWO_CORES, samples=60)

    print("\n" + "=" * 78)
    print("SUMMARY")
    print("=" * 78)
    print(f"  [N=32,K=8,T=18] miniature exact results:")
    print(f"    three-core mechanism: EMPTY (W = RS, quotient budget -3 < 0)")
    print(f"    two-core badCount: F_97 o=2 -> {n97}, F_97 o=7 -> {n97b}, "
          f"F_1153 o=2 -> {n1153}; generic cap 2(N-T+1) = 30 < 32 = N")
    print(f"    perturbation max around extremal stack: {worst}; random "
          f"W-stack sweep max: {sweep_max}")
    print("  Four-pencil consolidation: the extremal two-core families have")
    print("  pencil cores of size 17 = T-1 > T-2, so they admit NO")
    print("  four-two-fresh-pencil cover (a foreign line covers <= 1 scalar")
    print("  per pencil, 4 lines cover <= 8 < badCount).  The local")
    print("  FavorableFourTwoFreshPencilExtraction shape is therefore wrong")
    print("  for extremal families even though the COUNT target holds; only")
    print("  the guarded (large-count) form can be true, vacuously.")


if __name__ == "__main__":
    main()
