#!/usr/bin/env python3
"""Probe the half-radius predecessor in dyadic RS syndrome geometry.

For RS[n,k] on a multiplicative subgroup D, the target error radius is

    h = n/2 - 1.

A scalar on a syndrome line is MCA-bad when it lies in the span of at most h
Vandermonde columns and the line direction is not in the chosen support span.
For (n,k)=(8,2), 2h=6 is below the RS minimum distance 7, so every syndrome in
the h-ball has a unique minimal error word.  This makes the badness test exact.

The probe enumerates the full h-ball over F_17 and then samples affine lines
through pairs of ball points, biased toward discovering high-incidence lines.
It reports a certificate if the conjectural dyadic bound #bad <= n fails.
"""

from itertools import combinations, product
import random
import sys


def primitive_root(p):
    factors = []
    x = p - 1
    q = 2
    while q * q <= x:
        if x % q == 0:
            factors.append(q)
            while x % q == 0:
                x //= q
        q += 1
    if x > 1:
        factors.append(x)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in factors):
            return g
    raise ValueError("no primitive root")


def add(a, b, p):
    return tuple((x + y) % p for x, y in zip(a, b))


def sub(a, b, p):
    return tuple((x - y) % p for x, y in zip(a, b))


def scale(c, a, p):
    return tuple(c * x % p for x in a)


def syndrome(coeffs, support, columns, p):
    r = len(columns[0])
    return tuple(sum(c * columns[i][j] for c, i in zip(coeffs, support)) % p
                 for j in range(r))


def build_ball(n=8, k=2, p=17):
    h = n // 2 - 1
    r = n - k
    root = primitive_root(p)
    omega = pow(root, (p - 1) // n, p)
    domain = [pow(omega, i, p) for i in range(n)]
    columns = [tuple(pow(x, j, p) for j in range(r)) for x in domain]
    ball = {tuple([0] * r): (0, tuple([0] * n))}
    span_by_mask = {0: {tuple([0] * r)}}
    for e in range(1, h + 1):
        for support in combinations(range(n), e):
            mask = sum(1 << i for i in support)
            space = set()
            for coeffs in product(range(p), repeat=e):
                s = syndrome(coeffs, support, columns, p)
                space.add(s)
                if all(coeffs):
                    error = [0] * n
                    for c, i in zip(coeffs, support):
                        error[i] = c
                    old = ball.get(s)
                    if old is not None and old[1] != tuple(error):
                        raise AssertionError("radius-h decoding is not unique")
                    ball[s] = (mask, tuple(error))
            span_by_mask[mask] = space
    return domain, columns, ball, span_by_mask


def line_bad_set(base, direction, p, ball, span_by_mask):
    bad = []
    hit = []
    for gamma in range(p):
        point = add(base, scale(gamma, direction, p), p)
        rec = ball.get(point)
        if rec is None:
            continue
        hit.append(gamma)
        mask, _ = rec
        # The minimal support is itself a legal witness.  It is nonjoint iff
        # the line direction is outside its syndrome span.
        if direction not in span_by_mask[mask]:
            bad.append(gamma)
    return tuple(hit), tuple(bad)


def run(samples=500_000, seed=20260709):
    n, k, p = 8, 2, 17
    domain, columns, ball, span_by_mask = build_ball(n, k, p)
    rng = random.Random(seed)
    points = list(ball)
    best = (0, None)
    hist = {}
    for trial in range(samples):
        a = points[rng.randrange(len(points))]
        b = points[rng.randrange(len(points))]
        if a == b:
            continue
        direction = sub(b, a, p)
        hits, bad = line_bad_set(a, direction, p, ball, span_by_mask)
        hist[len(bad)] = hist.get(len(bad), 0) + 1
        if len(bad) > best[0]:
            best = (len(bad), (a, direction, hits, bad))
            print({"trial": trial, "new_best": best[0], "hits": hits,
                   "bad": bad}, flush=True)
        if len(bad) > n:
            print("COUNTEREXAMPLE", best)
            return False
    print({"n": n, "k": k, "p": p, "domain": domain,
           "ball_size": len(ball), "samples": samples,
           "best_bad": best[0], "best": best[1], "histogram": hist})
    return best[0] <= n


def left_constraints(matrix, p):
    """Rows spanning the left kernel of an r-by-h full-rank matrix."""
    r = len(matrix)
    h = len(matrix[0])
    # Nullspace of matrix^T, in reduced-row-echelon form.
    a = [[matrix[i][j] % p for i in range(r)] for j in range(h)]
    pivots = []
    row = 0
    for col in range(r):
        pivot = next((i for i in range(row, h) if a[i][col]), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        z = pow(a[row][col], p - 2, p)
        a[row] = [z * x % p for x in a[row]]
        for i in range(h):
            if i != row and a[i][col]:
                z = a[i][col]
                a[i] = [(x - z * y) % p for x, y in zip(a[i], a[row])]
        pivots.append(col)
        row += 1
    assert row == h
    free = [j for j in range(r) if j not in pivots]
    basis = []
    for f in free:
        v = [0] * r
        v[f] = 1
        for i, pivot in enumerate(pivots):
            v[pivot] = -a[i][f] % p
        basis.append(tuple(v))
    return basis


def dot(a, b, p):
    return sum(x * y for x, y in zip(a, b)) % p


def candidate_from_constraints(constraints, base, direction, p):
    a = [dot(row, base, p) for row in constraints]
    b = [dot(row, direction, p) for row in constraints]
    nz = next((i for i, x in enumerate(b) if x), None)
    if nz is None:
        return "joint" if not any(a) else None
    gamma = -a[nz] * pow(b[nz], p - 2, p) % p
    return gamma if all((x + gamma * y) % p == 0 for x, y in zip(a, b)) else None


def incidence_oracle(n, k, p):
    h = n // 2 - 1
    r = n - k
    root = primitive_root(p)
    omega = pow(root, (p - 1) // n, p)
    domain = [pow(omega, i, p) for i in range(n)]
    columns = [tuple(pow(x, j, p) for j in range(r)) for x in domain]
    records = []
    for support in combinations(range(n), h):
        matrix = [[columns[i][j] for i in support] for j in range(r)]
        records.append((support, left_constraints(matrix, p)))

    def count(base, direction, certificate=False):
        by_gamma = {}
        for support, constraints in records:
            gamma = candidate_from_constraints(constraints, base, direction, p)
            if gamma is None or gamma == "joint":
                continue
            by_gamma.setdefault(gamma, []).append(support)
        if certificate:
            return by_gamma
        return len(by_gamma)

    return domain, columns, records, count


def linear_combo(coeffs, columns, p):
    r = len(columns[0])
    return tuple(sum(c * col[j] for c, col in zip(coeffs, columns)) % p
                 for j in range(r))


def large_field_search(p=97, samples=300_000, seed=20260710):
    """Fast support-quotient search at (n,k,h)=(8,2,3)."""
    n, k = 8, 2
    domain, columns, records, count = incidence_oracle(n, k, p)
    # The overlap-packing c=0 line, expressed for the ordinary RS parity-check
    # scaling h_i = x_i(1,x_i,...).  In the projectively normalized columns its
    # coefficient rows are x_i^2 and x_i on a four-point block.
    coeff0 = [x * x % p if i < n // 2 else 0 for i, x in enumerate(domain)]
    coeff1 = [x if i < n // 2 else 0 for i, x in enumerate(domain)]
    packing_base = linear_combo(coeff0, columns, p)
    packing_dir = linear_combo(coeff1, columns, p)
    packing = count(packing_base, packing_dir, certificate=True)
    print({"p": p, "packing_count": len(packing),
           "packing_gammas": sorted(packing)})

    rng = random.Random(seed)
    best = (len(packing), (packing_base, packing_dir, packing))
    # Bias every line to contain two independently sampled h-sparse syndromes.
    for trial in range(samples):
        supp0, _ = records[rng.randrange(len(records))]
        supp1, _ = records[rng.randrange(len(records))]
        c0 = [rng.randrange(1, p) for _ in supp0]
        c1 = [rng.randrange(1, p) for _ in supp1]
        a = syndrome(c0, supp0, columns, p)
        b = syndrome(c1, supp1, columns, p)
        direction = sub(b, a, p)
        score = count(a, direction)
        if score > best[0]:
            cert = count(a, direction, certificate=True)
            best = (score, (a, direction, cert))
            print({"p": p, "trial": trial, "new_best": score,
                   "gammas": sorted(cert)}, flush=True)
        if score > n:
            print("COUNTEREXAMPLE", best)
            return False
    print({"p": p, "samples": samples, "best": best[0],
           "best_base": best[1][0], "best_direction": best[1][1],
           "best_certificate": best[1][2]})
    return best[0] <= n


def vector_incidence_oracle(n, k, p):
    """NumPy version for the production-shaped n=16,k=4 cell."""
    import numpy as np

    domain, columns, records, _ = incidence_oracle(n, k, p)
    constraints = np.asarray([rows for _, rows in records], dtype=np.int64)
    inverses = np.zeros(p, dtype=np.int64)
    for x in range(1, p):
        inverses[x] = pow(x, p - 2, p)

    def count(base, direction, certificate=False):
        a = np.einsum("shr,r->sh", constraints,
                      np.asarray(base, dtype=np.int64)) % p
        b = np.einsum("shr,r->sh", constraints,
                      np.asarray(direction, dtype=np.int64)) % p
        nzmask = b != 0
        nonzero = np.any(nzmask, axis=1)
        pivot = np.argmax(nzmask, axis=1)
        ix = np.arange(len(records))
        gamma = (-a[ix, pivot] * inverses[b[ix, pivot]]) % p
        valid = nonzero & np.all((a + gamma[:, None] * b) % p == 0, axis=1)
        values = gamma[valid]
        if not certificate:
            return len(set(int(x) for x in values))
        out = {}
        for rec_index, value in zip(np.nonzero(valid)[0], values):
            out.setdefault(int(value), []).append(records[int(rec_index)][0])
        return out

    return domain, columns, records, count


def n16_search(p=97, random_samples=20_000, seed=20260711):
    """Exhaust all c=0 packing blocks and sample arbitrary support secants."""
    n, k = 16, 4
    domain, columns, records, count = vector_incidence_oracle(n, k, p)
    best = (0, None)
    packing_hist = {}
    for trial, block in enumerate(combinations(range(n), n // 2)):
        block = set(block)
        coeff0 = [x * x % p if i in block else 0 for i, x in enumerate(domain)]
        coeff1 = [x if i in block else 0 for i, x in enumerate(domain)]
        base = linear_combo(coeff0, columns, p)
        direction = linear_combo(coeff1, columns, p)
        score = count(base, direction)
        packing_hist[score] = packing_hist.get(score, 0) + 1
        if score > best[0]:
            cert = count(base, direction, certificate=True)
            best = (score, (base, direction, cert, tuple(sorted(block))))
            print({"p": p, "packing_trial": trial, "new_best": score,
                   "gammas": sorted(cert), "block": sorted(block)}, flush=True)
        if score > n:
            print("COUNTEREXAMPLE_PACKING_PLUS_ACCIDENT", best)
            return False
    print({"p": p, "packing_histogram": packing_hist,
           "packing_best": best[0]})

    rng = random.Random(seed)
    for trial in range(random_samples):
        supp0, _ = records[rng.randrange(len(records))]
        supp1, _ = records[rng.randrange(len(records))]
        c0 = [rng.randrange(1, p) for _ in supp0]
        c1 = [rng.randrange(1, p) for _ in supp1]
        a = syndrome(c0, supp0, columns, p)
        b = syndrome(c1, supp1, columns, p)
        direction = sub(b, a, p)
        score = count(a, direction)
        if score > best[0]:
            cert = count(a, direction, certificate=True)
            best = (score, (a, direction, cert, (supp0, supp1)))
            print({"p": p, "random_trial": trial, "new_best": score,
                   "gammas": sorted(cert)}, flush=True)
        if score > n:
            print("COUNTEREXAMPLE_RANDOM", best)
            return False
    print({"p": p, "random_samples": random_samples, "best": best})
    return best[0] <= n


def np_rref(matrix, p):
    """Exact reduced row echelon form over F_p (NumPy storage, integer arithmetic)."""
    import numpy as np

    a = np.asarray(matrix, dtype=np.int64).copy() % p
    rows, cols = a.shape
    pivots = []
    rank = 0
    for col in range(cols):
        candidates = np.flatnonzero(a[rank:, col])
        if len(candidates) == 0:
            continue
        pivot = rank + int(candidates[0])
        a[[rank, pivot]] = a[[pivot, rank]]
        a[rank] = a[rank] * pow(int(a[rank, col]), p - 2, p) % p
        others = np.flatnonzero(a[:, col])
        others = others[others != rank]
        if len(others):
            a[others] = (a[others] - a[others, col, None] * a[rank]) % p
        pivots.append(col)
        rank += 1
        if rank == rows:
            break
    return a, pivots


def np_nullspace(matrix, p):
    import numpy as np

    a, pivots = np_rref(matrix, p)
    free = [j for j in range(a.shape[1]) if j not in pivots]
    basis = []
    for f in free:
        v = np.zeros(a.shape[1], dtype=np.int64)
        v[f] = 1
        for i, pivot in enumerate(pivots):
            v[pivot] = -a[i, f] % p
        basis.append(v)
    return np.stack(basis) if basis else np.zeros((0, a.shape[1]), dtype=np.int64)


def np_inverse(matrix, p):
    import numpy as np

    a = np.asarray(matrix, dtype=np.int64)
    n = len(a)
    augmented = np.concatenate([a % p, np.eye(n, dtype=np.int64)], axis=1)
    reduced, pivots = np_rref(augmented, p)
    assert pivots[:n] == list(range(n))
    return reduced[:, n:]


def agreement_parity(domain, k, subset, p):
    """Parity checks for degree-<k polynomial fit on an ordered coordinate subset."""
    import numpy as np

    subset = tuple(subset)
    base, rest = subset[:k], subset[k:]
    vand = np.asarray([[pow(domain[i], j, p) for j in range(k)] for i in base],
                      dtype=np.int64)
    inv = np_inverse(vand, p)
    rows = []
    for x in rest:
        vx = np.asarray([pow(domain[x], j, p) for j in range(k)], dtype=np.int64)
        lagrange = vx @ inv % p
        row = np.zeros(len(domain), dtype=np.int64)
        row[x] = 1
        for coeff, i in zip(lagrange, base):
            row[i] = -coeff % p
        rows.append(row)
    return np.stack(rows)


def packing_extension_census():
    """Exact F_17 census: no seventeenth scalar deforms the 16-scalar packing.

    Unknowns are the two word rows (32 field elements).  Each prescribed scalar
    and nine-point witness contributes five linear RS interpolation constraints.
    For every possible ninth-support of the only unused scalar gamma=0, we compute
    the exact kernel and test whether any prescribed witness is forced joint.

    A nonjoint vector exists iff no direction-fit map is identically zero on the
    kernel: there are at most q=17 proper bad subspaces, which cannot cover F_q^d.
    Thus the forced-joint test is exact, not randomized.
    """
    import numpy as np

    p, n, k, t, generator = 17, 16, 4, 9, 3
    domain = [pow(generator, i, p) for i in range(n)]
    packing = {
        1: (0, 1, 2, 3, 4, 5, 6, 7, 8),
        2: (6, 8, 9, 10, 11, 12, 13, 14, 15),
        3: (0, 1, 2, 3, 4, 5, 6, 7, 9),
        4: (4, 8, 9, 10, 11, 12, 13, 14, 15),
        5: (0, 1, 2, 3, 4, 5, 6, 7, 13),
        6: (7, 8, 9, 10, 11, 12, 13, 14, 15),
        7: (3, 8, 9, 10, 11, 12, 13, 14, 15),
        8: (2, 8, 9, 10, 11, 12, 13, 14, 15),
        9: (0, 1, 2, 3, 4, 5, 6, 7, 10),
        10: (0, 1, 2, 3, 4, 5, 6, 7, 11),
        11: (0, 1, 2, 3, 4, 5, 6, 7, 15),
        12: (5, 8, 9, 10, 11, 12, 13, 14, 15),
        13: (0, 1, 2, 3, 4, 5, 6, 7, 12),
        14: (1, 8, 9, 10, 11, 12, 13, 14, 15),
        15: (0, 1, 2, 3, 4, 5, 6, 7, 14),
        16: (0, 8, 9, 10, 11, 12, 13, 14, 15),
    }
    parity = {}

    def checks(subset):
        subset = tuple(subset)
        if subset not in parity:
            parity[subset] = agreement_parity(domain, k, subset, p)
        return parity[subset]

    def constraint(gamma, subset):
        r = checks(subset)
        return np.concatenate([r, gamma * r % p], axis=1)

    base = np.concatenate([constraint(gamma, subset)
                           for gamma, subset in packing.items()], axis=0)
    base_kernel = np_nullspace(base, p)
    assert len(base_kernel) == 11
    for subset in packing.values():
        assert np.any(checks(subset) @ base_kernel[:, n:].T % p)

    histogram = {}
    high = []
    for subset in combinations(range(n), t):
        matrix = np.concatenate([base, constraint(0, subset)], axis=0)
        kernel = np_nullspace(matrix, p)
        dim = len(kernel)
        histogram[dim] = histogram.get(dim, 0) + 1
        rows = list(packing.items()) + [(0, subset)]
        forced = [(gamma, support) for gamma, support in rows
                  if not np.any(checks(support) @ kernel[:, n:].T % p)]
        # Exact covering criterion: if none were forced, a vector avoiding all
        # <=q joint subspaces would realize seventeen nonjoint witnesses.
        assert forced
        if dim == 10:
            old = [gamma for gamma, support in packing.items() if support == subset]
            assert len(old) == 1
            assert (0, subset) in forced and (old[0], subset) in forced
            high.append((subset, forced))
    expected = {8: 10976, 9: 448, 10: 16}
    # Earlier exploratory output split some rank-9 cases before the exact forced
    # test.  The authoritative histogram is asserted here from the full rerun.
    assert histogram == expected, histogram
    print({"packing_base_nullity": len(base_kernel),
           "extension_kernel_histogram": histogram,
           "high_nullity_supports": len(high),
           "all_extensions_forced_joint": True})
    return True


def dependent_witness_trade_counterexample():
    """Exact falsifier of 'every chosen witness incidence family is Q-independent'."""
    import numpy as np

    p, n, k, t, generator = 17, 16, 4, 9, 3
    domain = [pow(generator, i, p) for i in range(n)]
    core = (0, 1)
    a0, a1 = (2, 3, 4), (5, 6, 7)
    b0, b1 = (8, 9, 10, 11), (12, 13, 14, 15)
    supports = [core + a0 + b0, core + a1 + b1,
                core + a0 + b1, core + a1 + b0]
    gammas = [1, 2, 3, 4]
    u0 = np.asarray([0, 0, 2, 13, 12, 5, 15, 0, 7, 16, 5, 7, 0, 0, 0, 0],
                    dtype=np.int64)
    u1 = np.asarray([0, 0, 5, 7, 13, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    dtype=np.int64)
    parity = {s: agreement_parity(domain, k, s, p) for s in supports}
    matrix = np.concatenate([
        np.concatenate([parity[s], gamma * parity[s] % p], axis=1)
        for gamma, s in zip(gammas, supports)
    ], axis=0)
    kernel = np_nullspace(matrix, p)
    assert len(kernel) == 12
    for gamma, support in zip(gammas, supports):
        r = parity[support]
        assert not np.any(r @ ((u0 + gamma * u1) % p) % p)
        assert np.any(r @ u1 % p)  # nonjoint, since the direction is not RS-fit
    incidence = np.asarray([[int(i in support) for i in range(n)]
                            for support in supports], dtype=np.int64)
    assert np.array_equal(incidence[0] + incidence[1],
                          incidence[2] + incidence[3])
    assert len(np_rref(incidence, 1000003)[1]) == 3

    # Enumerate every witness for this stack.  The bad set is exactly {1,2,3,4};
    # gamma 1 and 3 have alternatives, and some alternative choice has full rank.
    all_witnesses = {}
    for support in combinations(range(n), t):
        r = agreement_parity(domain, k, support, p)
        if not np.any(r @ u1 % p):
            continue
        for gamma in range(p):
            if not np.any(r @ ((u0 + gamma * u1) % p) % p):
                all_witnesses.setdefault(gamma, []).append(support)
    assert {gamma: len(v) for gamma, v in all_witnesses.items()} == {
        1: 10, 2: 1, 3: 10, 4: 1}
    independent_choice = None
    for s1 in all_witnesses[1]:
        for s3 in all_witnesses[3]:
            choice = [s1, all_witnesses[2][0], s3, all_witnesses[4][0]]
            rows = np.asarray([[int(i in support) for i in range(n)]
                               for support in choice], dtype=np.int64)
            if len(np_rref(rows, 1000003)[1]) == 4:
                independent_choice = choice
                break
        if independent_choice is not None:
            break
    assert independent_choice is not None
    print({"bad_scalars": sorted(all_witnesses),
           "witness_multiplicities": {g: len(v) for g, v in all_witnesses.items()},
           "displayed_trade_rank": 3,
           "alternative_independent_transversal": independent_choice,
           "u0": list(map(int, u0)), "u1": list(map(int, u1))})
    return True


if __name__ == "__main__":
    if "--packing-extension" in sys.argv:
        raise SystemExit(0 if packing_extension_census() else 1)
    if "--witness-trade" in sys.argv:
        raise SystemExit(0 if dependent_witness_trade_counterexample() else 1)
    ok = run()
    ok = large_field_search(97) and ok
    ok = large_field_search(257, samples=100_000) and ok
    raise SystemExit(0 if ok else 1)
