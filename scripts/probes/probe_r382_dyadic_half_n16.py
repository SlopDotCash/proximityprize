#!/usr/bin/env python3
"""Search exact [16,4] dyadic RS syndrome lines at the half-radius predecessor.

For each 7-support T, span(H_T) is annihilated by the five coefficient rows of
X^j prod_{x in T}(X-x), 0 <= j < 5.  A line b+gamma*d meets this span iff the two
five-vectors A_T b and A_T d are proportional.  The calculation below batches all
C(16,7)=11440 supports and samples lines through pairs of sparse syndromes.
"""

from itertools import combinations
import random
import numpy as np


P = 97
N = 16
K = 4
E = 7
D = N - K


def primitive_root(p):
    factors, x, q = [], p - 1, 2
    while q * q <= x:
        if x % q == 0:
            factors.append(q)
            while x % q == 0:
                x //= q
        q += 1
    if x > 1:
        factors.append(x)
    return next(g for g in range(2, p)
                if all(pow(g, (p - 1) // q, p) != 1 for q in factors))


def mul_linear(poly, root):
    out = [0] * (len(poly) + 1)
    for i, a in enumerate(poly):
        out[i] = (out[i] - root * a) % P
        out[i + 1] = (out[i + 1] + a) % P
    return out


def setup():
    omega = pow(primitive_root(P), (P - 1) // N, P)
    domain = [pow(omega, i, P) for i in range(N)]
    columns = np.array([[pow(x, j, P) for j in range(D)] for x in domain], dtype=np.int64)
    supports = list(combinations(range(N), E))
    annihilators = np.zeros((len(supports), D - E, D), dtype=np.int64)
    for row, support in enumerate(supports):
        z = [1]
        for i in support:
            z = mul_linear(z, domain[i])
        for shift in range(D - E):
            annihilators[row, shift, shift:shift + len(z)] = z
    return domain, columns, supports, annihilators


def random_sparse(columns, rng):
    support = rng.sample(range(N), E)
    coeffs = np.array([rng.randrange(1, P) for _ in range(E)], dtype=np.int64)
    return (coeffs @ columns[support]) % P


def nullspace(matrix):
    a = np.array(matrix, dtype=np.int64) % P
    rows, cols = a.shape
    pivots = []
    r = 0
    for c in range(cols):
        nz = np.flatnonzero(a[r:, c])
        if len(nz) == 0:
            continue
        q = r + int(nz[0])
        a[[r, q]] = a[[q, r]]
        a[r] = a[r] * pow(int(a[r, c]), P - 2, P) % P
        for i in range(rows):
            if i != r and a[i, c]:
                a[i] = (a[i] - a[i, c] * a[r]) % P
        pivots.append(c)
        r += 1
        if r == rows:
            break
    free = [c for c in range(cols) if c not in pivots]
    basis = []
    for f in free:
        v = np.zeros(cols, dtype=np.int64)
        v[f] = 1
        for i, c in enumerate(pivots):
            v[c] = -a[i, f] % P
        basis.append(v)
    return np.array(basis, dtype=np.int64)


def half_annihilator(subset, domain):
    z = [1]
    for i in subset:
        z = mul_linear(z, domain[i])
    out = np.zeros((D - len(subset), D), dtype=np.int64)
    for shift in range(D - len(subset)):
        out[shift, shift:shift + len(z)] = z
    return out


def structured_half_span_search(domain, annihilators):
    """Find a line contained in three or more 8-subset spans."""
    a = tuple(range(N // 2))
    b = tuple(range(N // 2, N))
    aa = half_annihilator(a, domain)
    ab = half_annihilator(b, domain)
    intersection = nullspace(np.vstack([aa, ab]))
    assert len(intersection) == K
    best = (0, None)
    for c in combinations(range(N), N // 2):
        ac = half_annihilator(c, domain)
        coeff_kernel = nullspace((ac @ intersection.T) % P)
        if len(coeff_kernel) < 2:
            continue
        pencil = (coeff_kernel[:2] @ intersection) % P
        hits = line_incidence(pencil[0], pencil[1], annihilators)
        if len(hits) > best[0]:
            best = (len(hits), (c, pencil.tolist(), hits, len(coeff_kernel)))
            print({"structured_best": best}, flush=True)
    return best


def constrained_four_hit_search(columns, supports, annihilators, trials=5_000, seed=383):
    """Sample pencils forced through four independently chosen support spans."""
    rng = random.Random(seed)
    best = (0, None)
    for trial in range(trials):
        chosen = rng.sample(range(len(supports)), 4)
        gammas = rng.sample(range(P), 4)
        kernel = constraint_kernel(columns, supports, chosen, gammas)
        if len(kernel) == 0:
            continue
        for vector in kernel:
            base = vector[:D]
            direction = vector[D:2 * D]
            if not np.any(direction):
                continue
            hits = line_incidence(base, direction, annihilators)
            if len(hits) > best[0]:
                best = (len(hits), (chosen, gammas, base.tolist(), direction.tolist(), hits))
                print({"four_hit_trial": trial, "four_hit_best": best}, flush=True)
            if len(hits) > N:
                return best
    return best


def line_incidence(base, direction, annihilators):
    ab = np.einsum("sed,d->se", annihilators, base) % P
    ad = np.einsum("sed,d->se", annihilators, direction) % P
    joint = np.all(ab == 0, axis=1) & np.all(ad == 0, axis=1)
    candidates = ~joint

    gamma = np.full(len(annihilators), -1, dtype=np.int64)
    for j in range(D - E):
        pivot = candidates & (ad[:, j] != 0) & (gamma < 0)
        if np.any(pivot):
            inv = np.array([pow(int(x), P - 2, P) for x in ad[pivot, j]], dtype=np.int64)
            gamma[pivot] = (-ab[pivot, j] * inv) % P
    valid = gamma >= 0
    if np.any(valid):
        valid_indices = np.flatnonzero(valid)
        g = gamma[valid_indices]
        equations = (ab[valid_indices] + g[:, None] * ad[valid_indices]) % P
        valid[valid_indices] = np.all(equations == 0, axis=1)
    return sorted(set(int(x) for x in gamma[valid]))


def incidence_witnesses(base, direction, annihilators):
    ab = np.einsum("sed,d->se", annihilators, base) % P
    ad = np.einsum("sed,d->se", annihilators, direction) % P
    joint = np.all(ab == 0, axis=1) & np.all(ad == 0, axis=1)
    gamma = np.full(len(annihilators), -1, dtype=np.int64)
    for j in range(D - E):
        pivot = ~joint & (ad[:, j] != 0) & (gamma < 0)
        if np.any(pivot):
            inv = np.array([pow(int(x), P - 2, P) for x in ad[pivot, j]], dtype=np.int64)
            gamma[pivot] = (-ab[pivot, j] * inv) % P
    valid = gamma >= 0
    indices = np.flatnonzero(valid)
    if len(indices):
        equations = (ab[indices] + gamma[indices, None] * ad[indices]) % P
        valid[indices] = np.all(equations == 0, axis=1)
    out = {}
    for support_index in np.flatnonzero(valid):
        out.setdefault(int(gamma[support_index]), []).append(int(support_index))
    return out


def constraint_kernel(columns, supports, chosen, gammas):
    m = len(chosen)
    matrix = np.zeros((m * D, 2 * D + m * E), dtype=np.int64)
    for j, (support_index, gamma) in enumerate(zip(chosen, gammas)):
        rows = slice(j * D, (j + 1) * D)
        matrix[rows, :D] = np.eye(D, dtype=np.int64)
        matrix[rows, D:2 * D] = gamma * np.eye(D, dtype=np.int64)
        matrix[rows, 2 * D + j * E:2 * D + (j + 1) * E] = \
            -columns[list(supports[support_index])].T
    return nullspace(matrix)


def seeded_component_search(columns, supports, annihilators, seed_line,
                            trials=10_000, seed=384):
    rng = random.Random(seed)
    base = np.array(seed_line[0], dtype=np.int64)
    direction = np.array(seed_line[1], dtype=np.int64)
    witnesses = incidence_witnesses(base, direction, annihilators)
    best = (len(witnesses), (base.tolist(), direction.tolist(), sorted(witnesses)))
    for trial in range(trials):
        if len(witnesses) < 4:
            break
        gammas = rng.sample(list(witnesses), 4)
        chosen = [rng.choice(witnesses[g]) for g in gammas]
        kernel = constraint_kernel(columns, supports, chosen, gammas)
        candidates = list(kernel)
        for _ in range(4):
            if len(kernel) == 0:
                break
            coeffs = np.array([rng.randrange(P) for _ in range(len(kernel))], dtype=np.int64)
            candidates.append(coeffs @ kernel % P)
        for vector in candidates:
            b = vector[:D]
            d = vector[D:2 * D]
            if not np.any(d):
                continue
            found = incidence_witnesses(b, d, annihilators)
            if len(found) > best[0]:
                best = (len(found), (b.tolist(), d.tolist(), sorted(found)))
                base, direction, witnesses = b, d, found
                print({"seeded_trial": trial, "seeded_best": best}, flush=True)
            if len(found) > N:
                return best
    return best


def run(samples=200_000, seed=382):
    domain, columns, supports, annihilators = setup()
    structured = structured_half_span_search(domain, annihilators)
    if structured[0] > N:
        print("STRUCTURED_COUNTEREXAMPLE", structured, flush=True)
        return False
    constrained = constrained_four_hit_search(columns, supports, annihilators)
    if constrained[0] > N:
        print("FOUR_HIT_COUNTEREXAMPLE", constrained, flush=True)
        return False
    rng = random.Random(seed)
    best = (0, None)
    histogram = {}
    for trial in range(samples):
        a = random_sparse(columns, rng)
        b = random_sparse(columns, rng)
        if np.array_equal(a, b):
            continue
        direction = (b - a) % P
        hits = line_incidence(a, direction, annihilators)
        histogram[len(hits)] = histogram.get(len(hits), 0) + 1
        if len(hits) > best[0]:
            best = (len(hits), (a.tolist(), direction.tolist(), hits))
            print({"trial": trial, "best": best}, flush=True)
        if len(hits) > N:
            print("COUNTEREXAMPLE", best, flush=True)
            return False
    print({"p": P, "n": N, "k": K, "e": E, "domain": domain,
           "supports": len(supports), "samples": samples,
           "best": best, "histogram": histogram})
    return best[0] <= N


if __name__ == "__main__":
    raise SystemExit(0 if run() else 1)
