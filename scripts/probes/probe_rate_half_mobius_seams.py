#!/usr/bin/env python3
"""Exact finite checks for the first-prime three-line construction at floor(n/3).

The production collision count uses the Stepanov argument in the companion note.
At small lengths this probe instead enumerates every group element, constructs
both received words and checks every claimed mixed-word witness on its core.
"""

from itertools import combinations

P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478
N = 2**30
PAIR_EXPONENTS = ((0, 1), (3, 6), (10, 15))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def cross(u, v):
    return tuple((u[(i + 1) % 3] * v[(i + 2) % 3] -
                  u[(i + 2) % 3] * v[(i + 1) % 3]) % P for i in range(3))


def determinant(m):
    a, b, c, d = m
    return (a*d - b*c) % P


def transform(m, x):
    a, b, c, d = m
    if (c*x+d) % P == 0:
        return None
    return (a*x+b) * pow(c*x+d, -1, P) % P


def relative(v, w):
    """A projective representative of w^{-1} v."""
    a, b, c, d = v
    e, f, h, j = w
    return tuple(z % P for z in (j*a-f*c, j*b-f*d, e*c-h*a, e*d-h*b))


def seam_data(n):
    b, remainder = divmod(n - 4, 6)
    require(remainder == 0 and N % n == 0, 'unsupported length')
    g = pow(G, N // n, P)
    require(pow(g, n, P) == 1 and pow(g, n // 2, P) != 1, 'generator order')
    roots = [tuple(pow(g, i, P) for i in exps) for exps in PAIR_EXPONENTS]
    require(len({x for pair in roots for x in pair}) == 6, 'six distinct roots')
    polys = [(u*v % P, (-u-v) % P, 1) for u,v in roots]
    cols = [cross(polys[(i+1) % 3], polys[(i+2) % 3]) for i in range(3)]
    require(sum(a*v for a,v in zip(polys[0], cols[0])) % P, 'quadratic basis')
    maps = [(-r % P, s, -s % P, t) for r,s,t in cols]
    require(all(determinant(m) for m in maps), 'singular individual map')
    for i,j in combinations(range(3), 2):
        require(all(relative(maps[i], maps[j])), 'relative map must have four nonzero coefficients')
    seam_labels = set()
    for i,pair in enumerate(roots):
        for x in pair:
            y = transform(maps[(i+1) % 3], x)
            require(y is not None and y == transform(maps[(i+2) % 3], x), 'seam direction')
            seam_labels.add(y)
    require(len(seam_labels) == 6, 'seam label collision')
    return b, g, roots, polys, maps, seam_labels


def production():
    b, _, _, _, _, _ = seam_data(N)
    k = N // 2
    A, B, C, D = 4096, 64, 64, 2048
    require(A <= N and A*B <= N and A-1+(B-1)*N < P and D < P, 'independence or derivative range')
    require(A*B*C > D*A+D*(D-1), 'auxiliary dimension')
    collision_cap = (A-1 + N*(B+C-2)) // D
    available = N - 6*collision_cap - 6 - 18 - 3
    require(available >= 3*b, 'insufficient ordinary coordinates')
    common = N - 6 - 3*b
    core = common + 4 + b
    errors = N - core - 1
    slots = 3*(N-core)
    require(common+3 < k <= core and errors == N//3, 'degree or witness size')
    require(slots == N+2 and slots * 2**128 > P, 'mass below prize tolerance')
    return (f'n={N} per-pair bound={collision_cap} ordinary available >= {available} '
            f'ordinary needed={3*b} errors={errors} distinct bad scalars >= {slots}')


def exhaustive(n):
    b, g, roots, polys, maps, seam_labels = seam_data(n)
    domain = [pow(g, i, P) for i in range(n)]
    seam = {x for pair in roots for x in pair}
    images = [{transform(m, x) for x in domain} for m in maps]
    ordinary = []
    for x in domain:
        if x in seam:
            continue
        for i,m in enumerate(maps):
            y = transform(m, x)
            if y is None or y in seam_labels or any(y in images[j] for j in range(3) if i != j):
                break
        else:
            ordinary.append(x)
    require(len(ordinary) >= 3*b, 'short small-instance pool')
    groups = [set(ordinary[i*b:(i+1)*b]) for i in range(3)]
    common = set(domain) - seam - set.union(*groups)
    cores = [common | groups[j] | set(roots[j]) | set(roots[(j-1) % 3]) for j in range(3)]
    target = n - n//3 - 1
    require(len(common)+3 < n//2 <= target and all(len(c)==target for c in cores), 'small core sizes')
    received = {}
    heads = [{}, {}, {}]
    for x in domain:
        locator = 1
        for u in common:
            locator = locator * (x-u) % P
        diffs = []
        for (a, q, _), (s, t, v, w) in zip(polys, maps):
            h = locator * (x*x+q*x+a) % P
            diffs.append((h*(s*x+t) % P, h*(v*x+w) % P))
        require(all(sum(d[i] for d in diffs) % P == 0 for i in (0,1)), 'polynomial edge relation')
        heads[0][x] = (0,0)
        heads[1][x] = diffs[0]
        heads[2][x] = tuple((diffs[0][i]+diffs[1][i]) % P for i in (0,1))
        vals = {heads[j][x] for j in range(3) if x in cores[j]}
        require(len(vals)==1, 'receiver consistency')
        received[x] = vals.pop()
    labels = set()
    for j in range(3):
        require(all(heads[j][u] == received[u] for u in cores[j]), 'incorrect common agreement')
        for x in domain:
            if x in cores[j]:
                continue
            s = (received[x][0] - heads[j][x][0]) % P
            t = (received[x][1] - heads[j][x][1]) % P
            require(t != 0, 'second row must mismatch the unique polynomial fixed by the core')
            gamma = -s*pow(t, -1, P) % P
            require((s+gamma*t) % P == 0 and gamma not in labels, 'mixed agreement or label collision')
            labels.add(gamma)
    require(len(labels)==n+2, 'small label budget')
    return f'n={n} actual ordinary available={len(ordinary)} errors={n//3} distinct witness labels={len(labels)}'


if __name__ == '__main__':
    for small_length in (64, 256, 1024):
        print(exhaustive(small_length))
    print(production())
