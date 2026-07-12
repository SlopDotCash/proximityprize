#!/usr/bin/env python3
"""G210 exact depth-two flatness certificate (#466/#509).

For an even-order cyclic subgroup G=<g>, ordered pair sums split by exponent difference d.
The diagonal d=0 contributes one orbit (weight 1). Every non-antipodal pair {d,n-d},
1 <= d < n/2, contributes two orbits (weight 2). Its quotient-class label is

    L_d = (1 + g^d)^n mod p.

Thus the G209 partition is obtained by merging the weighted primitive labels
[(L_0,1),(L_1,2),...,(L_{n/2-1},2)]. It is the unique floor histogram [1,2,...,2]
iff these n/2 labels are pairwise distinct. A collision L_d=L_e is equivalent to
(1+g^d)/(1+g^e) in G, hence to the direct characteristic-p weighted relation

    1 + g^d = a(1 + g^e),  a in G.

This probe verifies the equivalence against direct ordered-pair enumeration and prints the
large exceptional n=32 cells identified by the referee.
"""
from collections import Counter


def factor(x):
    out = {}
    d = 2
    while d * d <= x:
        while x % d == 0:
            out[d] = out.get(d, 0) + 1
            x //= d
        d += 1
    if x > 1:
        out[x] = out.get(x, 0) + 1
    return out


def primitive_n_root(p, n):
    assert (p - 1) % n == 0
    for g in range(2, p):
        if pow(g, n, p) != 1:
            continue
        if all(pow(g, n // ell, p) != 1 for ell in factor(n)):
            return g
    raise AssertionError("no primitive root")


def direct_partition(p, n, g):
    G = [pow(g, i, p) for i in range(n)]
    rep = Counter((x + y) % p for x in G for y in G)
    classes = Counter()
    for t, multiplicity in rep.items():
        if t:
            classes[pow(t, n, p)] += multiplicity
    assert all(v % n == 0 for v in classes.values())
    return sorted((v // n for v in classes.values()), reverse=True)


def primitive_partition(p, n, g):
    m = n // 2
    atoms = [(pow(2, n, p), 1, 0)]
    atoms += [(pow((1 + pow(g, d, p)) % p, n, p), 2, d) for d in range(1, m)]
    merged = Counter()
    locations = {}
    for label, weight, d in atoms:
        merged[label] += weight
        locations.setdefault(label, []).append((d, weight))
    collisions = {label: ds for label, ds in locations.items() if len(ds) > 1}
    return sorted(merged.values(), reverse=True), atoms, collisions


def analyze(p, n):
    g = primitive_n_root(p, n)
    direct = direct_partition(p, n, g)
    primitive, atoms, collisions = primitive_partition(p, n, g)
    assert direct == primitive
    floor = 2 * n - 3
    sumsq = sum(k * k for k in direct)
    labels = [x[0] for x in atoms]
    distinct = len(set(labels)) == len(labels)
    flat_hist = (len(direct) == n // 2 and direct.count(1) == 1 and direct.count(2) == n // 2 - 1)
    floor_eq = sumsq == floor
    assert floor_eq == flat_hist == distinct == (not collisions)

    # Verify every collision gives the advertised direct weighted relation.
    Gset = {pow(g, i, p) for i in range(n)}
    relations = []
    for label, ds in collisions.items():
        for i in range(len(ds)):
            for j in range(i + 1, len(ds)):
                d, _ = ds[i]
                e, _ = ds[j]
                xd = (1 + pow(g, d, p)) % p
                xe = (1 + pow(g, e, p)) % p
                a = xd * pow(xe, p - 2, p) % p
                assert a in Gset
                assert (1 + pow(g, d, p) - a * (1 + pow(g, e, p))) % p == 0
                relations.append((d, e, a, label))
    return dict(p=p, n=n, g=g, ks=direct, sumsq=sumsq, floor=floor,
                distinct=distinct, collisions=collisions, relations=relations)


def main():
    cells = [(17, 8), (113, 8), (97, 16), (2593, 16),
             (257, 32), (3617, 32), (50177, 32), (51137, 32)]
    for p, n in cells:
        row = analyze(p, n)
        print(f"p={p:>5} n={n:>2} g={row['g']:>5} ks={row['ks']} "
              f"sumsq/floor={row['sumsq']}/{row['floor']} distinct={row['distinct']}")
        for d, e, a, label in row["relations"]:
            print(f"  collision d={d},e={e}: L={label}; a={a} in G; "
                  f"1+g^d = a(1+g^e) mod p")
    print("ALL PASS: direct census = primitive-label merge; floor iff labels are pairwise distinct")


if __name__ == "__main__":
    main()
