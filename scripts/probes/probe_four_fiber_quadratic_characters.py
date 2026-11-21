#!/usr/bin/env python3
"""Verify the production binary convolution ranks and sample four-fiber filters."""

from itertools import combinations
from math import prod


def charbit(a, p):
    residue = pow(a % p, (p - 1) // 2, p)
    if residue not in (1, p - 1):
        raise ValueError("a quadratic character input vanished")
    return int(residue != 1)


def production_ranks():
    n = 2**30
    for p, g in (
        (365375409332725729550921208179070755120141565953,
         303645430271030343624574566109998498685964493478),
        (730750818665451459101842416358141509841924915201,
         201436115152415656266926822135577208540274735310),
    ):
        assert pow(g, n // 2, p) == p - 1
        w = pow(g, n // 8, p)
        blocks = [charbit(n // 8, p)] + [charbit(1 - pow(w, j, p), p) for j in range(1, 8)]
        hasse = [sum(bit for j, bit in enumerate(blocks) if j & i == i) % 2 for i in range(8)]
        assert hasse.index(1) == 6
        print(f"p={p} Hasse={hasse} pure rank={n - 6} generator character={charbit(g, p)}")


def root(sites, x, p):
    return prod(x - s for s in sites) % p


def census(p, domain, marked):
    """Try every partition of the ordinary sites for one oriented K4 marking."""
    a, b, c, d, e, f, z, w = marked
    assert len(set(marked)) == 8 and set(marked) <= set(domain)
    pool = set(domain).difference(marked)
    assert len(pool) == 8
    ordered = sorted(pool)
    exceptional = {a, d}
    dset = pool | exceptional

    def ratio(x):
        return (x - b) * (x - c) * pow((x - a) * (x - d), -1, p) % p

    scale = pow(ratio(f), -1, p)
    assert ratio(e) * scale % p == 1
    rval = {v: (ratio(v) * scale) % p for v in pool}
    dchar = {v: charbit(root(dset - {v}, v, p), p) for v in pool}
    matrix = {
        v: sum((charbit(v - u, p) << j) for j, u in enumerate(ordered) if v != u)
        for v in pool
    }
    fourth = next(i for i in range(2, p) if i * i % p == p - 1)
    symbols = {pow(fourth, j, p): j for j in range(4)}

    def quartic(v):
        return symbols[pow(v % p, (p - 1) // 4, p)]

    # Remove the local uniformizer from the representative of F(F-1)(F-R).
    quartic_delta = {v: quartic(root(pool - {v}, v, p) * (v-b)**2 * (v-f)**2
                                 * (v-d) * (v-a)**3) for v in pool}
    pairs = combinations(ordered, 2)
    passing = [0, 0]
    quartic_passes = 0
    exact = 0
    total = 0
    for u0 in pairs:
        s0 = set(u0)
        for u1 in combinations(sorted(pool - s0), 2):
            s1 = set(u1)
            for u2 in combinations(sorted(pool - s0 - s1), 2):
                s2 = set(u2)
                s3 = pool - s0 - s1 - s2
                total += 1
                xmask = sum(1 << j for j, v in enumerate(ordered) if v in (s2 | s3))
                ymask = sum(1 << j for j, v in enumerate(ordered) if v in (s0 | s3))
                accepted = [True, True]
                reference = [None, None]
                for j, v in enumerate(ordered):
                    x = (xmask >> j) & 1
                    y = (ymask >> j) & 1
                    l0 = ((matrix[v] & xmask).bit_count() + charbit((v-a)*(v-b), p)) % 2
                    l1 = ((matrix[v] & ymask).bit_count() + charbit((v-a)*(v-f), p)) % 2
                    for twist in (0, 1):
                        delta = dchar[v] ^ twist
                        row = (l0 ^ (x * delta) ^ (y * charbit(rval[v], p)),
                               l1 ^ (x * charbit(1-rval[v], p))
                               ^ (y * (delta ^ charbit(-1, p))))
                        if reference[twist] is None:
                            reference[twist] = row
                        accepted[twist] &= (row == reference[twist])
                for twist in (0, 1):
                    passing[twist] += int(accepted[twist])

                pass_fourth = False
                if any(accepted):
                    for delta0 in range(4):
                        refs = set()
                        for v in ordered:
                            q0 = quartic(root((s0 | {b}) - {v}, v, p)) - quartic(
                                root((s1 | {d}) - {v}, v, p))
                            q1 = quartic(root((s2 | {f}) - {v}, v, p)) - quartic(
                                root((s1 | {d}) - {v}, v, p))
                            delta = quartic_delta[v] + delta0
                            eta, rho, sigma = quartic(-1), quartic(rval[v]), quartic(1-rval[v])
                            if v in s0:
                                expected = (delta-2*eta-rho, eta)
                            elif v in s1:
                                expected = (-delta, -delta)
                            elif v in s2:
                                expected = (0, delta-sigma)
                            else:
                                expected = (rho, eta+sigma)
                            refs.add(((expected[0]-q0) % 4, (expected[1]-q1) % 4))
                        if len(refs) == 1:
                            pass_fourth = True
                            break
                quartic_passes += int(pass_fourth)

                def common_ratio(top, bottom, support):
                    return len({root(top, v, p) * pow(root(bottom, v, p), -1, p) % p
                                for v in support}) == 1

                full = (common_ratio(s0 | {b}, s1 | {d}, s2 | {f})
                        and common_ratio(s0 | {a}, s1 | {c}, s3 | {f}))
                if full:
                    exact += 1
                    assert pass_fourth, "a genuine split configuration failed the character test"
    assert total == 2520
    print(f"p={p} marked={marked} tested={total} quadratic passes={passing} quartic={quartic_passes} exact={exact}")
    return passing, quartic_passes, exact


if __name__ == "__main__":
    production_ranks()
    for w, expected in ((5, ([0, 0], 0, 0)), (8, ([0, 1], 1, 1)), (16, ([2, 0], 0, 0))):
        assert census(17, range(1, 17), (2, 3, 6, 9, 4, 13, 1, w)) == expected
