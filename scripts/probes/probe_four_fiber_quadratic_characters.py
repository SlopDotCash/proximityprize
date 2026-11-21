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


def check_double(p, n, ordinary, extra, private, alpha, scale, exceptional):
    """Check all three polynomial square roots of the doubled section over the base field."""
    f0, f1, _, g0, g1, _ = extra
    u0, u1, _, _ = private

    def trim(coeff):
        while coeff and coeff[-1] == 0:
            coeff.pop()
        return coeff

    def mul(*factors):
        out = [1]
        for factor in factors:
            new = [0] * (len(out) + len(factor) - 1)
            for j, a in enumerate(out):
                for k, b in enumerate(factor):
                    new[j+k] = (new[j+k] + a*b) % p
            out = trim(new)
        return out

    def sub(f, g):
        return trim([((f[i] if i < len(f) else 0) - (g[i] if i < len(g) else 0)) % p
                     for i in range(max(len(f), len(g)))])

    def nod(sites):
        return mul(*([(-s) % p, 1] for s in sorted(sites)))

    def div(f, g):
        rem = f.copy()
        out = [0] * (len(f) - len(g) + 1)
        while len(rem) >= len(g):
            j = len(rem) - len(g)
            out[j] = rem[-1] * pow(g[-1], -1, p) % p
            rem = sub(rem, [0]*j + mul([out[j]], g))
        assert not rem, "the doubled coordinate has a finite pole"
        return trim(out)

    def is_square(f):
        if not f:
            return True
        if (len(f)-1) % 2:
            return False
        top = next((v for v in range(p) if v*v % p == f[-1]), None)
        if top is None:
            return False
        h = (len(f)-1) // 2
        q = [0]*h + [top]
        for j in reversed(range(h)):
            old_square = mul(q, q)
            q[j] = (f[h+j]-old_square[h+j]) * pow(2*top, -1, p) % p
        return mul(q, q) == f

    A = mul([alpha], nod(u0 | f0))
    B = nod(u1 | f1)
    r = mul([scale], nod(f0 | g1))
    s = nod(f1 | g0)
    # Leading constant of F(F-1)(F-R), including its square class.
    d = mul([alpha*(alpha-1)*(alpha-scale) % p], nod(ordinary | exceptional))
    dr = div(mul(d, r), s)
    num = sub(mul(A,A,s), mul(r,B,B))
    den = mul([4], B, s, A, sub(A,B), sub(mul(A,s),mul(r,B)))
    doubled = div(mul(d,num,num), den)
    assert len(doubled) <= len(d) <= n and all(is_square(q)
        for q in (doubled, sub(doubled,d), sub(doubled,dr)))


def census(p, domain, shape, marked):
    """Count all balanced partitions for one marked exceptional configuration."""
    domain = set(domain)
    if shape == "complete":
        a, b, c, d, e, f, z, w = marked
        extra = ({b}, {d}, {f}, {a}, {c}, {f})
    elif shape == "missing":
        a, b, c, d, e, z = marked
        extra = ({b}, {d}, set(), {a}, {c}, set())
    elif shape == "triple":
        c, d, e, t, z = marked
        extra = (set(), {d}, set(), set(), {c}, set())
    else:
        raise ValueError("unknown overlap shape")
    assert len(set(marked)) == len(marked) and set(marked) <= domain
    pool = domain.difference(marked)
    ordered = sorted(pool)
    f0, f1, f2, g0, g1, g3 = extra
    degree = len(domain) // 4 - 1
    sizes = (degree-len(f0), degree-len(f1), degree-len(f2), degree-len(g3))
    assert sum(sizes) == len(pool)

    def ratio(top, bottom, v):
        return root(top, v, p) * pow(root(bottom, v, p), -1, p) % p

    def raw_r(v):
        return ratio(f0 | g1, f1 | g0, v)

    scale = pow(raw_r(e), -1, p)
    assert all(raw_r(s) * scale % p == 1 for s in f2 & g3)
    rval = {v: raw_r(v) * scale % p for v in pool}
    # Exceptional valuations of F(F-1)(F-R), including possible poles.
    exponents = {v: 2*int(v in f0) + int(v in f2) + int(v in g3)
                 - 3*int(v in f1) - int(v in g0) for v in marked}
    exceptional = {v for v in marked if exponents[v] % 2}
    xextra = exceptional ^ f0 ^ f1
    yextra = exceptional ^ f2 ^ f1
    dset = pool | exceptional

    fourth = next(i for i in range(2, p) if i * i % p == p - 1)
    symbols = {pow(fourth, j, p): j for j in range(4)}

    def quartic(v):
        return symbols[pow(v % p, (p - 1) // 4, p)]

    data = {}
    for v in pool:
        unit = root(pool - {v}, v, p) * prod((v-s)**(v0 % 4) for s, v0 in exponents.items())
        data[v] = (
            sum(charbit(v-u, p) << j for j, u in enumerate(ordered) if v != u),
            charbit(root(dset - {v}, v, p), p),
            charbit(root(xextra, v, p), p), charbit(root(yextra, v, p), p),
            quartic(unit), quartic(rval[v]),
            quartic(1-rval[v]) if rval[v] != 1 else 0,
        )

    passing = [0, 0]
    quartic_passes = exact = total = 0
    eta = quartic(-1)
    for u0 in combinations(ordered, sizes[0]):
        s0 = set(u0)
        for u1 in combinations(sorted(pool-s0), sizes[1]):
            s1 = set(u1)
            for u2 in combinations(sorted(pool-s0-s1), sizes[2]):
                s2 = set(u2)
                s3 = pool - s0 - s1 - s2
                total += 1
                xmask = sum(1 << j for j, v in enumerate(ordered) if v in (s2 | s3))
                ymask = sum(1 << j for j, v in enumerate(ordered) if v in (s0 | s3))
                accepted = [True, True]
                reference = [None, None]
                for j, v in enumerate(ordered):
                    matrix, dchar, ex, ey, _, rho, sigma = data[v]
                    x, y = (xmask >> j) & 1, (ymask >> j) & 1
                    if rval[v] == 1 and x:
                        accepted = [False, False]
                        break
                    l0 = ((matrix & xmask).bit_count() + ex) % 2
                    l1 = ((matrix & ymask).bit_count() + ey) % 2
                    for twist in (0, 1):
                        delta = dchar ^ twist
                        row = (l0 ^ (x * delta) ^ (y * (rho % 2)),
                               l1 ^ (x * (sigma % 2)) ^ (y * (delta ^ (eta % 2))))
                        if reference[twist] is None:
                            reference[twist] = row
                        accepted[twist] &= row == reference[twist]
                    if not any(accepted):
                        break
                for twist in (0, 1):
                    passing[twist] += int(accepted[twist])

                pass_fourth = False
                if any(accepted):
                    for delta0 in range(4):
                        refs = set()
                        for v in ordered:
                            q0 = quartic(ratio((s0 | f0)-{v}, (s1 | f1)-{v}, v))
                            q1 = quartic(ratio((s2 | f2)-{v}, (s1 | f1)-{v}, v))
                            _, _, _, _, d4, rho, sigma = data[v]
                            delta = d4 + delta0
                            if v in s0:
                                expected = (delta-2*eta-rho, eta)
                            elif v in s1:
                                expected = (-delta, -delta)
                            elif v in s2:
                                expected = (0, delta-sigma)
                            else:
                                expected = (rho, eta+sigma)
                            refs.add(((expected[0]-q0) % 4, (expected[1]-q1) % 4))
                            if len(refs) > 1:
                                break
                        if len(refs) == 1:
                            pass_fourth = True
                            break
                quartic_passes += int(pass_fourth)
                fvalues = {ratio(s0 | f0, s1 | f1, v) for v in (s2 | f2)}
                gvalues = {ratio(s0 | g0, s1 | g1, v) for v in (s3 | g3)}
                full = (len(fvalues) == 1 and len(gvalues) == 1
                        and next(iter(gvalues)) == scale * next(iter(fvalues)) % p)
                if full:
                    exact += 1
                    check_double(p, len(domain), pool, extra, (s0,s1,s2,s3),
                                 pow(next(iter(fvalues)), -1, p), scale, exceptional)
                    assert pass_fourth, "a genuine split configuration failed the character test"
    print(f"p={p} {shape}={marked} tested={total} quadratic={passing} quartic={quartic_passes} exact={exact}")
    return total, passing, quartic_passes, exact


def witness_controls():
    p = 17
    sites = set(range(2, 17))
    for shape, heads, center, values in (
        ("missing", ((1, {6,8,9,12,14,16}), (12, {2,3,4,9,12,14}), (14, {2,4,6,8,11,16})),
         {5:3,7:5,10:7,13:12,15:5}, [0,7,3,10]),
        ("triple", ((1, {2,3,7,10,11,14}), (2, {3,5,7,8,10,12}), (5, {2,8,11,12,14,16})),
         {4:4,6:16,9:10,13:1,15:14}, [0,15,7,13]),
    ):
        heads = ((0, set()), *heads)
        errs = [{v for v in sites if c*root(s, v, p) % p != center.get(v, 0)} for c, s in heads]
        assert all(len(s) == 5 for s in errs)
        assert set.union(*errs) == sites
        assert [c*root(s, 1, p) % p for c, s in heads] == values and len(set(values)) == 4
        freq = [sum(sum(v in s for s in errs) == i for v in sites) for i in range(5)]
        assert freq == ([0, 10, 5, 0, 0] if shape == "missing" else [0, 11, 3, 1, 0])


if __name__ == "__main__":
    production_ranks()
    for w, expected in ((5, ([0, 0], 0, 0)), (8, ([0, 1], 1, 1)), (16, ([2, 0], 0, 0))):
        assert census(17, range(1, 17), "complete", (2, 3, 6, 9, 4, 13, 1, w)) == (2520, *expected)
    assert census(17, range(1, 17), "missing", (5,13,11,3,7,1)) == (25200, [0,1], 1, 1)
    assert census(17, range(1, 17), "triple", (16,5,15,9,1)) == (92400, [1,1], 2, 2)
    witness_controls()
