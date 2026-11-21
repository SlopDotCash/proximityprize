#!/usr/bin/env python3
"""Reconstruct the two full heads and two extra directions on a small smooth domain."""

from math import comb, prod


def verify(errors):
    p, n, k = 65537, 256, 16
    g = pow(3, (p - 1) // n, p)
    domain = [pow(g, j, p) for j in range(n)]
    assert len(set(domain)) == n
    t, s, r = n - errors, k // 2, k // 2 - 2
    quotient = [pow(x, s, p) for x in domain]
    a, b, c, d = quotient[:4]

    def div(numerator, denominator):
        return numerator * pow(denominator, -1, p) % p

    scale = div(c - a, c - b)
    eta = div(d - a, scale * (d - b))
    blocks = [set(i for i in range(n) if quotient[i] == u) for u in (a, b, c, d)]
    ordinary = sorted(set(range(n)) - set.union(*blocks))
    pad = set(ordinary[:r])
    common = pad | blocks[0]
    core_a, core_b = common | blocks[1], common | blocks[2] | blocks[3]
    remaining = ordinary[r:]
    cut = t - 1 - len(core_a)
    core_a |= set(remaining[:cut])
    core_b |= set(remaining[cut:cut + t - 1 - len(core_b)])
    outside = set(range(n)) - (core_a | core_b)
    assert len(core_a) == len(core_b) == t - 1
    locator = [prod(x - domain[j] for j in pad) % p for x in domain]
    w = [h * (u - a) % p for h, u in zip(locator, quotient)]
    q = [h * scale * (u - b) % p for h, u in zip(locator, quotient)]
    u = [0 if i in core_a else w[i] if i in core_b else q[i] for i in range(n)]
    keys = []
    for j, core in enumerate((core_a, core_b)):
        for i in sorted(set(range(n)) - core):
            den = w[i] if j else 0
            slope = div(eta * q[i] - den, q[i] - den) if i in outside else 1
            assert slope
            keys.append((j, i, slope))
    assert comb(len(keys) + 1, 2) < p
    for theta in range(p):
        alpha = [(domain[i] + theta) * slope % p for _, i, slope in keys]
        if len(set(alpha) | {0}) == 1 + len(alpha):
            break
    else:
        raise AssertionError("no separating theta")
    v = [(x + theta) * (eta * q[i] if i in outside else u[i]) % p for i, x in enumerate(domain)]
    head0, head1 = [0] * n, [(x + theta) * w[i] % p for i, x in enumerate(domain)]
    labels = set()
    for (j, i, _), value in zip(keys, alpha):
        z = div(-1, value)
        head_u, head_v, core = (w, head1, core_b) if j else (head0, head0, core_a)
        for site in core | {i}:
            assert (u[site] - head_u[site] + z * (v[site] - head_v[site])) % p == 0
        assert u[i] != head_u[i] and len(core) >= k
        labels.add(z)
    extra_q = [(x + theta) * eta * q[i] % p for i, x in enumerate(domain)]
    zero = outside | pad | blocks[1] | blocks[2]
    vertical = outside | pad | blocks[1] | blocks[3]
    assert len(outside) >= k and min(len(zero), len(vertical)) >= t
    assert all(u[i] == q[i] for i in zero) and any(v[i] != extra_q[i] for i in zero)
    assert all(v[i] == extra_q[i] for i in vertical) and any(u[i] != q[i] for i in vertical)
    labels.add(0)
    pole = next(z for z in range(p) if z not in labels)
    finite = {0} | {div(1, z - pole) for z in labels}
    assert len(finite) == 2 * (errors + 1) + 2
    print(f"e={errors}, t={t}, theta={theta}, extra support sizes {len(zero)},{len(vertical)}, "
          f"{len(finite)} distinct finite bad labels")


if __name__ == "__main__":
    for e in (158, 159):
        verify(e)
    n, k = 2**30, 2**26
    first = n - (n + 2 * k + k // 2 - 2) // 3
    last = 5 * n // 8 - 1
    assert (first, last) == (659903830, 671088639)
    print(f"production errors {first}..{last}, odd budgets {2 * first + 3}..{2 * last + 3}")
