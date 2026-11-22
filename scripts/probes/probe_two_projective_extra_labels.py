#!/usr/bin/env python3
"""Reconstruct the two full heads and two extra directions on a small smooth domain."""

from math import comb, prod

from probe_mu16_quintic_fibers import multiply, norm, subtract, vanisher


CUBIC_FIBERS = ((0, 1, 8), (2, 9, 10), (3, 5, 7), (6, 9, 14), (7, 11, 13))


def certify_cubics():
    """Check both pencil identities coefficientwise modulo Y^8+1."""
    w, q, q_cross, v, v_cross = map(vanisher, CUBIC_FIBERS)
    for split, cross in ((q, q_cross), (v, v_cross)):
        num = subtract(w[0], cross[0])
        den = subtract(split[0], cross[0])
        assert (norm(num), norm(den), norm(subtract(den, num))) == (4, 4, 16)
        for a, b, c in zip(w, split, cross):
            assert multiply(den, subtract(a, c)) == multiply(num, subtract(b, c))


def verify(errors, geometry):
    p, n, k = 65537, 256, 16
    g = pow(3, (p - 1) // n, p)
    domain = [pow(g, j, p) for j in range(n)]
    assert len(set(domain)) == n
    t = n - errors

    def div(numerator, denominator):
        return numerator * pow(denominator, -1, p) % p

    if geometry == "linear":
        s = k // 2
        quotient = [pow(x, s, p) for x in domain]
        a, b, c, d = quotient[:4]
        scale = div(c - a, c - b)
        eta = div(d - a, scale * (d - b))
        raw_w = [(x - a) % p for x in quotient]
        raw_q = [scale * (x - b) % p for x in quotient]
        raw_v = [eta * y % p for y in raw_q]
        r = k - 2 - s
    else:
        s = k // 4
        quotient = [pow(x, s, p) for x in domain]
        root = pow(g, n // 16, p)
        def evaluate(triple, value):
            return prod(value - pow(root, i, p) for i in triple) % p
        w0, q0, qc, v0, vc = CUBIC_FIBERS
        raw_w = [evaluate(w0, x) for x in quotient]
        raw_q, raw_v = [], []
        for target, triple, cross in ((raw_q, q0, qc), (raw_v, v0, vc)):
            num = evaluate(w0, 0) - evaluate(cross, 0)
            den = evaluate(triple, 0) - evaluate(cross, 0)
            scale = div(num, den)
            target.extend(scale * evaluate(triple, x) % p for x in quotient)
        r = k - 2 - 3 * s

    sites = set(range(n))
    w_zero = {i for i in sites if raw_w[i] == 0}
    q_zero = {i for i in sites if raw_q[i] == 0}
    v_zero = {i for i in sites if raw_v[i] == 0}
    q_cross = {i for i in sites if raw_q[i] == raw_w[i]}
    v_cross = {i for i in sites if raw_v[i] == raw_w[i]}
    shared = {i for i in sites if raw_v[i] == raw_q[i]}
    first, second = q_zero | v_zero, q_cross | v_cross
    first |= shared - (w_zero | first | second)
    assert first.isdisjoint(second) and w_zero.isdisjoint(first | second)
    ordinary = sorted(sites - (w_zero | first | second))
    pad = set(ordinary[:r])
    core_a, core_b = pad | w_zero | first, pad | w_zero | second
    remaining = ordinary[r:]
    cut = t - 1 - len(core_a)
    assert cut >= 0 and len(core_b) <= t - 1
    core_a |= set(remaining[:cut])
    core_b |= set(remaining[cut:cut + t - 1 - len(core_b)])
    outside = sites - (core_a | core_b)
    assert len(core_a) == len(core_b) == t - 1
    locator = [prod(x - domain[j] for j in pad) % p for x in domain]
    w, q, exterior_v = ([h * y % p for h, y in zip(locator, row)]
                        for row in (raw_w, raw_q, raw_v))
    u = [0 if i in core_a else w[i] if i in core_b else q[i] for i in range(n)]
    keys = []
    for j, core in enumerate((core_a, core_b)):
        for i in sorted(set(range(n)) - core):
            den = w[i] if j else 0
            slope = div(exterior_v[i] - den, q[i] - den) if i in outside else 1
            assert slope
            keys.append((j, i, slope))
    assert comb(len(keys) + 1, 2) < p
    for theta in range(p):
        alpha = [(domain[i] + theta) * slope % p for _, i, slope in keys]
        if len(set(alpha) | {0}) == 1 + len(alpha):
            break
    else:
        raise AssertionError("no separating theta")
    v = [(x + theta) * (exterior_v[i] if i in outside else u[i]) % p for i, x in enumerate(domain)]
    head0, head1 = [0] * n, [(x + theta) * w[i] % p for i, x in enumerate(domain)]
    labels = set()
    for (j, i, _), value in zip(keys, alpha):
        z = div(-1, value)
        head_u, head_v, core = (w, head1, core_b) if j else (head0, head0, core_a)
        for site in core | {i}:
            assert (u[site] - head_u[site] + z * (v[site] - head_v[site])) % p == 0
        assert u[i] != head_u[i] and len(core) >= k
        labels.add(z)
    extra_q = [(x + theta) * exterior_v[i] % p for i, x in enumerate(domain)]
    zero = outside | pad | q_zero | q_cross
    vertical = outside | pad | v_zero | v_cross
    assert len(outside) >= k and min(len(zero), len(vertical)) >= t
    assert all(u[i] == q[i] for i in zero) and any(v[i] != extra_q[i] for i in zero)
    assert all(v[i] == extra_q[i] for i in vertical) and any(u[i] != q[i] for i in vertical)
    labels.add(0)
    pole = next(z for z in range(p) if z not in labels)
    finite = {0} | {div(1, z - pole) for z in labels}
    assert len(finite) == 2 * (errors + 1) + 2
    print(f"{geometry} e={errors}, t={t}, theta={theta}, extra support sizes {len(zero)},{len(vertical)}, "
          f"{len(finite)} distinct finite bad labels")


if __name__ == "__main__":
    certify_cubics()
    for e in (158, 159):
        verify(e, "linear")
    for e in (157, 158, 159):
        verify(e, "cubic")
    n, k = 2**30, 2**26
    first = n - (n + 2 * k + k // 2 - 2) // 3
    last = 5 * n // 8 - 1
    assert (first, last) == (659903830, 671088639)
    print(f"production errors {first}..{last}, odd budgets {2 * first + 3}..{2 * last + 3}")
    cubic_first = n - (n + 11 * (k // 4) - 2) // 3
    assert cubic_first == 654311425 and last - cubic_first + 1 == 16777215
    print(f"cubic errors {cubic_first}..{last}, odd budgets {2 * cubic_first + 3}..{2 * last + 3}")
