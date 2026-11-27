#!/usr/bin/env python3
"""Verify the four-head divisor counts and reconstruction at small lengths."""
from collections import Counter
from itertools import product

from probe_split_pencil_square_completions import P1, add, euclidean, gcd, mul, val

HEADS = range(4)


def partition(values):
    groups = {}
    for i, value in enumerate(values):
        groups[value] = groups.get(value, 0) | (1 << i)
    return tuple(sorted(groups.values()))


PARTITIONS = sorted({partition(v) for v in product(HEADS, repeat=4)}, key=len)


def refines(part, coarse):
    return all(any(group & big == group for big in coarse) for group in part)


def domain_root_count(poly, p, n):
    """Degree of gcd(poly, X^n-1), without constructing X^n."""
    if len(poly) <= 1:
        return 0
    power, base = (1,), (0, 1)
    exp = n
    while exp:
        if exp % 2:
            power = euclidean(mul(power, base, p), poly, p)[1]
        base = euclidean(mul(base, base, p), poly, p)[1]
        exp //= 2
    return len(gcd(poly, add(power, (1,), p, -1), p)) - 1


def divisor_profile(polys, p, n):
    assert n and (p - 1) % n == 0 and len(set(polys)) == 4
    result = {}
    for part in PARTITIONS:
        common = ()
        for group in part:
            members = [i for i in HEADS if group & (1 << i)]
            for i in members[1:]:
                diff = add(polys[members[0]], polys[i], p, -1)
                common = gcd(common, diff, p)
        count = domain_root_count(common, p, n) if common else n
        result[part] = count - sum(v for coarse, v in result.items() if refines(part, coarse))
    assert min(result.values()) >= 0 and sum(result.values()) == n
    return Counter({part: v for part, v in result.items() if v})


def capacity_dp(site_types, need):
    # Keep only the best capacity for a given vector of capped core sizes.
    layers = [{(0, 0, 0, 0): (0, None, None)}]
    for part in site_types:
        layer = {}
        for state, (current, _, _) in layers[-1].items():
            for block in (0, *part):
                nxt = tuple(min(need, state[i] + bool(block & (1 << i))) for i in HEADS)
                fresh = int(len(part) > 1) if block else len(part)
                if nxt not in layer or current + fresh > layer[nxt][0]:
                    layer[nxt] = current + fresh, state, block
        layers.append(layer)
    state = (need,) * 4
    if state not in layers[-1]:
        return -1, ()
    maximum = layers[-1][state][0]
    actions = []
    for layer in reversed(layers[1:]):
        _, state, block = layer[state]
        actions.append(block)
    return maximum, tuple(reversed(actions))


def extension_fixture():
    # The sixteen nonzero base-field sites sit in F_17[i], with i² = 3.
    p = 17
    roots = ((), (8, 10, 11, 12, 13, 16), (7, 8, 9, 10, 15, 16), (6, 7, 8, 11, 12, 15))
    polys = []
    for scale, sites in zip((0, 1, 11, 5), roots):
        f = (scale,) if scale else ()
        for a in sites:
            f = mul(f, (-a, 1), p)
        polys.append(f)
    grid = list(range(1, 17))
    values = [[val(f, x, p) for f in polys] for x in grid]
    parts = [partition(v) for v in values]
    assert len(PARTITIONS) == 15 and divisor_profile(tuple(polys), p, 16) == Counter(parts)
    cap, choices = capacity_dp(parts, 10)
    assert cap > 16 and capacity_dp(parts, 11)[0] <= 16

    def plus(a, b):
        return (a % p + b % p) % p + p * ((a // p + b // p) % p)

    def negate(a):
        return (-a % p) + p * (-(a // p) % p)

    def times(a, b):
        return ((a % p) * (b % p) + 3 * (a // p) * (b // p)) % p + p * (
            ((a % p) * (b // p) + (a // p) * (b % p)) % p)

    inverse = {v: next(w for w in range(1, p*p) if times(v, w) == 1) for v in range(1, p*p)}
    scalar = {(-x) % p for x, part, choice in zip(grid, parts, choices) if choice and len(part) > 1}
    received, witnesses = {}, []
    for x, row, block in zip(grid, values, choices):
        if block:
            i = next(i for i in HEADS if block & (1 << i))
            received[x] = (x * row[i] % p, row[i])
            if len(set(row)) > 1:
                j = next(j for j in HEADS if row[j] != row[i])
                witnesses.append(((-x) % p, j, x))
        else:
            # Choosing v=i keeps all denominators away from zero.
            v = p
            for u in range(p*p):
                if u == times(x, v):
                    continue
                folds = {r: times(plus(x*r % p, negate(u)), inverse[plus(v, negate(r))]) for r in row}
                if len(set(folds.values())) == len(set(row)) and not scalar.intersection(folds.values()):
                    break
            else:
                raise AssertionError("no available fresh labels")
            received[x] = u, v
            scalar.update(folds.values())
            witnesses.extend((z, row.index(r), x) for r, z in folds.items())
    assert len(scalar) == len(witnesses) == cap
    for z, j, fresh in witnesses:
        core = [x for x, row in zip(grid, values) if received[x] == (x*row[j] % p, row[j])]
        assert len(core) >= 10 and fresh not in core
        # A joint pair of degree <= 7 is fixed by any eight core sites.
        for x in [*core[:10], fresh]:
            value = val(polys[j], x, p)
            u, v = received[x]
            assert plus(u, times(z, v)) == times(plus(x, z), value)
    print(f"Four sextics over F_17, in F_289: {cap} distinct bad labels at 5 errors; "
          "the same four heads cannot exceed 16 labels at 4 errors with cores of size 11.")


def production():
    n, d, e, mass = 2**30, 2**29 - 1, 286_331_153, 946_807_831
    t, core = n - e, n - e - 7000
    assert 48 * core - 20 * n - 30 * d == 214_412_398
    populations = [(mass - i*(e+1) + 4-i) // (5-i) for i in HEADS]
    assert populations == [189_361_567, 165_119_170, 124_715_175, 43_907_185]
    deficits = [e // (size-1) for size in populations]
    assert deficits == [1, 1, 2, 6] and n - 2*core + d == 35_805_393 < min(populations)
    assert 1 + 5*(n - 2*core + d) < mass
    gaps = [6*(5*t - sum(min(s, v) for v in deficits)) - 12*n - 20*d + 12*s for s in range(1, 8)]
    assert gaps == [10, 10, 16, 22, 28, 34, 46]
    assert 2*(n - 3*(e+1)) > e

    # Check the fourteen gcds on the first-prime septic witness before pulling back by X^(n/16).
    w = 357111556877444407914257742635116754287240874648
    assert pow(w, 8, P1) == P1 - 1
    polys = []
    for i in HEADS:
        a = pow(w, 4*i, P1)
        polys.append(mul((a**3, 0, a**2, 0, a, 0, 1),
                         ((w**5 + w**3*a**3) % P1, (a + w**2*a**2) % P1), P1))
    parts = [partition([val(f, pow(w, j, P1), P1) for f in polys]) for j in range(16)]
    assert divisor_profile(tuple(polys), P1, 16) == Counter(parts)
    fiber = n // 16
    q = (fiber - 4) // 6
    common_roots = {3: q-1, 7: 4*q+3, 11: q}
    cores = [sum(common_roots.values())] * 4
    capacity = 0
    for j, part in enumerate(parts):
        remaining = fiber - common_roots.get(j, 0)
        if j == 7:
            capacity += len(part) * remaining
            continue
        largest = max(b.bit_count() for b in part)
        blocks = [b for b in part if b.bit_count() == largest]
        assert remaining % len(blocks) == 0
        for b in blocks:
            for i in HEADS:
                if b & (1 << i):
                    cores[i] += remaining // len(blocks)
        capacity += remaining
    assert cores == [760_567_124, 760_567_125, 760_567_124, 760_567_125]
    assert capacity == n+1 and n-min(cores)-1 == 313_174_699
    print(f"First-prime cover through {e:,} errors; minimum five-set gap {min(gaps)}. "
          f"Published septic allocation reconstructed with {capacity:,} labels.")


if __name__ == "__main__":
    extension_fixture()
    production()
