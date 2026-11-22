"""Check constrained rank-one traces and fixed-row Paley moments over small tori."""

from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement, permutations, product
from math import factorial, prod

from probe_paley_translate_moments import trace_power


def partitions(size):
    def extend(blocks):
        if len(blocks) == size:
            yield blocks
        else:
            for block in range(max(blocks) + 2):
                yield from extend((*blocks, block))
    yield from extend((0,))


def gram_columns(matrix):
    cols = list(zip(*matrix))
    return [[sum(x * y for x, y in zip(a, b)) for b in cols] for a in cols]


def cyclic_product(gram, word):
    return prod(gram[j][word[(k + 1) % len(word)]] for k, j in enumerate(word))


def check_partitions():
    matrices = [
        ((1, 1, -1), (1, -1, 1), (-1, 1, 1)),
        ((1, 0, -1, 1), (1, -1, 0, -1), (-1, 1, -1, 0)),
        ((1, -1, 1, 1), (-1, 1, -1, -1)),
        ((1, 1, 0, 0), (0, 0, 1, 1)),
    ]
    count = 0
    negative = False
    for matrix in matrices:
        n, length = len(matrix), len(matrix[0])
        gram = gram_columns(matrix)
        trace = sum(gram[i][i] for i in range(length))
        # Exact rational Rayleigh lower bounds on the true squared norm suffice.
        lower = Fraction(0)
        for root in range(length):
            x = [int(i == root) for i in range(length)]
            for _ in range(8):
                sx = [sum(a * b for a, b in zip(row, x)) for row in gram]
                if not any(x):
                    break
                lower = max(lower, Fraction(sum(a * b for a, b in zip(x, sx)), sum(a * a for a in x)))
                x = sx
        for r in range(2, 6):
            distinct = sum(cyclic_product(gram, word) for word in permutations(range(length), r))
            negative |= distinct < 0
            reconstructed = 0
            for blocks in partitions(r):
                s = max(blocks) + 1
                constrained = sum(cyclic_product(gram, [w[b] for b in blocks])
                                  for w in product(range(length), repeat=s))
                assert abs(constrained) <= n ** (r - s) * lower ** (s - 1) * trace
                if s == r:
                    assert constrained == trace_power(matrix, r)
                mu = prod((-1) ** (k - 1) * factorial(k - 1) for k in Counter(blocks).values())
                reconstructed += mu * constrained
                count += 1
            assert reconstructed == distinct
    assert negative
    return count


def check_torus(p, delta):
    identity = (1, 0)
    group = [(a, 1) for a in range(p) if (a*a - delta) % p] + [identity]
    char = [0] + [1 if pow(z, (p - 1) // 2, p) == 1 else -1 for z in range(1, p)]
    m = len(group)
    rows = (identity, group[0], group[2], group[3])
    n, length, r = len(rows), 4, 3

    def mul(v, w):
        return ((v[0]*w[0] + delta*v[1]*w[1]) % p, (v[0]*w[1] + v[1]*w[0]) % p)

    def canonical(v):
        return (v[0] * pow(v[1], -1, p) % p, 1) if v[1] else identity

    def bracket(v, w):
        return char[(v[0]*w[1] - v[1]*w[0]) % p]

    profiles = Counter()
    for row in product(range(n), repeat=r):
        for col in permutations(range(length), r):
            cells = Counter((row[(k + t) % r], col[k]) for k in range(r) for t in (0, 1))
            odd = [(i, j) for (i, j), multiplicity in cells.items() if multiplicity % 2]
            assert (not odd) == (len(set(row)) == 1)
            slopes = Counter(-j for i, j in odd)
            assert all(marks == 2 for marks in slopes.values())
            for sign in (-1, 1):
                assert all(sum(marks * min(h, sign*d) for d, marks in slopes.items()) % 2 == 0
                           for h in range(-length, length + 1))
            profiles[tuple(sorted(cells.items()))] += 1

    window_count = 0
    aggregate = Counter()
    for g in group:
        powers = [identity]
        for _ in range(m):
            powers.append(mul(powers[-1], g))
        order = next(i for i in range(1, m + 1) if powers[i][1] == 0)
        norm = (g[0] ** 2 - delta * g[1] ** 2) % p
        inverse = (g[0] * pow(norm, -1, p) % p, -g[1] * pow(norm, -1, p) % p)
        inverse_powers = [identity]
        for _ in range(1, length):
            inverse_powers.append(mul(inverse_powers[-1], inverse))
        traces = {}
        for c in group:
            matrix = [[bracket(u, mul(c, powers[j])) for j in range(length)] for u in rows]
            gram = gram_columns(matrix)
            traces[c] = trace_power(matrix, r)
            cells = {(i, j): bracket(mul(inverse_powers[j], rows[i]), c)
                     for i in range(n) for j in range(length)}
            assert all(matrix[i][j] == char[norm] ** j * cells[i, j] for i, j in cells)
            distinct = 0
            for key, count in profiles.items():
                val = prod(cells[cell] ** k for cell, k in key)
                aggregate[key] += val
                distinct += count * val
            assert distinct == sum(cyclic_product(gram, word) for word in permutations(range(length), r))
        if order == m:
            for h in (length, m - 1, m):
                starts = range(1 - length, h)
                assert all(sum(a <= j < a + length for a in starts) == length for j in range(h))
                for offset in range(m):
                    actual = sum(traces[canonical(powers[(offset + a) % m])] for a in starts)
                    assert actual <= 2 * sum(traces.values())
                    window_count += 1

    even = [k for k in profiles if all(multiplicity % 2 == 0 for _, multiplicity in k)]
    assert sum(profiles[k] for k in even) == n * len(tuple(permutations(range(length), r)))
    assert all(0 <= aggregate[k] <= m ** 2 for k in even)
    return len(profiles), window_count


def check_adaptive_rows(p):
    length, r = 3, 2
    character = [0] + [1 if pow(y, (p - 1) // 2, p) == 1 else -1 for y in range(1, p)]
    polys = Counter()
    for exponents in combinations_with_replacement(range(length), 2*r):
        mult = Counter(exponents)
        polys[tuple(sorted(mult.items()))] = factorial(2*r) // prod(factorial(k) for k in mult.values())
    assert sum(polys.values()) == length ** (2*r)
    assert any(sum(j*k for j, k in key) % 2 for key in polys)  # odd degree at infinity
    cases = 0
    for g in range(1, p):
        orbit = [pow(g, j, p) for j in range(p-1)]
        rows = [[character[(x-z) % p] for z in orbit[:length]] for x in range(p)]
        moment = sum(sum(row) ** (2*r) for row in rows)
        expanded = sum(weight * sum(prod(row[j] ** k for j, k in key) for row in rows)
                       for key, weight in polys.items())
        assert moment == expanded
        if len(set(orbit)) != p-1:
            continue
        for b in range(1, p):
            sums = [0] * p
            for h, z in enumerate(orbit, 1):
                sums = [s + character[(x-b*z) % p] for x, s in enumerate(sums)]
                if h == length:
                    assert sums == [character[b] * sum(rows[x * pow(b, -1, p) % p]) for x in range(p)]
                blocks, tail = divmod(h, length)
                total = 0
                # Best post hoc row signs and best a distinct rows, including x=0.
                for a, score in enumerate(sorted(map(abs, sums), reverse=True), 1):
                    total += score
                    excess = max(0, total - a*tail)
                    assert excess ** (2*r) <= blocks ** (2*r) * a ** (2*r - 1) * moment
                    cases += 1
    return cases


def check_phase_sampling():
    # Evaluate the Laurent-polynomial interpolation identity exactly at roots
    # strictly between the mesh points, using a finite field of good characteristic.
    q, length = 193, 4
    grid = 4 * length
    root = next(z for z in range(2, q) if pow(z, grid, q) == q - 1 and pow(z, 2 * grid, q) == 1)
    mesh = [pow(root, 2*k, q) for k in range(grid)]

    def fejer(z, a):
        return (sum(pow(z, k, q) for k in range(a)) * sum(pow(z, -k, q) for k in range(a))
                * pow(a, -1, q)) % q

    for j in range(length):
        for k in range(2 * grid):
            z = pow(root, k, q)
            sample = 0
            for w in mesh:
                ratio = z * pow(w, -1, q) % q
                kernel = (3 * fejer(ratio, 3 * length) - fejer(ratio, length)) * pow(2, -1, q)
                sample += pow(w, j, q) * kernel
            assert sample * pow(grid, -1, q) % q == pow(z, j, q)
    return 2 * grid * length


def check_phase_rows(p):
    length, r = 4, 2
    units = ((1, 0), (0, 1), (-1, 0), (0, -1))
    character = [0] + [1 if pow(z, (p - 1) // 2, p) == 1 else -1 for z in range(1, p)]

    def phase_sum(row, phase, first=0):
        return tuple(sum(a * units[(phase * j) % 4][i] for j, a in enumerate(row, first))
                     for i in (0, 1))

    def abs2(z):
        return z[0] ** 2 + z[1] ** 2

    cases = 0
    for g in range(1, p):
        orbit = [pow(g, j, p) for j in range(p-1)]
        rows = [[character[(x - z) % p] for z in orbit[:length]] for x in range(p)]
        for phase in range(4):
            block = [phase_sum(row, phase) for row in rows]
            moment = sum(abs2(z) ** r for z in block)
            expanded = [0, 0]
            for js in product(range(length), repeat=2*r):
                weight = units[phase * (sum(js[:r]) - sum(js[r:])) % 4]
                term = sum(prod(row[j] for j in js) for row in rows)
                for k in (0, 1):
                    expanded[k] += weight[k] * term
            assert expanded == [moment, 0]
            if len(set(orbit)) != p - 1:
                continue
            for b in range(1, p):
                for h in (length, p-2, p-1):
                    blocks, tail = divmod(h, length)
                    full = blocks * length
                    vectors = []
                    for x in range(p):
                        row = [character[(x - b*z) % p] for z in orbit[:h]]
                        short = phase_sum(row[:length], phase)
                        assert short == tuple(character[b] * v for v in block[x * pow(b, -1, p) % p])
                        z = phase_sum(row[:full], phase)
                        wall = phase_sum(row[full:], phase, full)
                        assert abs2(wall) <= tail ** 2
                        vectors.append((z, (z[0] + wall[0], z[1] + wall[1])))
                    ordered = sorted(vectors, key=lambda pair: abs2(pair[1]), reverse=True)
                    real = imag = 0
                    for a, ((x, y), (u, v)) in enumerate(ordered, 1):
                        # Choose a post hoc Gaussian unit giving the largest real
                        # projection on the full arc, then test its full-block part.
                        c, d = max(units, key=lambda cd: cd[0]*u - cd[1]*v)
                        real += c*x - d*y
                        imag += c*y + d*x
                        assert (real*real + imag*imag) ** r <= blocks ** (2*r) * a ** (2*r-1) * moment
                        cases += 1
    return cases


def main():
    partition_checks = check_partitions()
    sample_checks = check_phase_sampling()
    profile_count = window_count = row_checks = phase_checks = 0
    for p in (11, 13, 17):
        row_checks += check_adaptive_rows(p)
        phase_checks += check_phase_rows(p)
        nonsquare = next(z for z in range(2, p) if pow(z, (p - 1) // 2, p) == p - 1)
        for delta in (1, nonsquare):
            profiles, windows = check_torus(p, delta)
            profile_count += profiles
            window_count += windows
    print(f"{partition_checks} constrained trace bounds, {profile_count} cell profiles "
          f"across six tori, {window_count} generator/start/window checks, "
          f"{row_checks} adaptive affine-row checks, {phase_checks} complex-phase row checks, "
          f"{sample_checks} interpolation checks")


if __name__ == "__main__":
    main()
