"""Exact two-parameter Paley trace, branch-chain and window controls."""

from collections import Counter
from itertools import product
from math import gcd, prod

from probe_paley_translate_moments import trace_power


def resolution_counts(gaps):
    """Count geometric blowups and odd components of the displayed resolution."""
    branch = len(gaps)
    blowups = 0
    for distances in (gaps, [-d for d in gaps]):
        low, high = min(0, *distances), max(0, *distances)
        levels = range(low, high + 1)
        blowups += high - low
        odd = {j for j in levels if sum(min(j, d) for d in distances) % 2}
        branch += len(odd)
        # A section with d=j meets the jth line at slope one, off both nodes.
        for j in levels:
            incident = int(j in distances) + int(j - 1 in odd) + int(j + 1 in odd)
            if j not in odd:
                assert incident in (0, 2)
        blowups += sum(j in distances for j in odd) + sum(j + 1 in odd for j in odd)
    # At t of order e, two sections coincide exactly when their gaps agree mod e.
    for e in range(1, max(gaps) - min(gaps) + 1):
        roots = sum(gcd(a, e) == 1 for a in range(1, e + 1))
        for size in Counter(d % e for d in gaps).values():
            if size >= 2:
                blowups += roots
                if size % 2:
                    branch += roots
                    blowups += size * roots
    b2 = 2 * (4 + blowups) - 2 * branch - 2
    assert b2 >= 0
    return blowups, b2


def check(p, delta, length, moment):
    char = [0] + [1 if pow(t, (p - 1) // 2, p) == 1 else -1 for t in range(1, p)]
    group = [(a, 1) for a in range(p) if (a * a - delta) % p] + [(1, 0)]
    identity = (1, 0)
    m = len(group)
    assert 2 * length < p and m == p - char[delta]

    def mul(v, w):
        a, b = v
        c, d = w
        return ((a * c + delta * b * d) % p, (a * d + b * c) % p)

    def det(v, w):
        return (v[0] * w[1] - v[1] * w[0]) % p

    def canonical(v):
        a, b = v
        return (a * pow(b, -1, p) % p, 1) if b else identity

    multiplicities = Counter()
    for rows in product(range(length), repeat=moment):
        for cols in product(range(length), repeat=moment):
            gaps = [rows[(i + j) % moment] - cols[i] for i in range(moment) for j in (0, 1)]
            multiplicities[tuple(sorted(Counter(gaps).items()))] += 1
    sums = {key: 0 for key in multiplicities}
    traces = {}
    all_gaps = range(1 - length, length)
    powers = {}
    orders = {}
    for g in group:
        orbit = [identity]
        for _ in range(m):
            orbit.append(mul(orbit[-1], g))
        order = next(i for i in range(1, m + 1) if orbit[i][1] == 0)
        orders[g] = order
        powers[g] = [canonical(v) for v in orbit]
        # Keep actual inverse powers, including their scalar, to check the sign.
        norm = (g[0] ** 2 - delta * g[1] ** 2) % p
        inv = (g[0] * pow(norm, -1, p) % p, -g[1] * pow(norm, -1, p) % p)
        signed_powers = {i: orbit[i] for i in range(length)}
        for i in range(1, length):
            signed_powers[-i] = mul(signed_powers[1 - i], inv)
        for c in group:
            gap_sign = {d: char[det(signed_powers[d], c)] for d in all_gaps}
            mat = [[char[det(orbit[i], mul(c, orbit[j]))]
                    for j in range(length)] for i in range(length)]
            assert all(mat[i][j] == char[norm] ** j * gap_sign[i-j]
                       for i in range(length) for j in range(length))
            trace = trace_power(mat, moment)
            from_gaps = 0
            for key, walks in multiplicities.items():
                value = prod(gap_sign[d] ** k for d, k in key)
                sums[key] += value
                from_gaps += walks * value
            assert trace == from_gaps >= 0
            traces[g, c] = trace

    paired = 0
    nonpaired = 0
    for key, walks in multiplicities.items():
        odd = [d for d, k in key if k % 2]
        if not odd:
            paired += walks
            assert 0 <= sums[key] <= m ** 2
            continue
        nonpaired += 1
        assert len(odd) >= 2 and len(odd) % 2 == sum(odd) % 2 == 0
        blowups, b2 = resolution_counts(odd)
        # A coarse explicit bound on the line and exceptional corrections.
        assert abs(sums[key]) <= (b2 + 5 * blowups + 10 * moment + 25) * (p + 1)
    assert paired <= prod(range(1, 2 * moment, 2)) * length ** (moment + 1)
    assert sum(traces.values()) == sum(sums[k] * v for k, v in multiplicities.items())

    # Count the labels using integer starts even when two starts agree in the torus.
    windows = 0
    for h in (length, m // 2, m - 1, m):
        starts = range(1 - length, h)
        reps = [[(j - i, i) for i in range(length) if j - i in starts] for j in range(h)]
        assert all(len(rs) == length and all(a + i == j for a, i in rs)
                   for j, rs in enumerate(reps))
        relative = Counter((b - a) % m for a, b in product(starts, repeat=2))
        assert max(relative.values()) <= 2 * len(starts)
        for g in group:
            if orders[g] != m:
                continue
            x = powers[g]
            for offset in range(m):
                grouped = sum(weight * traces[g, x[(offset + d) % m]]
                              for d, weight in relative.items())
                assert grouped <= 2 * len(starts) * sum(traces[g, c] for c in group)
                # Exact signed test of the operator inequality before the coarser sup bound.
                u = [(-1) ** (i + i // 4) for i in range(h)]
                v = [(-1) ** (i // 2) for i in range(h)]
                cut = sum(u[i] * v[j] * char[det(x[i], x[(offset + j) % m])]
                          for i, j in product(range(h), repeat=2))
                assert (cut * length) ** (2 * moment) <= (
                    h ** (2 * moment) * len(starts) ** (2 * moment - 2) * grouped)
                windows += 1
    return nonpaired, windows


def main():
    both = starts = 0
    for p in (7, 11, 17, 23):
        nonsquare = next(a for a in range(2, p) if pow(a, (p - 1) // 2, p) == p - 1)
        for delta in (1, nonsquare):
            for r in (2, 3):
                cases, windows = check(p, delta, 3, r)
                both += cases
                starts += windows
    print(f"16 torus/moment cases, {both} nonpaired signed-gap profiles, "
          f"{starts} generator/start/window tests")


if __name__ == "__main__":
    main()
