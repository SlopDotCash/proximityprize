"""Test quarter-turn and two reflection families of saturated septics on the named μ64."""
from collections import Counter, defaultdict
from itertools import combinations, product
from math import prod

from probe_many_head_locator_attack import require
from probe_mu64_septic_character import PRIME, SITES


def kernels(rows, width):
    """Free columns of row reduction give a basis of the coefficient kernel."""
    rows = [list(row) for row in rows]
    pivots = []
    for column in range(width):
        start = len(pivots)
        pivot = next((i for i in range(start, len(rows)) if rows[i][column]), None)
        if pivot is None:
            continue
        rows[start], rows[pivot] = rows[pivot], rows[start]
        inverse = pow(rows[start][column], -1, PRIME)
        row = [v * inverse % PRIME for v in rows[start]]
        rows[start] = row
        for i, other in enumerate(rows):
            if i != start and other[column]:
                rows[i] = [(v - other[column] * w) % PRIME for v, w in zip(other, row)]
        pivots.append(column)
    basis = []
    for free in set(range(width)).difference(pivots):
        vector = [0] * width
        vector[free] = 1
        for i, pivot in enumerate(pivots):
            vector[pivot] = -rows[i][free] % PRIME
        basis.append(vector)
    return basis


def normalized_supports(size):
    """The adjacent support has no repeated exponent modulo 16, up to rotation."""
    for residues in combinations(range(1, 16), size - 1):
        for phases in product(range(4), repeat=size - 1):
            sites = tuple(sorted([0] + [r + 16 * t for r, t in zip(residues, phases)]))
            if all(sites <= tuple(sorted((a-b) % 64 for a in sites)) for b in sites[1:]):
                yield sites


def support_polynomial(sites):
    coefficients = [1]
    for j in sites:
        x = SITES[j]
        coefficients = ([-x * coefficients[0] % PRIME] +
                        [(a - x*b) % PRIME for a, b in zip(coefficients, coefficients[1:])] + [1])
    return coefficients


def opposite_sets(locator, available, residue, count):
    """Opposite conditions supporting a nonzero row in the given character space."""
    width = 9 - len(locator)
    def entry(i, j):
        return locator[i-j] if 0 <= i-j < len(locator) else 0
    basis = kernels([[entry(i, j) for j in range(width)] for i in (residue, residue+4)], width)
    if not basis:
        return set()
    columns = []
    for vector in basis:
        coefficients = [
            sum(entry(i, j)*v for j, v in enumerate(vector)) *
            (1 + SITES[(16*(i-residue)) % 64]) % PRIME for i in range(8)
        ]
        column = []
        for exponent in available:
            value = 0
            for c in reversed(coefficients):
                value = (value*SITES[exponent] + c) % PRIME
            column.append(value)
        columns.append(column)
    linear_rows = dict(zip(available, zip(*columns)))
    if len(columns) > 2:
        return {sites for sites in combinations(available, count)
                if len({a % 16 for a in sites}) == count and
                kernels([linear_rows[a] for a in sites], len(columns))}
    zeros, lines = [], defaultdict(list)
    for exponent, row in linear_rows.items():
        if not any(row):
            zeros.append(exponent)
        elif len(row) == 2:
            direction = row[1]*pow(row[0], -1, PRIME) % PRIME if row[0] else None
            lines[direction].append(exponent)
    groups = list(lines.values()) or [[]]
    return {tuple(sorted(sites)) for line in groups for sites in combinations(zeros + line, count)
            if len({a % 16 for a in sites}) == count}


def quarter_turn():
    for size, expected in [(4, 7280), (5, 69888), (6, 512512)]:
        tested = 0
        for support in normalized_supports(size):
            tested += 1
            used = {j % 16 for j in support}
            available = [j for j in range(32) if j % 16 not in used]
            locator = support_polynomial(support)
            first = opposite_sets(locator, available, 1, 7 - size)
            if first:
                second = opposite_sets(locator, available, 2, 7 - size)
                require(not first.intersection(second), f"surviving quarter turn at {support}")
        require(tested == expected, f"rotation representatives of size {size}")
        print(f"Adjacent degree {size}: {tested} rotation classes, zero quartets", flush=True)


def reflection_products():
    t = {j: (SITES[j]-1)*pow(SITES[j]+1, -1, PRIME) % PRIME for j in range(1, 32)}
    grouped = defaultdict(list)
    for support in combinations(t, 4):
        value = prod(t[j] for j in support) % PRIME
        grouped[min(value, PRIME-value)].append(support)
    counts = Counter()
    for group in grouped.values():
        for a, b in combinations(group, 2):
            if set(a).intersection(b):
                continue
            def paired(support, j):
                return prod((t[i]**2 - t[j]**2) % PRIME for i in support) % PRIME
            hits = sum(paired(a, j) == paired(b, j) for j in t if j not in a and j not in b)
            counts[hits] += 1
    require(counts == {0: 4074, 1: 21}, "Cayley-coordinate product census")
    print(f"Cayley-coordinate reflection: {dict(sorted(counts.items()))}", flush=True)


def reflection_traces():
    trace = {j: (SITES[j] + SITES[-j]) % PRIME for j in range(1, 32)}
    pairs = Counter()
    for j in trace:
        differences = {i: (trace[j] - trace[i]) % PRIME for i in trace if i != j}
        buckets = defaultdict(list)
        for support in combinations(differences, 4):
            value = prod(differences[i] for i in support) % PRIME
            buckets[value].append(support)
        for group in buckets.values():
            for a, b in combinations(group, 2):
                if set(a).isdisjoint(b):
                    pairs[a, b] += 1
    counts = Counter(pairs.values())
    require(counts == {1: 22136, 2: 50}, "trace-coordinate comparison census")
    print(f"Trace-coordinate reflection: {dict(sorted(counts.items()))}", flush=True)


if __name__ == "__main__":
    quarter_turn()
    reflection_products()
    reflection_traces()
