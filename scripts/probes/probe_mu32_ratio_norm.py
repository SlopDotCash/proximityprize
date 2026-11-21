#!/usr/bin/env python3
"""Exact upper bounds for the odd part of a cross-product norm on mu_32.

Only integer arithmetic is used. Each table weight rounds upward, including
negative weights. The dynamic program maximizes over disjoint ordered supports.
"""
from math import isqrt

N = 32
PRECISION = 40
UNIT = 1 << PRECISION
SCALE = 1024


def chord_intervals():
    """Enclose 2-2cos(pi*j/16) scaled by UNIT, through half-angle identities."""
    values = {0: (0, 0), 8: (2 * UNIT, 2 * UNIT), 16: (4 * UNIT, 4 * UNIT)}
    for step in (4, 2, 1):
        for j in range(step, 8, step * 2):
            low, high = values[2 * j]
            lo_sqrt = isqrt((4 * UNIT - high) * UNIT)
            hi_sqrt = 1 + isqrt((4 * UNIT - low) * UNIT)
            values[j] = (2 * UNIT - hi_sqrt, 2 * UNIT - lo_sqrt)
            values[16 - j] = (4 * UNIT - values[j][1], 4 * UNIT - values[j][0])
    return [values[min(j, N - j)] for j in range(N)]


def log2_chords():
    # The bit length of u-1 is ceil(log2(u)) for every positive integer u.
    return [None if j == 0 else (hi**SCALE - 1).bit_length() - PRECISION * SCALE
            for j, (_, hi) in enumerate(chord_intervals())]


def maxima(logs, y, degrees):
    largest = max(degrees)
    answers = dict.fromkeys(degrees, 0)
    for mask in range(256):  # one choice per conjugate pair of embeddings
        # Swapping the two supports exchanges the two possible 2-adic charges.
        # Complementing this embedding mask then interchanges the archimedean factors.
        weights = []
        for j in range(1, N):
            if j == y:
                continue
            a = b = 0
            for h in range(8):
                t = 2 * h + 1
                left, right = logs[t * j % N], logs[t * (j - y) % N]
                if mask & (1 << h):
                    a += left
                    b += right
                else:
                    a += right
                    b += left
            a -= (j & -j) * SCALE
            s = j - y
            b -= (s & -s) * SCALE
            weights.append((a, b))
        # A lower sentinel that cannot be reached by any valid assignment.
        table = [[-10**8] * (largest + 1) for _ in range(largest + 1)]
        table[0][0] = 0
        for a, b in weights:
            for i in range(largest, -1, -1):
                for j in range(largest, -1, -1):
                    best = table[i][j]
                    if i:
                        best = max(best, table[i - 1][j] + a)
                    if j:
                        best = max(best, table[i][j - 1] + b)
                    table[i][j] = best
        for d in degrees:
            answers[d] = max(answers[d], table[d][d] + 16 * SCALE)
    return answers


def check_list_lower():
    from math import prod

    p = (3 * 2**48 + 69) * 2**80 + 1
    if pow(5, (p - 1) // 2, p) != p - 1 or not (3 * 2**48 + 69 < 2**80):
        raise ArithmeticError("invalid Proth certificate")
    g = pow(5, (p - 1) // 32, p)
    sites = [pow(g, j, p) for j in range(32)]
    if len(set(sites)) != 32 or p // 2**128 != 3:
        raise ArithmeticError("incorrect field or subgroup")
    fibers = [pow(g, 4*j, p) for j in range(8)]
    root_sets = [(3, 6, 7), (3, 5, 7), (4, 5, 6)]
    rows = []
    # One zero in fibers 0, 1 and 4 creates a common agreement for all four heads.
    for x in sites:
        weight = prod(x - sites[i] for i in (0, 1, 4)) % p
        vals = [0]
        for roots in root_sets:
            scale = prod(fibers[2] - fibers[j] for j in roots) % p
            vals.append(weight * prod(pow(x, 4, p) - fibers[j] for j in roots)
                        * pow(scale, -1, p) % p)
        rows.append(vals)
    choose_head = (2, 1, 1, 0, 0, 0, 0, 0)
    center = [row[choose_head[j % 8]] for j, row in enumerate(rows)]
    heads = list(zip(*rows))
    agreements = [sum(v == c for v, c in zip(head, center)) for head in heads]
    if len(set(heads)) != 4 or agreements != [22, 22, 22, 24]:
        raise ArithmeticError(f"unexpected agreements {agreements}")
    print(f"F_{p}, order 32, budget 3: four distinct heads have {agreements} agreements")


def main():
    logs = log2_chords()
    degrees = (7, 8, 9)
    bounds = [maxima(logs, y, degrees) for y in (1, 2, 4, 8)]
    for d in degrees:
        row = [b[d] for b in bounds]
        print(f"d={d}, scaled upper exponents at spacings 1,2,4,8: {row} / {SCALE}")
    if max(b[d] for b in bounds for d in (7, 8)) >= 128 * SCALE:
        raise ArithmeticError("the lift to characteristics above 2^128 failed")
    if max(b[9] for b in bounds) >= 133 * SCALE:
        raise ArithmeticError("the nonic lift above 2^133 failed")


if __name__ == "__main__":
    main()
    check_list_lower()
