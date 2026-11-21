"""Find four radius-h+1 candidates when one word is at distance h, n=4h.

For a fixed size-h support T of the received word, subtract its nearest
codeword. Every other candidate must vanish outside the union of T and a
disjoint size-(h+1) set E. Its scale is the only free coefficient.
On T these scalings agree exactly when the locator value vectors are
proportional. Rotation or inversion preserves the projective equality.
"""

from collections import Counter
from itertools import combinations
from math import prod


PRIME = (3 * 2**48 + 69) * 2**80 + 1


def buckets(domain, support):
    complement = sorted(set(range(len(domain))) - set(support))
    base = domain[support[0]]
    ratios = {
        i: tuple(
            (domain[j] - domain[i]) * pow(base - domain[i], -1, PRIME) % PRIME
            for j in support[1:]
        )
        for i in complement
    }
    result = {}
    for errors in combinations(complement, len(support) + 1):
        key = tuple(
            prod(ratios[i][k] for i in errors) % PRIME
            for k in range(len(support) - 1)
        )
        result.setdefault(key, []).append(errors)
    return result


def check_length(n):
    h = n // 4
    generator = pow(5, (PRIME - 1) // n, PRIME)
    domain = tuple(pow(generator, i, PRIME) for i in range(n))
    if len(set(domain)) != n or pow(generator, n, PRIME) != 1:
        raise AssertionError("wrong domain order")
    seen = set()
    multiplicities = Counter()
    for support in combinations(range(n), h):
        if support in seen:
            continue
        seen.update(
            tuple(sorted((a * j + b) % n for j in support))
            for a in (1, -1) for b in range(n)
        )
        classes = buckets(domain, support)
        multiplicities[max(map(len, classes.values()))] += 1
        if n == 8 and support == (0, 1):
            expected = {(2, 3, 7), (2, 5, 6), (3, 4, 5)}
            if not any(expected <= set(group) for group in classes.values()):
                raise AssertionError("length-eight witness")
    if n == 16 and multiplicities != {1: 64, 2: 8}:
        raise AssertionError(multiplicities)
    print(f"n={n} h={h} support_orbits_by_max_extra_list={dict(multiplicities)}")


def check_lifted_four():
    """Construct the base received word, verify all three cubic heads and the lift."""
    generator = pow(5, (PRIME - 1) // 8, PRIME)
    omega = [pow(generator, i, PRIME) for i in range(8)]
    support = {0, 1}
    errors = [{2, 3, 7}, {2, 5, 6}, {3, 4, 5}]
    heads = []
    for error in errors:
        roots = set(range(8)) - support - error
        values = [prod(x - omega[j] for j in roots) % PRIME for x in omega]
        heads.append([v * pow(values[0], -1, PRIME) % PRIME for v in values])
    received = [1, heads[0][1], 0, 0, 0, 0, 0, 0]
    for head, predicted in zip(heads, errors):
        if {i for i in range(8) if received[i] != head[i]} != predicted:
            raise AssertionError("base error set")
    scale = 2**27
    seams = [2, 3, 5]
    roots_per_seam = {
        j: (scale - 1) // 3 + (i < (scale - 1) % 3) for i, j in enumerate(seams)
    }
    error_counts = [scale * len(e) - sum(roots_per_seam.get(j, 0) for j in e)
                    for e in [support, *errors]]
    ceiling = 3 * scale - 2 * (scale - 1) // 3
    if ceiling != 313174700 or max(error_counts) != ceiling:
        raise AssertionError(error_counts)
    print(f"n={8*scale} four_error_counts={error_counts} first_bad_at_most={ceiling}")


if __name__ == "__main__":
    check_length(8)
    check_length(16)
    check_lifted_four()
