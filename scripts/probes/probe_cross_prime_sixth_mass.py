"""Cross-check the split-place norm inequality against literal ordered triple counts."""

from collections import Counter
from functools import cache
from itertools import combinations_with_replacement, product
from math import factorial, log, prod


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def cyclotomic_norm(coefficients):
    """Absolute norm from Z[X]/(X^degree+1), for dyadic degree."""
    while len(coefficients) > 1:
        degree = len(coefficients) // 2
        reduced = [0] * degree
        for parity, sign in ((0, 1), (1, -1)):
            half = coefficients[parity::2]
            for i, x in enumerate(half):
                for j, y in enumerate(half):
                    exponent = i + j + parity
                    reduced[exponent % degree] += sign * (-1 if exponent >= degree else 1) * x * y
        coefficients = reduced
    return abs(coefficients[0])


@cache
def factors(value):
    result = {}
    q = 2
    while q * q <= value:
        while value % q == 0:
            result[q] = result.get(q, 0) + 1
            value //= q
        q = 3 if q == 2 else q + 2
    if value != 1:
        result[value] = 1
    return result


@cache
def subgroup(p, n):
    for b in range(2, p):
        g = pow(b, (p - 1) // n, p)
        if pow(g, n // 2, p) == p - 1:
            return tuple(pow(g, j, p) for j in range(n))
    raise ValueError("no generator")


def check(n):
    degree = n // 2
    hits = Counter()
    zero_words = 0
    log_norm_sum = 0
    ordered_count = 0
    for exponents in combinations_with_replacement(range(n), 6):
        weight = factorial(6) // prod(factorial(k) for k in Counter(exponents).values())
        ordered_count += weight
        coefficients = [0] * degree
        for i in exponents:
            coefficients[i % degree] += 1 if i < degree else -1
        norm = cyclotomic_norm(coefficients)
        if norm == 0:
            require(not any(coefficients), "nonzero coefficient vector has zero norm")
            zero_words += weight
            continue
        log_norm_sum += weight * log(norm)
        for p, exponent in factors(norm).items():
            if (p - 1) % n:
                continue
            H = subgroup(p, n)
            r = sum(sum(H[(j * i) % n] for i in exponents) % p == 0
                    for j in range(1, n, 2))
            require(1 <= r <= exponent, "split-prime incidence count exceeds its valuation or vanishes")
            hits[p] += weight * r

    require(ordered_count == n**6, "incomplete ordered-tuple census")
    require(zero_words == 15 * n**3 - 45 * n**2 + 40 * n, "incorrect count of zero relations")
    total_excess = 0
    log_mass = 0
    for p, accumulated_hits in hits.items():
        triples = Counter(sum(t) % p for t in product(subgroup(p, n), repeat=3))
        excess = sum(m**2 for m in triples.values()) - zero_words
        require(degree * excess == accumulated_hits, "split-place tally disagrees with literal triple counts")
        total_excess += excess
        log_mass += excess * log(p)
    # All comparisons of counts above are exact. These two checks summarize
    # the independently computed real logarithms, with slack for rounding.
    require(degree * log_mass <= log_norm_sum + 1e-7, "weighted prime mass exceeds observed log norm")
    require(log_norm_sum <= degree * n**6 * log(6) / 2 + 1e-7, "observed log norm exceeds aggregate upper bound")
    print(f"n={n} split_exceptional={len(hits)} sum_excess={total_excess} "
          f"log_mass={log_mass:.6f} normalized_log_norm={log_norm_sum / degree:.6f}")


if __name__ == "__main__":
    for group_order in (2, 4, 8, 16):
        check(group_order)
