"""Verify the budget-two smooth RS list threshold and the coset construction.

Run with Python 3.8 or newer. The large-domain check works on the four
cosets. Small instances also expand the actual polynomials at every point.
"""

from itertools import combinations, product
from math import comb


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def poly_mul(left, right, p):
    out = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] = (out[i + j] + a * b) % p
    return out


def evaluate(coefficients, x, p):
    answer = 0
    for c in reversed(coefficients):
        answer = (answer * x + c) % p
    return answer


def fiber_polynomial(coset_values, p):
    """Return coefficients of the monic product of Y-a over selected fibers."""
    out = [1]
    for a in coset_values:
        out = poly_mul(out, [-a, 1], p)
    return out


def production_certificate():
    p = 680564733906249808969588989158290882561
    n = 2**30
    s, k = n // 4, n // 2
    # A Proth certificate: for each prime r dividing p, the order of 7
    # modulo r is divisible by 2^92, so r exceeds the square root of p.
    require(p - 1 == (2**37 + 13) * 2**92, "2-part of p-1")
    require(p < 2**184 and pow(7, (p - 1) // 2, p) == p - 1,
            "Proth primality certificate")
    g = pow(7, (p - 1) // n, p)
    require(g == 249631592359537775319900728087975376651, "generator")
    require(pow(g, n, p) == 1 and pow(g, n // 2, p) == p - 1,
            "exact order 2^30")
    require(p // 2**128 == 2, "floor of list budget")
    values = [pow(g, j * s, p) for j in range(4)]
    require(len(set(values)) == 4, "four distinct fiber values")
    # H vanishes at s-1 of the s points in the reserved fiber, represented
    # below by values[0]. Check the residual polynomial on the quotient.
    heads = set()
    for chosen in combinations(values[1:], 2):
        residual = fiber_polynomial(chosen, p)
        require(residual[-1] == 1, "degree-two leading coefficient")
        # f_T(X) = H(X)*(X^k - residual(X^s)). Its degree is at most
        # (s-1) + s = 2s-1, because the monic degree-two term cancels.
        heads.add(tuple((-c) % p for c in residual[:-1]))
        roots = [a for a in values if evaluate(residual, a, p) == 0]
        require(set(roots) == set(chosen), "exact support on quotient")
        require(n - (s * len(roots) + s - 1) == s + 1, "first failing radius")
    require(len(heads) == 3, "three distinct codewords")
    require(2 * s < n - k + 1, "unique decoding at preceding radius")
    print(f"n={n} k={k} p={p} g={g} budget=2 last_good={s} first_bad={s+1}")


def finite_fiber_lists(p, g, n, fibers, selected):
    """Independently expand all candidates for n=M*s, k=b*s."""
    s, remainder = divmod(n, fibers)
    k = selected * s
    xs = [pow(g, i, p) for i in range(n)]
    require(remainder == 0 and 0 < selected < fibers, "fiber parameters")
    require(len(set(xs)) == n and pow(g, n, p) == 1, "small-domain generator")
    values = [pow(g, i * s, p) for i in range(fibers)]
    reserved = [x for x in xs if pow(x, s, p) == values[0]]
    require(len(reserved) == s, "reserved fiber size")
    h = fiber_polynomial(reserved[1:], p)
    center = [evaluate(h, x, p) * pow(x, k, p) % p for x in xs]
    words = set()
    for chosen in combinations(values[1:], selected):
        residual = fiber_polynomial(chosen, p)
        head = [0] * ((selected - 1) * s + 1)
        for j, c in enumerate(residual[:-1]):
            head[j * s] = (-c) % p
        coefficients = poly_mul(h, head, p)
        require(len(coefficients) <= k, "degree below k")
        word = tuple(evaluate(coefficients, x, p) for x in xs)
        agreements = {x for x, y, z in zip(xs, center, word) if y == z}
        expected = set(reserved[1:]) | {x for x in xs if pow(x, s, p) in chosen}
        require(agreements == expected and len(agreements) == k + s - 1,
                "actual exact agreement support")
        words.add(word)
    require(len(words) == comb(fibers - 1, selected), "distinct finite list")
    print(f"p={p} n={n} k={k} s={s} explicit_list={len(words)} agreements={k+s-1}")


def exhaustive_small_threshold():
    """Check every [4,2] word and every center over F5 for list budget 2."""
    p = 5
    xs = (1, 2, 4, 3)
    words = [tuple((a * x + b) % p for x in xs)
             for a, b in product(range(p), repeat=2)]
    maxima = [0, 0]
    for center in product(range(p), repeat=4):
        distances = [sum(y != z for y, z in zip(center, word)) for word in words]
        for radius in (1, 2):
            maxima[radius - 1] = max(maxima[radius - 1],
                                     sum(t <= radius for t in distances))
    require(maxima[0] == 1 and maxima[1] > 2, "exhaustive adjacent thresholds")
    print(f"exhaustive F5 [4,2] max_lists_at_1_and_2={maxima}")


def modular_rank(rows, p):
    """Rank of a matrix over F_p by row elimination."""
    matrix = [list(row) for row in rows]
    rank = 0
    for col in range(len(matrix[0])):
        pivot = next((j for j in range(rank, len(matrix)) if matrix[j][col] % p), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        inverse = pow(matrix[rank][col], -1, p)
        for j in range(rank + 1, len(matrix)):
            factor = matrix[j][col] * inverse % p
            if factor:
                matrix[j] = [(u - factor * v) % p
                             for u, v in zip(matrix[j], matrix[rank])]
        rank += 1
    return rank


def check_common_syndrome_dimension(supports, d, p):
    """Compare the actual shared syndrome dimension to the common-support size."""
    # For each i>0 impose V(E_i)e_i - V(E_0)e_0 = 0. Any RS column
    # multipliers are nonzero and are absorbed into the variables e_i.
    rows = []
    for other in range(1, len(supports)):
        for j in range(2 * d):
            row = []
            for i, support in enumerate(supports):
                sign = int(i == other) - int(i == 0)
                row.extend(sign * pow(x, j, p) % p for x in sorted(support))
            rows.append(row)
    nullity = sum(map(len, supports)) - modular_rank(rows, p)
    return nullity, len(set.intersection(*supports))


def finite_syndrome_obstruction():
    p, g, n = 17, 3, 16
    d = n // 4
    xs = [pow(g, j, p) for j in range(n)]
    fibers = {pow(x, d, p): {z for z in xs if pow(z, d, p) == pow(x, d, p)}
              for x in xs}
    classes = list(fibers.values())
    patterns = [
        [set()] * 4,
        [{xs[0]} - group for group in classes],
        [{xs[0], xs[1], xs[2], xs[3]} - group for group in classes],
        [{xs[(i + 1) % 4]} for i in range(4)],
    ]
    dimensions = []
    for extras in patterns:
        require(len(set.union(*extras)) <= d, "outlier union in range")
        supports = [group | extra for group, extra in zip(classes, extras)]
        nullity, shared = check_common_syndrome_dimension(supports, d, p)
        require(nullity == shared, "four cosets admit only common errors")
        dimensions.append(nullity)
    # Omitting a coset leaves room for a syndrome without a single common
    # representative. Add one point of the omitted coset to all three supports.
    supports = [group | {xs[0]} for group in classes if xs[0] not in group]
    nullity, shared = check_common_syndrome_dimension(supports, d, p)
    require((nullity, shared) == (2, 1), "three-coset counterexample to full coverage")
    print(f"four-coset common dimensions={dimensions}; three-coset dimension={nullity}")


if __name__ == "__main__":
    production_certificate()
    for parameters in [(17, 3, 16, 4, 2), (17, 3, 16, 8, 2),
                       (97, 28, 32, 8, 3), (97, 28, 32, 16, 8)]:
        finite_fiber_lists(*parameters)
    exhaustive_small_threshold()
    finite_syndrome_obstruction()
