"""Exact coset enumeration for the parity formula from capacity to radius one."""

from itertools import product
from math import comb


def require(test, detail):
    if not test:
        raise ArithmeticError(detail)


def coefficients(t, ell):
    return [((-1) ** (j - t)) * comb(j - 1, t - 1) for j in range(t, ell + 1)]


def profile(n, k, alphabet, t):
    if t == 0:
        return alphabet**k
    odd = (k - t) % 2
    ell = k - odd
    weights = coefficients(t, ell)
    moment_sum = sum(w * comb(n, j) * alphabet ** (k - j)
                     for j, w in enumerate(weights, t))
    zero_center_loss = sum(w * comb(n, j) for j, w in enumerate(weights, t)) - 1
    return moment_sum - odd * zero_center_loss


def evaluate(coeffs, x, p):
    value = 0
    for c in reversed(coeffs):
        value = (value * x + c) % p
    return value


def codewords(n, k, p, width):
    rows = [tuple(evaluate(a, x, p) for x in range(n))
            for a in product(range(p), repeat=k)]
    # Use base-p digits only to compare vector symbols for equality.
    for heads in product(rows, repeat=width):
        yield tuple(sum(digit * p**i for i, digit in enumerate(col)) for col in zip(*heads))


def bonneau_weights(n, k, alphabet, agreement_histogram):
    """Bonneau's coset weight formula (2.2)–(2.4), Davydov et al."""
    d = n - k + 1
    weights = list(reversed(agreement_histogram))
    if d == 1:
        return
    for w in range(d - 1, n + 1):
        universal = comb(n, w) * sum((-1) ** j * comb(w, j) * alphabet ** (w - d + 1 - j)
                                     for j in range(w - d + 2))
        small_weights = sum((-1) ** j * comb(j + n - w, j) * comb(n - v, w - j - v) * weights[v]
                            for j in range(w - d + 2, w + 1) for v in range(w - j + 1))
        require(universal + small_weights == weights[w], ("Bonneau", n, k, alphabet, w))


def check_code(n, k, p, width):
    alphabet = p**width
    words = list(codewords(n, k, p, width))
    require(len(set(words)) == alphabet**k, "injective evaluation")
    best = [0] * (k + 1)
    extremizers = [0] * (k + 1)
    exact = [profile(n, k, alphabet, t) for t in range(k + 1)]
    # Subtract the unique codeword agreeing on the first k symbols. Exactly one
    # representative of each coset now has a zero prefix of length k.
    for tail in product(range(alphabet), repeat=n - k):
        center = (0,) * k + tail
        histogram = [0] * (n + 1)
        for word in words:
            agreements = sum(x == y for x, y in zip(word, center))
            histogram[agreements] += 1
        bonneau_weights(n, k, alphabet, histogram)
        for t in range(k + 1):
            count = sum(histogram[t:])
            best[t] = max(best[t], count)
            attaining = count == exact[t]
            extremizers[t] += attaining
            predicted = (t == 0 or
                         (not any(tail) if (k - t) % 2 else not any(histogram[k + 1:])))
            require(attaining == predicted, ("maximizer", n, k, p, width, t, tail))
    require(best == exact and all(extremizers), ("profile", n, k, p, width, best, exact))
    return alphabet**(n - k), alphabet**n


def check_differences():
    for k in range(1, 24):
        for t in range(1, k + 1):
            ell = k - (k - t) % 2
            weights = coefficients(t, ell)

            def poly(s):
                return sum(w * comb(s, j) for j, w in enumerate(weights, t))

            for s in range(ell + 1):
                require(poly(s) == int(s >= t), ("interpolation", s, t, ell))
            for s in range(ell, 41):
                delta = comb(s, t - 1) * comb(s - t, ell - t)
                require(poly(s + 1) - poly(s) == delta, ("difference", s, t, ell))
                require(delta * (s - t + 1) ==
                        comb(s, ell) * (ell - t + 1) * comb(ell, t - 1),
                        ("ratio", s, t, ell))


if __name__ == "__main__":
    check_differences()
    cases = centers = pairs = 0
    for p, n, width in [(2, 2, 1), (3, 3, 1), (5, 5, 1), (7, 6, 1),
                        (3, 3, 2), (5, 4, 2), (3, 3, 3)]:
        for k in range(1, n + 1):
            cosets, comparisons = check_code(n, k, p, width)
            cases += 1
            centers += cosets
            pairs += comparisons
    print(f"verified {cases} codes, {centers} coset representatives, {pairs} word comparisons")
