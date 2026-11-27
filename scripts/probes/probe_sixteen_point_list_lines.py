"""Exact first nonunique lists on two smooth boards over extensions of F_17."""

from collections import Counter
from itertools import combinations
from math import comb, prod


PRIME = 17


def line_key(left, right, inverse):
    """Reduced row basis of a projective line in the pivot error coordinates."""
    p = len(inverse)
    a = next(i for i, x in enumerate(left) if x)
    top = tuple(x * inverse[left[a]] % p for x in left)
    lower = [(y - right[a] * x) % p for x, y in zip(top, right, strict=True)]
    b = next(i for i, x in enumerate(lower) if x)
    bottom = tuple(y * inverse[lower[b]] % p for y in lower)
    top = tuple((x - top[b] * y) % p for x, y in zip(top, bottom, strict=True))
    return (top, bottom) if a < b else (bottom, top)


def census(n, e):
    """Count all lists through a pivot of exact weight e, with n-k=2e-2."""
    p = PRIME
    board = tuple(pow(3, i * (p - 1) // n, p) for i in range(n))
    assert len(set(board)) == n
    full = (1 << n) - 1
    inverse = [0] + [pow(x, -1, p) for x in range(1, p)]

    def mask(indices):
        return sum(1 << i for i in indices)

    def normal(values):
        scale = inverse[values[0]]
        return tuple(v * scale % p for v in values[1:])

    # Locators vanish exactly off A union B. Cache their values on all sites.
    locators = {}
    for size in (n - 2 * e, n - 2 * e + 1):
        for zeros in combinations(range(n), size):
            locators[mask(zeros)] = tuple(
                prod(x - board[i] for i in zeros) % p for x in board)

    seen = set()
    peak, generic_peak, orbit_count = 0, 0, 0
    witness = None
    for idx in combinations(range(n), e):
        A = mask(idx)
        if A in seen:
            continue
        orbit_count += 1
        seen.update(mask((a + sign * i) % n for i in idx)
                    for a in range(n) for sign in (1, -1))
        outside = tuple(i for i in range(n) if not (A >> i & 1))
        rational, generic = Counter(), Counter()

        # An (e-1)-site neighbor must be disjoint. The difference is a
        # nonzero constant times the locator; it fixes a unique pivot point.
        for rest in combinations(outside, e - 1):
            B = mask(rest)
            L = locators[full ^ (A | B)]
            rational[normal([L[i] for i in idx])] += 1

            # Put a shared site back for an e-site neighbor. The error at
            # the shared site can be varied independently of the locator.
            base = [L[i] for i in idx]
            for j in range(e):
                direction = tuple(int(i == j) for i in range(e))
                generic[line_key(base, direction, inverse)] += 1
                old = base[j]
                for value in range(1, p):
                    if value != old:
                        base[j] = value
                        rational[normal(base)] += 1
                base[j] = old

        # Disjoint e-site neighbors have differences L times a linear
        # polynomial. Exclude its roots on either support to keep weights exact.
        for rest in combinations(outside, e):
            B = mask(rest)
            L = locators[full ^ (A | B)]
            base = tuple(L[i] for i in idx)
            slope = tuple(L[i] * board[i] % p for i in idx)
            generic[line_key(base, slope, inverse)] += 1
            rational[normal(base)] += 1
            forbidden = {board[i] for i in (*idx, *rest)}
            for root in range(p):
                if root not in forbidden:
                    values = [(b - root * a) % p for a, b in zip(base, slope, strict=True)]
                    rational[normal(values)] += 1

        error, rational_count = rational.most_common(1)[0]
        if rational_count + 1 > peak:
            peak = rational_count + 1
            pivot = [0] * n
            for i, value in zip(idx, (1, *error), strict=True):
                pivot[i] = value
            witness = pivot
        generic_peak = max(generic_peak, 1 + max(generic.values()))
    assert len(seen) == comb(n, e)
    return peak, generic_peak, orbit_count, witness


def direct_list(word, n, k, e):
    """Interpolate every k-set in F_17 and evaluate directly on every site."""
    p = PRIME
    x = tuple(pow(3, j * (p - 1) // n, p) for j in range(n))
    words = set()
    for S in combinations(range(n), k):
        coeff = {i: word[i] * pow(prod(x[i] - x[j] for j in S if j != i) % p, -1, p) % p
                 for i in S}
        candidate = tuple(sum(coeff[i] * prod(at - x[j] for j in S if j != i)
                              for i in S) % p for at in x)
        if sum(a != b for a, b in zip(candidate, word, strict=True)) <= e:
            words.add(candidate)
    return len(words)


def main():
    for n, e, expected in [(8, 3, (7, 3, 5)), (16, 5, (6, 3, 147))]:
        k = n - 2 * e + 2
        peak, generic, orbits, word = census(n, e)
        print(f"n={n}, k={k}, e={e}: {orbits} pivot orbits, maximum {peak} over F_17, "
              f"maximum {generic} off the rational points of the lines; center {word}", flush=True)
        assert (peak, generic, orbits) == expected
        assert direct_list(word, n, k, e) == peak

    half = [1, 1, 11, 0, 0, 0, 0, 0, 12, 0, 4, 0, 0, 0, 0, 0]
    x = [pow(3, j, PRIME) for j in range(16)]
    quarter = [pow(t, 5, PRIME) * (1 + 5 * pow(t, 8, PRIME)) % PRIME for t in x]
    assert direct_list(half, 16, 8, 6) == 10
    assert direct_list(quarter, 16, 4, 9) == 8
    assert 17**32 // 2**128 == 6
    print("Direct interpolation: 10 half-rate words at six errors and 8 quarter-rate words "
          "at nine errors, with a 128-bit budget of 6.")


if __name__ == "__main__":
    main()
