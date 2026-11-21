"""Enumerate every possible error locator for a smooth RS received word.

The center is 1 + X + ... + X^((s-1)*h-1), the code dimension is
(s-2)*h, and the domain has size s*h. At h+1 errors the entire list
has size s-1 when h+1 > s. See docs/research/proximity-gap/PROGRESS.md for the all-length proof.
"""

from itertools import combinations


def vanisher(roots, prime):
    coefficients = [1]
    for root in roots:
        updated = [0] * (len(coefficients) + 1)
        for degree, value in enumerate(coefficients):
            updated[degree] = (updated[degree] - root * value) % prime
            updated[degree + 1] = value
        coefficients = updated
    return coefficients


def exact_list(prime, generator, fibers, width):
    length = fibers * width
    domain = tuple(pow(generator, index, prime) for index in range(length))
    if len(set(domain)) != length or pow(generator, length, prime) != 1:
        raise ValueError("generator does not have the declared order")

    # A monic degree (s-1)*h-1 word can agree with the received word
    # only through a vanisher of that degree. Subtracting this vanisher
    # must cancel every coefficient from k=(s-2)*h upwards. Enumerating
    # agreement sets checks this independently of the error-locator proof.
    k = (fibers - 2) * width
    lists = set()
    for errors in combinations(domain, width + 1):
        errors = frozenset(errors)
        agreement_vanisher = vanisher((x for x in domain if x not in errors), prime)
        if all(value == 1 for value in agreement_vanisher[k:]):
            lists.add(errors)
    return lists, domain


def check(prime, generator, fibers, width):
    candidates, domain = exact_list(prime, generator, fibers, width)
    image = {pow(x, width, prime) for x in domain}
    predicted = {
        frozenset(x for x in domain if x == 1 or pow(x, width, prime) == value)
        for value in image if value != 1
    }
    if width + 1 <= fibers or candidates != predicted:
        raise AssertionError((prime, fibers, width, len(candidates), len(predicted)))
    print(f"p={prime} n={len(domain)} k={(fibers-2)*width} e={width+1} complete_list={len(candidates)}")


def check_shifted_moment_windows():
    """Compare every pair implicitly via its moment class at each shift.

    Equal signed memberships at opposite points are equivalent to equality
    of the difference of their indicator values on each opposite pair.
    Checking one such vector per bucket therefore checks all pairs in it.
    """
    p = 2013265921
    n, h = 16, 4
    g = pow(31, (p - 1) // n, p)
    if pow(g, n, p) != 1 or pow(g, n // 2, p) != p - 1:
        raise AssertionError("incorrect root order")
    if p ** (n // 8 - 1) <= (2 * h + 2) ** (n // 2):
        raise AssertionError("norm threshold")
    for shift in range(h + 1):
        exponents = [r for r in range(1 - shift, h - shift) if r % 2]
        powers = [[pow(g, (r * i) % n, p) for i in range(n)] for r in exponents]
        buckets = {}
        for support in combinations(range(n), h + 1):
            key = tuple(sum(row[i] for i in support) % p for row in powers)
            skew = tuple(int(i in support) - int(i + n//2 in support) for i in range(n//2))
            if buckets.setdefault(key, skew) != skew:
                raise AssertionError((shift, support))
        print(f"n={n} shift={shift} primitive_exponents={exponents} moment_classes={len(buckets)}")

    h = 2**28
    # Power-of-two comparison suffices even for the smallest prime of interest.
    if not (2 * h + 2 < 2**30 and 128 * (h//2 - 1) > 30 * (2*h)):
        raise AssertionError("production norm threshold")


if __name__ == "__main__":
    check(13, 2, 3, 4)
    check(17, 3, 4, 4)
    check(97, pow(5, 6, 97), 4, 4)
    check(31, pow(3, 2, 31), 3, 5)
    check_shifted_moment_windows()
