"""Check the quarter-rate matching, rational-center error count and pencil identities."""
from fractions import Fraction
from itertools import combinations, product

from probe_quarter_coset_lists import require


def named_bounds():
    n = 2**30
    d = n // 4 - 1
    t = 2 * d
    m = 2 * n + 1
    upper = 1 + Fraction(m * (n * d - t * t), n * d)
    energy = 2 * upper * (upper - 1) * (upper + 1)**2

    def matching(h):
        mu = 1 - Fraction(h, d)
        bound = (m - energy / (1 - mu**2) - energy / mu**4) / 2
        return bound.numerator // bound.denominator

    small, large = matching(901), matching(1_000_000)
    require((small, large) == (1_182_724, 1_072_766_345), 'disjoint pairs')
    holes = n - 2 * t + 900
    require(n - 2 * holes - (1_000_000 + 3) > 3 * d, 'common determinant roots')
    coarse = 4 * holes - 4
    passing = []
    for exceptional in range(holes + 1, coarse + 1):
        degree = (exceptional - 4) // 2
        hits = exceptional - holes
        if small * (hits**2 - exceptional * degree) <= exceptional * (hits - degree):
            passing.append(exceptional)
    require((holes, coarse, max(passing)) == (904, 3612, 3080), 'residual agreement bound')
    require((max(passing) - 4) // 2 == 1538, 'parameter degree bound')
    print(f'{small:,} tight pairs, {large:,} pencil members, '
          f'{max(passing):,} possible exceptional sites, parameter degree at most 1,538')


def field_control():
    # Every unordered factorization of one highly split polynomial supplies a genuine
    # quadratic in a pencil. Varying the received word also exercises exception sites.
    p = 17
    xs = range(p)
    roots = (1, 2, 3, 4, 5, 6)

    def factor(subset, x):
        result = 1
        for a in subset:
            result = result * (x - a) % p
        return result

    partitions = [T for T in combinations(roots, 3) if 1 in T]
    pairs = [(T, set(roots).difference(T)) for T in partitions]
    for x in xs:
        values = [(factor(T, x), factor(V, x)) for T, V in pairs]
        N = factor(roots, x)
        sums = [(a + b) % p for a, b in values]
        for i, (a, b) in enumerate(values):
            require(a*b % p == N, 'common divisor product')
            for j, (c, e) in enumerate(values):
                require((a-c)*(b-c)*(a-e)*(b-e) % p == N*(sums[i]-sums[j])**2 % p,
                        'four cross-differences')
        for y in xs:
            if N or y:
                hits = {s for s, factors in zip(sums, values) if y in factors}
                require(len(hits) <= 1, 'a single sum on an exceptional site')
    # Test determinants without any polynomial-pencil assumptions at every possible
    # common root and every choice of the three other roots over the small field.
    for y, a, b, c in product(range(7), repeat=4):
        s = [y + v for v in (a, b, c)]
        q = [y * v for v in (a, b, c)]
        require(((s[1]-s[0])*(q[2]-q[0]) - (s[2]-s[0])*(q[1]-q[0])) % 7 == 0,
                'triple determinant')
    print('Two finite-field controls passed.')


if __name__ == '__main__':
    field_control()
    named_bounds()
