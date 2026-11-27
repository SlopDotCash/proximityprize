"""Check the quarter-rate matching, rational-center error count and pencil identities."""
from fractions import Fraction
from itertools import combinations, product

from probe_quarter_coset_lists import evaluate, fiber_polynomial, poly_mul, require
from probe_quarter_sixteen_splines import nullspace


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


def recovery_controls():
    # In the second linear system the columns represent homogeneous forms, by
    # storing their coefficient of X^j Z^(weight-j) in position j.
    p, d, cap = 12097, 32, 9
    n = 4*d+4
    for degree, large_denominator in ((64, True), (64, False), (63, False)):
        u = 1
        v = next(w for b in range(2, p) if (w := pow(b, degree, p)) != u)
        zeros = [x for x in range(p) if pow(x, degree, p) in (u, v)]
        require(len(zeros) == 2*degree, 'fully split product')
        scale = 1
        if large_denominator:
            anchor = next(pow(b, d, p) for b in range(1, p)
                          if pow(b, 2*d, p) not in (u, v))
            A = [-anchor % p] + [0]*(d-1) + [1]
            B = [(u-anchor**2) % p]
            scale = (anchor**2-u) * pow(anchor**2-v, -1, p) % p
        else:
            A = [1]
            B = [u]+[0]*(degree-1)+[p-1]
        ell = min(d+1-len(A), 2*d+1-len(B))
        first = [-u]+[0]*(degree-1)+[1]
        second = [-scale*v]+[0]*(degree-1)+[scale]
        N = poly_mul(first, second, p)
        # Omit two roots of N and insert other sites. Include a pole if available.
        sites = zeros[2:]
        poles = [x for x in range(p) if evaluate(A, x, p) == 0]
        fillers = [x for x in range(p) if x not in zeros and x not in poles]
        sites = sites + (poles[:1]+fillers)[:n-len(sites)]
        received = []
        for i, x in enumerate(sites):
            a, b = evaluate(A, x, p), evaluate(B, x, p)
            received.append((b*pow(a, -1, p) + (i == 0)) % p if a else 0)
        weights = (d+cap, 2*d+cap)
        rows = [[-y*pow(x, j, p) % p for j in range(weights[0]+1)] +
                [pow(x, j, p) for j in range(weights[1]+1)]
                for x, y in zip(sites, received)]
        first_space = nullspace(rows, p)
        require(first_space, 'a rational recovery solution')
        for vec in first_space:
            U, V = vec[:weights[0]+1], vec[weights[0]+1:]
            for x in range(150):
                require((evaluate(A, x, p)*evaluate(V, x, p)
                         - evaluate(B, x, p)*evaluate(U, x, p)) % p == 0,
                        'unique reduced rational function')

        G = fiber_polynomial(sites, p)
        families = [(poly_mul(B, B, p), cap),
                    ([-v for v in G], cap-4-2*ell),
                    ([-v for v in A], 3*d-ell+cap)]
        columns = [([0]*shift + factor) for factor, weight in families
                   for shift in range(weight+1)]
        total = 4*d-2*ell+cap
        eqs = [[col[j] % p if j < len(col) else 0 for col in columns]
               for j in range(total+1)]
        kernel = nullspace(eqs, p)
        require(kernel, 'a homogeneous recovery solution')
        for vec in kernel:
            K = vec[:cap+1]
            D = vec[cap+1:cap+1+(cap-4-2*ell)+1]
            require(any(K) and any(D), 'nonzero ratio')
            lhs, rhs = poly_mul(N, K, p), poly_mul(G, D, p)
            require(all((lhs[j] if j < len(lhs) else 0) == (rhs[j] if j < len(rhs) else 0)
                        for j in range(total+1)), 'every solution recovers the true product')
    print('Three homogeneous recovery systems passed, including a pole and a common zero at infinity.')


if __name__ == '__main__':
    field_control()
    named_bounds()
    recovery_controls()
