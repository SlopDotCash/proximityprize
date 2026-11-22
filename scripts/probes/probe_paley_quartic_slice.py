"""Exact contractions and a positive-definiteness certificate for the edge block."""

from collections import Counter
from itertools import combinations
from math import comb, lcm


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def moments(p, k):
    squares = {i*i % p for i in range(1, p)}
    adjacency = [sum(1 << ((a+s) % p) for s in squares) for a in range(p)]
    counts = Counter()

    def grow(candidates, mask, left):
        if left:
            while candidates:
                bit = candidates & -candidates
                candidates ^= bit
                grow(candidates & adjacency[bit.bit_length()-1], mask | bit, left-1)
        else:
            subset = mask
            while subset:
                counts[subset] += 1
                subset = (subset-1) & mask
            counts[0] += 1

    grow((1 << p)-1, 0, 4)
    four_sites = counts[0]
    den = [comb(k-j, 4-j) for j in range(5)]
    unit = lcm(*den)
    y = {mask: count*(unit//den[mask.bit_count()]) for mask, count in counts.items()}
    require(four_sites and y[0]*comb(k, 4) == unit*four_sites, "singular four-site total")
    contractions = Counter()
    for mask, weight in y.items():
        sites = mask
        while sites:
            bit = sites & -sites
            sites ^= bit
            contractions[mask ^ bit] += weight
    require(contractions == {mask: (k-mask.bit_count())*weight for mask, weight in y.items()
                             if mask.bit_count() < 4}, "slice contractions on all monomials")
    # WE=(k-1)C, computed from the incident edges themselves, including the
    # singleton-on-edge cases and the triples with zero weight.
    edges = [(1 << a) | (1 << b) for a, b in combinations(range(p), 2)
             if (a-b) % p in squares]
    require(len({y[e] for e in edges}) == 1, "edge transitivity")
    # The affine square multipliers and translations act transitively on edges;
    # check every edge directly at the smaller primes and one orbit at p=137.
    for v, neighbors in enumerate(adjacency):
        star = [(1 << v) | (1 << a) for a in range(p) if neighbors >> a & 1]
        for edge in (edges if p < 100 else edges[:1]):
            require(sum(y.get(edge | other, 0) for other in star) ==
                    (k-1)*y.get(edge | (1 << v), 0), "incidence contraction")
    if p == 137 and k == 6:
        clique = (0, 1, 2, 38)
        require(y[sum(1 << i for i in clique)] > 0, "missing obstructing four-clique")
        common = [i for i in range(p) if all((i-v) % p in squares for v in clique)]
        require(common == [16, 19, 39, 74, 101] and
                not any((a-b) % p in squares for a, b in combinations(common, 2)),
                "four-clique extends to a six-clique")
    return squares, y, four_sites


def positive_definite(matrix):
    # Fraction-free symmetric elimination; the successive pivots have the
    # signs of leading principal minors (Sylvester's criterion).
    mat = [row[:] for row in matrix]
    previous = 1
    for i in range(len(mat)):
        pivot = mat[i][i]
        if pivot <= 0:
            return False
        for a in range(i+1, len(mat)):
            for b in range(a, len(mat)):
                quotient, rem = divmod(pivot*mat[a][b]-mat[a][i]*mat[i][b], previous)
                require(rem == 0, "nonexact Bareiss step")
                mat[a][b] = mat[b][a] = quotient
        previous = pivot
    return True


def root_intervals(degree):
    # For p=2*degree+1 prime, 1+sum_{h=1}^degree T_h has the distinct roots
    # 2*cos(2*pi*j/p), j=1,...,degree, with T_h(2*cos t)=2*cos(h*t).
    previous, current = [2], [0, 1]
    poly = [1]+[0]*degree
    for h in range(1, degree+1):
        for i, coeff in enumerate(current):
            poly[i] += coeff
        following = [0]+current
        for i, coeff in enumerate(previous):
            following[i] -= coeff
        previous, current = current, following

    def sign(num, den):
        value, power = poly[-1], 1
        for coeff in reversed(poly[:-1]):
            power *= den
            value = value*num + power*coeff
        require(value != 0, "unexpected rational cyclotomic root")
        return value > 0

    den = 256
    signs = [sign(i, den) for i in range(-2*den, 2*den+1)]
    starts = [i-2*den for i in range(4*den) if signs[i] != signs[i+1]]
    require(len(starts) == degree, "incomplete real root isolation")
    intervals = []
    for start in starts:
        lo, scale = start, den
        left_sign = sign(lo, scale)
        while scale < 1 << 45:
            if sign(2*lo+1, 2*scale) == left_sign:
                lo = 2*lo+1
            else:
                lo *= 2
            scale *= 2
        intervals.append((lo, scale))
    return intervals


def certify_edge_block(p, squares, y):
    # With midpoint coordinates, negation makes each offset sequence even.
    # Its real Fourier matrix is A_0 + sum A_h*T_h(2*cos theta).
    half = (p-1)//2
    radii = [r for r in range(1, half+1) if 2*r % p in squares]

    def edge(mid, r):
        return (1 << ((mid-r) % p)) | (1 << ((mid+r) % p))

    coeff = [[[y.get(edge(0, r) | edge(h, s), 0) for h in range(half+1)]
              for s in radii] for r in radii]
    for i, r in enumerate(radii):
        for j, s in enumerate(radii):
            require(coeff[i][j] == coeff[j][i] and
                    all(c == y.get(edge(0, r) | edge(-h, s), 0)
                        for h, c in enumerate(coeff[i][j])), "Fourier symmetry")
    require(len(radii)*p == p*(p-1)//4, "edge Fourier inventory")
    zero = [[row[0]+2*sum(row[1:]) for row in cell] for cell in coeff]
    require(positive_definite(zero), "constant frequency was not positive definite")
    scale = 1 << 32
    for lo, den in root_intervals(half):
        # x=lo/den approximates its root within 1/den. Since |T'_h|<=h^2
        # on [-2,2], each scaled T_h incurs error <=1 + scale*h^2/den.
        # Values at the rational endpoint use integer polynomial recurrence.
        weights = [scale]
        previous, current, power = 2, lo, den
        for _ in range(1, half+1):
            weights.append((scale*current)//power)
            previous, current = current, lo*current-den*den*previous
            power *= den
        matrix = [[sum(c*w for c, w in zip(cell, weights)) for cell in row] for row in coeff]
        err_num = max(sum(c*(den+scale*h*h) for h, c in enumerate(cell) if h)
                      for row in coeff for cell in row)
        # Absolute row sums bound the operator error across the root interval.
        shift = (len(radii)*err_num+den-1)//den
        for i in range(len(radii)):
            matrix[i][i] -= shift
        require(positive_definite(matrix), "failed certified Fourier margin")
    return half+1


def main():
    for p, k in ((29, 4), (53, 5), (137, 6)):
        squares, y, four = moments(p, k)
        frequencies = certify_edge_block(p, squares, y)
        print(f"p={p} k={k}: {four} four-cliques, all contractions, "
              f"{frequencies} exact positive Fourier blocks")


if __name__ == "__main__":
    main()
