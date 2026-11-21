"""Verify the six edges, center values and site allocations of the half-rate witness."""

from itertools import combinations
from math import comb

from probe_many_head_locator_attack import require
from probe_smooth_four_head_attack import GENERATOR, PRIME


def main():
    n = 2**30
    s = n // 8
    width = s // 2
    root = pow(GENERATOR, s, PRIME)
    require(pow(root, 4, PRIME) == PRIME - 1, "quotient has order eight")
    vertices = [pow(root, j, PRIME) for j in range(4)]
    edges = list(combinations(range(4), 2))
    # The four vertex fibers each occupy two of the sixteen index blocks.
    # Each remaining block of width s/2 has one kind of nonroot site.
    roles = {4: (0, 14913082), 5: (1, 14913082), 6: (2, 14913082),
             7: (3, 14913081), 12: (4, 14913081), 13: (5, 14913081),
             14: (None, 44739241), 15: (None, 0)}
    cores = [0] * 6
    labels = common = 0
    for j in range(16):
        t = pow(root, j, PRIME)
        points = []
        for first, second in edges:
            a, b = vertices[first], vertices[second]
            x = ((a + b)*t - a*b) % PRIME
            y = ((a*a + a*b + b*b)*t - a*b*(a+b) + 7*x) % PRIME
            points.append((x, y))
        vertex = j % 8
        if vertex < 4:
            owner = next(i for i, edge in enumerate(edges) if vertex in edge)
            ordinary = width
        else:
            owner, ordinary = roles[j]
        received = points[owner] if owner is not None else (17, 29)
        root_sites = width - ordinary
        common += root_sites
        slopes = set()
        for i, (x, y) in enumerate(points):
            cores[i] += root_sites
            if (x, y) == received:
                cores[i] += ordinary
            else:
                require(y != received[1], "nonzero slope denominator")
                slopes.add((received[0]-x)*pow((y-received[1]) % PRIME, -1, PRIME) % PRIME)
        require(len(slopes) == (6 if owner is None else 3), "distinct usable directions")
        labels += ordinary * len(slopes)
    errors = n - min(cores) - 1
    require(common + s + 1 < n//2 <= min(cores), "degree and core uniqueness")
    require(labels > PRIME//2**128 and comb(labels, 2) <= PRIME, "over budget with simultaneous labels")
    require((common, errors, labels) == (402653182, 387740104, 2147483649), "production count")
    print(f"{errors} errors, {labels} distinct bad scalars, {common} roots, cores={cores}")


if __name__ == "__main__":
    main()
