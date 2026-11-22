"""Verify the six edges, center values and site allocations of the half-rate witness."""

from itertools import combinations
from math import comb

from probe_many_head_locator_attack import require
from probe_smooth_four_head_attack import GENERATOR, PRIME


def edge_values(t, vertices, edges):
    points = []
    for first, second in edges:
        a, b = vertices[first], vertices[second]
        x = ((a + b)*t - a*b) % PRIME
        y = ((a*a + a*b + b*b)*t - a*b*(a+b) + 7*x) % PRIME
        points.append((x, y))
    return points


def five_vertex_mass(root, s):
    vertices = [pow(root, j, PRIME) for j in range(5)]
    edges = list(combinations(range(5), 2))
    common = 3*s - 2
    cores = [common] * len(edges)
    labels = 0
    for j in range(6):
        points = edge_values(pow(root, j, PRIME), vertices, edges)
        count = s if j < 5 else 2
        owner = next((i for i, edge in enumerate(edges) if j in edge), None)
        u, v = points[owner] if owner is not None else (17, 29)
        directions = set()
        for i, (x, y) in enumerate(points):
            if j in edges[i]:
                require((x, y) == (u, v), "incident edge agrees")
                cores[i] += count
            else:
                require(y != v, "foreign edge misses the second coordinate")
                directions.add((u-x)*pow((y-v) % PRIME, -1, PRIME) % PRIME)
        require(len(directions) == (6 if j < 5 else 10), "all foreign directions are distinct")
        labels += count * len(directions)
    require(set(cores) == {671088638} and labels == 4026531860, "ten-head population")
    require(comb(labels, 2) <= PRIME, "simultaneous separation")
    print(f"Five vertices: {8*s-min(cores)-1} errors, {labels} distinct labels, all cores {min(cores)}")


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
        points = edge_values(t, vertices, edges)
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
    five_vertex_mass(root, s)
    print(f"{errors} errors, {labels} distinct bad scalars, {common} roots, cores={cores}")


if __name__ == "__main__":
    main()
