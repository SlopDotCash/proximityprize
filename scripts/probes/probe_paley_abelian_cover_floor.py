#!/usr/bin/env python3
"""Exact first-prize spectral floor from a test function on the abelian cover."""

from fractions import Fraction
from itertools import combinations, product
from math import comb


def layer_forms(degree, weights):
    """Squared norm, l1 norm and adjacency form on the signed squarefree layers."""
    sizes = [2**k * comb(degree // 2, k) for k in range(len(weights))]
    norm = sum(size * w**2 for size, w in zip(sizes, weights))
    mass = sum(size * w for size, w in zip(sizes, weights))
    edges = 2 * sum(
        sizes[k] * (degree - 2*k) * weights[k] * weights[k+1]
        for k in range(len(weights) - 1)
    )
    return norm, mass, edges


def check_small_layers():
    """Reconstruct the forms by enumerating lattice vertices and neighbors."""
    dimension = 4
    weights = (7, 4, 3, 2)
    values = {}
    for k, weight in enumerate(weights):
        for occupied in combinations(range(dimension), k):
            for signs in product((-1, 1), repeat=k):
                vertex = [0] * dimension
                for index, sign in zip(occupied, signs):
                    vertex[index] = sign
                values[tuple(vertex)] = weight
    edges = 0
    for vertex, value in values.items():
        for i in range(dimension):
            for delta in (-1, 1):
                other = list(vertex)
                other[i] += delta
                edges += value * values.get(tuple(other), 0)
    explicit = sum(w**2 for w in values.values()), sum(values.values()), edges
    if explicit != layer_forms(2 * dimension, weights):
        raise ArithmeticError("layer enumeration disagrees with the closed formulas")


def main():
    check_small_layers()
    p = 365375409332725729550921208179070755120141565953
    n = 2**30
    coefficients = (100, 319, 917, 2287, 4541, 5335)
    weights = [c * 32768**(5-k) for k, c in enumerate(coefficients)]
    norm, mass, edges = layer_forms(n, weights)
    denominator = p * norm - mass**2
    numerator = p * edges - n * mass**2
    if denominator <= 0 or not 104498 * denominator < numerator < 104499 * denominator:
        raise ArithmeticError("production Rayleigh certificate failed")
    lower_bound = Fraction(numerator, denominator)
    print(f"Guaranteed largest nonprincipal eigenvalue >= {lower_bound}")
    print("Exact interval for the certificate: (104498, 104499)")

    weights = [32768**3, 2 * 32768**2, 3 * 32768, 2]
    norm, mass, edges = layer_forms(n, weights)
    threshold = 65536
    frequency_count = Fraction(p * (edges - threshold * norm), (n - threshold) * mass**2)
    coset_count = (frequency_count - 1) / n
    if not 125802243 < coset_count < 125802244:
        raise ArithmeticError("production coset-count certificate failed")
    print("At least 125802244 nonzero subgroup cosets have period > 65536.")


if __name__ == "__main__":
    main()
