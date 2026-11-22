#!/usr/bin/env python3
"""Count independently representable locator signatures and check the distance bounds."""

from collections import defaultdict
from functools import lru_cache
from itertools import product
from math import comb, prod

from probe_mu64_unit_lattice import PRIMES, require

ORDER = 512
EXPECTED = {
    128: 162556511019802226186357332579493573469778017126698240931258039194500582915358827449381351470947265625,
    64: 38023273840781151259760254827747883671613127455648285081482627480810178111853759865585931436920166015625,
}


def pivot(row):
    return next(i for i, value in enumerate(row) if value)


def subtract(row, multiple, basis_row):
    return tuple((a - multiple*b) % 3 for a, b in zip(row, basis_row))


def reduce_row(row, basis):
    for basis_row in basis:
        scale = row[pivot(basis_row)]
        if scale:
            row = subtract(row, scale, basis_row)
    return row


def extend(basis, row):
    row = reduce_row(row, basis)
    if not any(row):
        return basis
    first = pivot(row)
    if row[first] == 2:
        row = tuple((-v) % 3 for v in row)
    reduced = [subtract(b, b[first], row) if b[first] else b for b in basis]
    return tuple(sorted([*reduced, row], key=pivot))


def span(rows):
    basis = ()
    for row in rows:
        basis = extend(basis, row)
    return basis


def coordinates(row, indices):
    return tuple(row[j] for j in indices)


def linear_combination(coefficients, basis, dimension):
    if not basis:
        return (0,)*dimension
    return tuple(sum(a*b for a, b in zip(coefficients, col)) % 3 for col in zip(*basis))


def ternary_count(shift):
    """Sum 2^|J| over independent subfamilies of the 254 paired columns over F_3."""
    # Factor 1-z^d at d=2^a b as the product at b+t*(512/2^a).
    # Reflect odd primitive indices to the lower half; absolute values remove phase.
    phi = [[0]*ORDER for _ in range(ORDER//4)]
    for d in range(1, ORDER):
        step = d & -d
        for t in range(step):
            odd = d//step + t*(ORDER//step)
            phi[(min(odd, ORDER-odd)-1)//2][d] += 1
    columns = []
    for j in range(1, ORDER):
        mirror = (shift-j) % ORDER
        if j == shift or mirror < j:
            continue
        column = tuple((r[j]-r[(j-shift) % ORDER]) % 3 for r in phi)
        inverse = tuple((r[mirror]-r[-j % ORDER]) % 3 for r in phi)
        require(all((x+y) % 3 == 0 for x, y in zip(column, inverse)), 'reflection')
        if mirror == j:
            require(not any(column), 'fixed site')
        else:
            columns.append(column)
    require(len(columns) == 254, 'expected 254 pairs and two fixed sites')
    dimension = len(phi)
    supports = [frozenset(i for i, x in enumerate(col) if x) for col in columns]
    require(all(supports), 'unexpected zero column')

    def visit(indices, modulus):
        included = {j for j, support in enumerate(supports) if support.issubset(indices)}
        boundary = span(coordinates(col, indices) for j, col in enumerate(columns) if j not in included)
        width = len(indices)
        if modulus == 128:
            assigned = included
            order = indices
            prior = {(): 1}
        else:
            parts = defaultdict(list)
            for i in indices:
                odd = 2*i + 1
                parts[min(odd % (2*modulus), -odd % (2*modulus))].append(i)
            require(len(parts) == 2, 'binary split')
            left, right = map(tuple, parts.values())
            li, left_states = visit(left, 2*modulus)
            ri, right_states = visit(right, 2*modulus)
            assigned = included-li-ri
            order = left+right
            prior = {}
            for x, a in left_states.items():
                for y, b in right_states.items():
                    state = tuple(v+(0,)*len(right) for v in x) + tuple((0,)*len(left)+v for v in y)
                    prior[state] = a*b

        perm = tuple(indices.index(i) for i in order)
        undo = tuple(order.index(i) for i in indices)
        outgoing = span(coordinates(v, perm) for v in boundary)
        added = [coordinates(columns[j], order) for j in sorted(assigned)]
        ambient = span([*outgoing, *added, *(v for state in prior for v in state)])
        pivots = tuple(map(pivot, ambient))
        packed = lambda v: coordinates(v, pivots)
        for v in (*outgoing, *added):
            require(linear_combination(packed(v), ambient, width) == v, 'coordinate reconstruction')
        states = {span(packed(v) for v in state): count for state, count in prior.items()}
        require(sum(states.values()) == sum(prior.values()), 'distinct incoming states')
        for col in added:
            new = defaultdict(int, states)
            for state, count in states.items():
                larger = extend(state, packed(col))
                if len(larger) > len(state):
                    new[larger] += 2*count
            states = new
        # The exterior has dimension at most four for the two certified shifts.
        # Enumerate every vector of that space to intersect it with each state.
        boundary_small = tuple(map(packed, outgoing))
        require(len(boundary_small) <= 4, 'interface dimension')
        members = [linear_combination(c, boundary_small, len(pivots))
                   for c in product(range(3), repeat=len(boundary_small))]
        answer = defaultdict(int)
        for state, count in states.items():
            intersection = span(v for v in members if not any(reduce_row(v, state)))
            original = [coordinates(linear_combination(v, ambient, width), undo) for v in intersection]
            answer[span(original)] += count
        return included, answer

    included, final = visit(tuple(range(dimension)), 4)
    require(len(included) == 254 and set(final) == {()}, 'closed root')
    return final[()]


@lru_cache(maxsize=None)
def krawtchouk(j, d):
    return sum((-1)**r * comb(d, r)*comb(510-d, j-r)
               for r in range(j+1) if r <= d and j-r <= 510-d)


def distance_cap():
    """Degree-seven Delsarte certificate on the even distance grid at least 234."""
    roots = (234, 252, 254, 272, 274, 316, 318)
    f = lambda d: prod(root-d for root in roots)
    require(all(f(d) <= 0 for d in range(234, 511, 2)), 'off-diagonal sign')
    mass = 2**510
    # Orthogonality against the binomial weights recovers the expansion.
    # The identity on all 511 distances below checks the coefficients directly.
    from fractions import Fraction
    coefficients = [Fraction(sum(comb(510, d)*f(d)*krawtchouk(j, d) for d in range(511)),
                             mass*comb(510, j)) for j in range(8)]
    require(all(a >= 0 for a in coefficients) and coefficients[0] > 0, 'positive coefficients')
    require(all(sum(a*krawtchouk(j, d) for j, a in enumerate(coefficients)) == f(d)
                for d in range(511)), 'full polynomial identity')
    return f(0)//coefficients[0]


if __name__ == '__main__':
    q = prod(p-1 for p in PRIMES)
    for shift, expected in EXPECTED.items():
        count = ternary_count(shift)
        require(count == expected, 'independent-set count')
        fiber = (count+q-1)//q
        limit = (510-22)*(510+23)**2//602 if shift == 128 else distance_cap()
        require(fiber > limit, 'strict coding bound')
        print(f'shift {shift}: {count} signatures, fiber at least {fiber}, code cap {limit}')
