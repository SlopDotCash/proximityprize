#!/usr/bin/env python3
"""Exact cancellation search over all complex dyadic roots for the quintic pencil theorem."""

from dataclasses import dataclass
from functools import cache, reduce
from itertools import combinations, product
from math import gcd, prod


# A form is an integer linear combination of root angles in Q[1/2]/Z.
# The last entry is the coefficient of the fixed angle 1/2 (negation of a root).
def add(*forms):
    return tuple(map(sum, zip(*forms)))


def subtract(a, b):
    return tuple(x-y for x, y in zip(a, b))


@dataclass
class Constraints:
    parity: list
    equalities: list
    inequalities: list
    sums: list


def quintic_constraints(pair_count, heavy_counts, use_first_sum=True):
    dimension = 15-pair_count  # One angle per ordinary site or top-pair label.
    zero = (0,)*(dimension+1)
    minus = (*zero[:-1], 1)
    board = Constraints([], [], [], [])

    def variable(parity):
        index = len(board.parity)
        board.parity.append(parity)
        return zero[:index]+(1,)+zero[index+1:]

    def parity_of(form):
        return sum(a*b for a, b in zip(form, board.parity)) % 2

    def total(forms):
        return add(zero, *forms)

    labels = [variable(1) if i < pair_count else None for i in range(3)]
    sites = []
    for i, heavy in enumerate(heavy_counts):
        ordinary = 5-2*(i < pair_count)
        sites.append(([variable(0) for _ in range(heavy)],
                      [variable(1) for _ in range(ordinary-heavy)]))
    assert len(board.parity) == dimension
    board.equalities.append(sites[0][0][0])  # Rotate by a heavy (even-exponent) site.
    if pair_count == 2:
        board.inequalities.append(subtract(labels[0], labels[1]))
    ordinary_sites = [x for parts in sites for shell in parts for x in shell]
    for a, b in combinations(ordinary_sites, 2):
        if parity_of(a) == parity_of(b):
            board.inequalities.append(subtract(a, b))
    root_products = []
    for i, (heavy, light) in enumerate(sites):
        factors = heavy+light
        if labels[i] is not None:
            factors = factors+[labels[i], minus]
        root_products.append(total(factors))
    board.inequalities.extend(subtract(a, b) for a, b in combinations(root_products, 2))

    # Reflection at each top pair, H_j-H_k+t_i(conj(L_j)-conj(L_k)) = 0.
    for i in range(pair_count):
        j, k = (i+1) % 3, (i+2) % 3
        hj, lj = sites[j]
        hk, lk = sites[k]
        board.sums.append(hj+[add(x, minus) for x in hk]
                          +[subtract(labels[i], x) for x in lj]
                          +[add(subtract(labels[i], x), minus) for x in lk])

    # Three/four-center equations, using both shells as possible test sets.
    for i, parts in enumerate(sites):
        j, k = (i+1) % 3, (i+2) % 3
        for p, tests in enumerate(parts):
            if len(tests) < 3:
                continue
            opposite_j, opposite_k = sites[j][1-p], sites[k][1-p]
            u, v = labels[j], labels[k]
            if u is None and v is None:
                board.sums.extend([opposite_j, opposite_k])
                continue
            if u is None or v is None:
                label = u if u is not None else v
                quartet_product = add(label, label)
            else:
                quartet_product = add(u, v, minus)
            if len(tests) == 4:
                board.equalities.append(subtract(total(tests), quartet_product))
                completed = tests
            else:
                assert len(tests) == 3
                completed = tests+[subtract(quartet_product, total(tests))]
            equation = [subtract(zero, x) for x in opposite_j]
            equation.extend(subtract(minus, x) for x in opposite_k)
            if u is not None:
                equation.extend(subtract(x, u) for x in completed)
            if v is not None:
                equation.extend(add(subtract(x, v), minus) for x in completed)
            board.sums.append(equation)

    # Leading, constant and quartic coefficients of the three monic quintics.
    if use_first_sum:
        parts = ([], [])
        for i, (heavy, light) in enumerate(sites):
            j, k = (i+1) % 3, (i+2) % 3
            for x in heavy+light:
                for term in (add(x, root_products[j]), add(x, root_products[k], minus)):
                    parts[parity_of(term)].append(term)
        board.sums.extend(parts)
    board.sums = sorted((sorted(row) for row in board.sums if row), key=len)
    assert all(len(row) % 2 == 0 for row in board.sums)
    return board


@dataclass(frozen=True)
class Chart:
    # D*x = constants / scale + sum free[i]*columns[i] in the dyadic circle.
    constants: tuple
    columns: tuple
    scale: int
    denominator: int

    @staticmethod
    def whole(dimension):
        return Chart((0,)*dimension, tuple(tuple(int(i == j) for i in range(dimension))
                                           for j in range(dimension)), 2, 1)

    def evaluate(self, form):
        columns = tuple(sum(a*b for a, b in zip(form, col)) for col in self.columns)
        constant = (sum(a*b for a, b in zip(form, self.constants))
                    +form[-1]*self.denominator*(self.scale//2)) % self.scale
        return constant, columns

    def impose(self, form):
        constant, coefficients = self.evaluate(form)
        common = reduce(gcd, coefficients, 0)
        if common == 0:
            if constant == 0:
                yield self
            return
        branches = common & -common
        weights = tuple(x//branches for x in coefficients)
        pivot = min((i for i, x in enumerate(weights) if x % 2),
                    key=lambda i: abs(weights[i]))
        q = weights[pivot]
        removed = self.columns[pivot]
        columns = tuple(tuple(q*x-w*y for x, y in zip(col, removed))
                        for i, (w, col) in enumerate(zip(weights, self.columns)) if i != pivot)
        denominator = q*self.denominator
        scale = self.scale*branches
        # The different lifts of (-constant / old_scale) under multiplication by branches.
        for k in range(branches):
            root = (-constant) % self.scale+k*self.scale
            constants = tuple((q*branches*x+y*root) % scale
                              for x, y in zip(self.constants, removed))
            sign = 1 if denominator > 0 else -1
            odd_common = reduce(gcd, (abs(x) for col in columns for x in col), abs(denominator))
            new_columns = tuple(tuple(sign*x//odd_common for x in col) for col in columns)
            multiplier = sign*pow(odd_common, -1, scale)
            reduced = tuple((x*multiplier) % scale for x in constants)
            common_scale = reduce(gcd, reduced, scale//2)
            yield Chart(tuple(x//common_scale for x in reduced), new_columns,
                        scale//common_scale, abs(denominator)//odd_common)

    def permits_parity(self, parity):
        def mask(values):
            return sum((v % 2) << i for i, v in enumerate(values))

        basis = {}

        def remainder(vector):
            while vector and vector.bit_length() in basis:
                vector ^= basis[vector.bit_length()]
            return vector

        for col in self.columns:
            vector = remainder(mask(col))
            if vector:
                basis[vector.bit_length()] = vector
        target = remainder(mask(parity))
        # M > scale, or M = scale. Every case needs at least 8 half-grid points.
        return target == 0 or (self.scale >= 8 and remainder(target ^ mask(self.constants)) == 0)


class CancellationSearch:
    def __init__(self, board):
        self.board = board
        self.nodes = 0
        self.largest_scale = 2

    def survives(self):
        charts = [Chart.whole(len(self.board.parity))]
        for equality in self.board.equalities:
            charts = [new for chart in charts for new in chart.impose(equality)]
        return any(self.visit(chart, self.board.sums) for chart in charts)

    def visit(self, chart, rows):
        self.nodes += 1
        self.largest_scale = max(self.largest_scale, chart.scale)
        if not chart.permits_parity(self.board.parity):
            return False
        evaluate = cache(chart.evaluate)
        for form in self.board.inequalities:
            constant, coefficients = evaluate(form)
            if constant == 0 and not any(coefficients):
                return False
        reduced = []
        choice = None
        fewest = float('inf')
        for row in rows:
            # Remove affine characters that are already identically opposite on the chart.
            groups = {}
            for form in row:
                constant, coefficients = evaluate(form)
                opposite = ((constant+chart.scale//2) % chart.scale, coefficients)
                if opposite in groups:
                    groups[opposite].pop()
                    if not groups[opposite]:
                        del groups[opposite]
                else:
                    groups.setdefault((constant, coefficients), []).append(form)
            remaining = [a for forms in groups.values() for a in forms]
            if not remaining:
                continue
            reduced.append(remaining)
            # Choosing a pivot from fewer rows affects only the search order.
            if fewest == 1 or len(remaining) > fewest+3:
                continue
            for i, a in enumerate(remaining):
                _, coefficients = evaluate(a)
                partners = {}
                for j, b in enumerate(remaining):
                    value = evaluate(b)
                    if value[1] != coefficients:
                        partners.setdefault(value, j)
                if len(partners) < fewest:
                    if not partners:
                        return False
                    fewest = len(partners)
                    choice = (len(reduced)-1, i, list(partners.values()))
                    if fewest == 1:
                        break
        if not reduced:
            return True
        row_index, first, partners = choice
        row = reduced[row_index]
        minus = (0,)*len(self.board.parity)+(1,)
        for second in partners:
            equality = subtract(subtract(row[first], row[second]), minus)
            residual = reduced.copy()
            residual[row_index] = [x for i, x in enumerate(row) if i not in (first, second)]
            if any(self.visit(new, residual) for new in chart.impose(equality)):
                return True
        return False


def finite_points(chart, order):
    """Enumerate a chart restricted to mu_order (for independent tiny controls)."""
    if order % chart.scale:
        return set()
    inverse = pow(chart.denominator, -1, order)
    return {tuple((c*(order//chart.scale)+sum(a*b for a, b in zip(t, coeffs)))*inverse % order
                  for c, coeffs in zip(chart.constants, zip(*chart.columns) if chart.columns
                                       else [()] * len(chart.constants)))
            for t in product(range(order), repeat=len(chart.columns))}


def controls():
    # Direct enumeration checks torsion splitting and exact parametrization, including odd pivots,
    # scalar/empty charts, nonprimitive equations, parity projections and inconsistent systems.
    forms = [(1, 0, 0), (0, -2, 1), (-3, 2, 1), (4, 2, 0), (2, -4, 1),
             (6, 4, 0), (-3, -1, 0), (0, 0, 1), (0, 0, 0)]
    for order, f, g in product((8, 16, 32), forms, forms):
        charts = [b for a in Chart.whole(2).impose(f) for b in a.impose(g)]
        expected = {(x, y) for x, y in product(range(order), repeat=2)
                    if all((h[0]*x+h[1]*y+h[2]*(order//2)) % order == 0 for h in (f, g))}
        covered = set()
        for chart in charts:
            points = finite_points(chart, order)
            assert covered.isdisjoint(points)
            covered.update(points)
            assert all(chart.permits_parity((x % 2, y % 2)) for x, y in points)
        assert covered == expected
    # Removing the first-sum minor leaves candidates in both difficult census rows.
    for pair_count, counts in ((1, (1, 3, 3)), (2, (1, 1, 3))):
        assert CancellationSearch(quintic_constraints(pair_count, counts, False)).survives()
    # Verify the degree-ten second-coefficient contradiction by evaluating its roots directly.
    prime = 65537
    w = pow(3, (prime-1)//32, prime)
    for ie, je, te in product((1, 3, 5), (7, 9, 11), ((1, 3, 5), (5, 7, 11))):
        a, b = pow(w, ie, prime), pow(w, je, prime)
        t = [pow(w, i, prime) for i in te]
        t_product = prod(t) % prime
        lam = t_product*pow(a*b, -1, prime) % prime
        lam_inv = pow(lam, -1, prime)
        roots = [a, b, lam*a % prime, lam*b % prime]
        e2 = sum(x*y for x, y in combinations(roots, 2)) % prime
        assert (e2-(1+lam+lam_inv)*t_product-lam*(a*a+a*b+b*b)) % prime == 0
        u = [pow(x, -1, prime) for x in t]
        entries = [(e2*x*x-(1+lam+lam_inv)*y) % prime for x, y in zip(u, t)]
        difference = sum(entries[i]*(u[(i+1) % 3]-u[(i+2) % 3]) for i in range(3)) % prime
        vandermonde = sum(u[i]**2*(u[(i+1) % 3]-u[(i+2) % 3]) for i in range(3)) % prime
        assert difference == vandermonde*lam*(a*a+a*b+b*b) % prime != 0


def main():
    controls()
    total = 0
    for pair_count in (1, 2):
        for counts in product((1, 3), repeat=3):
            if pair_count == 1 and (counts[0] != 1 or counts[1] > counts[2]):
                continue
            if pair_count == 2 and counts[0] > counts[1]:
                continue
            search = CancellationSearch(quintic_constraints(pair_count, counts))
            assert not search.survives(), (pair_count, counts)
            total += search.nodes
            print(pair_count, counts, 'charts', search.nodes, 'largest constant order', search.largest_scale)
    print('quintic cases exhausted across all dyadic orders, charts', total)


if __name__ == '__main__':
    main()
