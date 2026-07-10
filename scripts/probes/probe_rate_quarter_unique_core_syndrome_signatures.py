#!/usr/bin/env python3
"""Exact CSP for the saturated unique-eight-core syndrome signatures.

This probe asks whether the currently proved combinatorial and syndrome-graph
constraints already contradict eight regular outsiders.  It models:

* eight root triples on the source core;
* eight distinct missed edges on the eight-coordinate complement;
* the saturated syndrome conclusion that the missed-edge graph is 2-regular;
* the unique-core pair budget |T_i intersect T_j| + |E_i intersect E_j| <= 3;
* root-triple multiplicity at most two; and
* at least four off-distinguished-secant signatures, whose missed edges lie
  in the fixed five-coordinate petal and whose roots avoid the fixed overlap.

A satisfying model is an abstract signature certificate only.  It does not
assert Reed--Solomon polynomial realizability.  UNSAT would mean the landed
cardinal and syndrome constraints close the residual by themselves.
"""

from argparse import ArgumentParser
from itertools import combinations

from z3 import And, Bool, If, Not, Or, PbEq, PbGe, Solver, sat


SOURCE_SIZE = 8
COMPLEMENT_SIZE = 8
SIGNATURES = 8
PETAL = frozenset(range(5))


def exactly(bits, count):
    return PbEq([(bit, 1) for bit in bits], count)


def build_solver(overlap_size=2, timeout_ms=0):
    solver = Solver()
    if timeout_ms:
        solver.set(timeout=timeout_ms)

    root = [[Bool(f"root_{s}_{i}") for i in range(SOURCE_SIZE)]
            for s in range(SIGNATURES)]
    edge = [[Bool(f"edge_{s}_{i}") for i in range(COMPLEMENT_SIZE)]
            for s in range(SIGNATURES)]
    off = [Bool(f"off_{s}") for s in range(SIGNATURES)]

    for s in range(SIGNATURES):
        solver.add(exactly(root[s], 3))
        solver.add(exactly(edge[s], 2))

    # Eight distinct edges and saturation of the degree-two chord bound.
    for s, t in combinations(range(SIGNATURES), 2):
        solver.add(Or(*[edge[s][i] != edge[t][i]
                        for i in range(COMPLEMENT_SIZE)]))
    for i in range(COMPLEMENT_SIZE):
        solver.add(exactly([edge[s][i] for s in range(SIGNATURES)], 2))

    # Unique-core secant budget for every two regular outsiders.
    for s, t in combinations(range(SIGNATURES), 2):
        intersection = [If(And(root[s][i], root[t][i]), 1, 0)
                        for i in range(SOURCE_SIZE)]
        intersection += [If(And(edge[s][i], edge[t][i]), 1, 0)
                         for i in range(COMPLEMENT_SIZE)]
        solver.add(sum(intersection) <= 3)

    # No root triple may occur three times.
    for a, b, c in combinations(range(SIGNATURES), 3):
        eq_ab = And(*[root[a][i] == root[b][i]
                      for i in range(SOURCE_SIZE)])
        eq_ac = And(*[root[a][i] == root[c][i]
                      for i in range(SOURCE_SIZE)])
        solver.add(Not(And(eq_ab, eq_ac)))

    # Off-secant signatures avoid the overlap and miss only in the petal.
    overlap = frozenset(range(overlap_size))
    for s in range(SIGNATURES):
        for i in overlap:
            solver.add(Or(Not(off[s]), Not(root[s][i])))
        for i in range(COMPLEMENT_SIZE):
            if i not in PETAL:
                solver.add(Or(Not(off[s]), Not(edge[s][i])))
    solver.add(PbGe([(flag, 1) for flag in off], 4))

    # Symmetry breaking: put the first signature off the secant and give it
    # the first available root triple and petal edge.
    solver.add(off[0])
    for i in range(SOURCE_SIZE):
        solver.add(root[0][i] == (i in range(overlap_size, overlap_size + 3)))
    for i in range(COMPLEMENT_SIZE):
        solver.add(edge[0][i] == (i in (0, 1)))

    return solver, root, edge, off


def selected(model, row):
    return tuple(i for i, bit in enumerate(row)
                 if bool(model.eval(bit, model_completion=True)))


def verify(rows, overlap_size):
    assert len(rows) == SIGNATURES
    roots = [frozenset(row["root"]) for row in rows]
    edges = [frozenset(row["edge"]) for row in rows]
    assert all(len(root) == 3 for root in roots)
    assert all(len(edge) == 2 for edge in edges)
    assert len(set(edges)) == SIGNATURES
    assert all(sum(i in edge for edge in edges) == 2
               for i in range(COMPLEMENT_SIZE))
    assert all(len(roots[s] & roots[t]) + len(edges[s] & edges[t]) <= 3
               for s, t in combinations(range(SIGNATURES), 2))
    assert all(sum(root == candidate for candidate in roots) <= 2
               for root in set(roots))
    overlap = frozenset(range(overlap_size))
    off_rows = [row for row in rows if row["off"]]
    assert len(off_rows) >= 4
    assert all(not (frozenset(row["root"]) & overlap) and
               frozenset(row["edge"]) <= PETAL for row in off_rows)


def run(overlap_size=2, timeout_ms=0):
    solver, root, edge, off = build_solver(overlap_size, timeout_ms)
    status = solver.check()
    print({"status": str(status), "overlap_size": overlap_size})
    if status != sat:
        return status
    model = solver.model()
    rows = [{
        "signature": s,
        "root": selected(model, root[s]),
        "edge": selected(model, edge[s]),
        "off": bool(model.eval(off[s], model_completion=True)),
    } for s in range(SIGNATURES)]
    verify(rows, overlap_size)
    for row in rows:
        print(row)
    return status


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("--overlap-size", type=int, choices=(0, 1, 2), default=2)
    parser.add_argument("--timeout-ms", type=int, default=0)
    args = parser.parse_args()
    raise SystemExit(0 if run(args.overlap_size, args.timeout_ms) == sat else 1)
