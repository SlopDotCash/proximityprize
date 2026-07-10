#!/usr/bin/env python3
"""Exact extremal census for the overlap-three root-block matching.

A root block of size k-1 in a petal of size k+1 is represented by its
two-element complement, hence by an edge of K_{k+1}.  Compatibility is
injective in each coordinate.  The unequal-slope Plucker argument forbids two
chosen pairs whose left and right edges are both adjacent.
"""

import argparse
import itertools

import z3


def solve(v: int) -> None:
    edges = list(itertools.combinations(range(v), 2))
    m = len(edges)
    adjacent = [[len(set(e) & set(f)) == 1 for f in edges] for e in edges]
    opt = z3.Optimize()
    x = [[z3.Bool(f"x_{i}_{j}") for j in range(m)] for i in range(m)]

    for i in range(m):
        opt.add(z3.PbLe([(x[i][j], 1) for j in range(m)], 1))
    for j in range(m):
        opt.add(z3.PbLe([(x[i][j], 1) for i in range(m)], 1))

    for i in range(m):
        for ip in range(i + 1, m):
            if not adjacent[i][ip]:
                continue
            for j in range(m):
                for jp in range(j + 1, m):
                    if adjacent[j][jp]:
                        opt.add(z3.Or(z3.Not(x[i][j]), z3.Not(x[ip][jp])))
                        opt.add(z3.Or(z3.Not(x[i][jp]), z3.Not(x[ip][j])))

    total = z3.Sum([z3.If(x[i][j], 1, 0) for i in range(m) for j in range(m)])
    opt.maximize(total)
    assert opt.check() == z3.sat
    model = opt.model()
    selected = [
        (edges[i], edges[j])
        for i in range(m)
        for j in range(m)
        if z3.is_true(model.eval(x[i][j]))
    ]
    print(f"v={v} edges={m} maximum={model.eval(total)} target_4k={4 * (v - 1)}")
    print("selected=" + " ".join(f"{a}->{b}" for a, b in selected))


def construct(m: int) -> None:
    if m % 2 == 0:
        raise ValueError("the a+b,a-b construction requires odd m")
    v = 2 * m
    selected = []
    for a in range(m):
        for b in range(m):
            left = (a, m + b)
            right = ((a + b) % m, m + ((a - b) % m))
            selected.append((left, right))
    assert len({left for left, _ in selected}) == m * m
    assert len({right for _, right in selected}) == m * m
    for i, (left, right) in enumerate(selected):
        for left2, right2 in selected[i + 1 :]:
            assert not (set(left) & set(left2) and set(right) & set(right2))
    print(
        f"construction m={m} v={v} size={len(selected)} "
        f"target_4k={4 * (v - 1)} excess={len(selected) - 4 * (v - 1)}"
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("v", type=int, nargs="?")
    parser.add_argument("--construct", type=int, metavar="ODD_M")
    args = parser.parse_args()
    if args.construct is not None:
        construct(args.construct)
    elif args.v is not None:
        solve(args.v)
    else:
        parser.error("provide v or --construct ODD_M")
