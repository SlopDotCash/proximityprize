#!/usr/bin/env python3
"""Probe (W6 lane): exact CP-SAT decision for the no-eight source-seven
cross-triple signature problem (#466, rate-1/4, n=16, k=4).

Question 1 (refutes the "sharp assertion" if SAT): do 13 regular signatures
(T_j 3-subset of a 7-set, E_j 3-subset of a 9-set) exist with

  (P1) pair law       |T_i n T_j| + |E_i n E_j| <= 4       (i<j)
  (P2) fiber cap      no root triple used by 4 signatures
  (W2) every unordered pair {a,b} has at most 2 balanced witnesses c,
       where balanced(a,b,c) := |E_a u E_b u E_c| <= 5 + |T_a n T_b n T_c|

Question 2 (stronger): same with ZERO balanced triples.

Usage: probe_w6_kfour_witness_cpsat.py [pop] [maxw|zero] [timeout_s]
"""

import sys
import itertools

from ortools.sat.python import cp_model


def build(pop, mode, timeout_s, extra_tight=False):
    m = cp_model.CpModel()
    # incidence booleans
    y = [[m.NewBoolVar(f"y{j}_{q}") for q in range(7)] for j in range(pop)]
    x = [[m.NewBoolVar(f"x{j}_{p}") for p in range(9)] for j in range(pop)]
    for j in range(pop):
        m.Add(sum(y[j]) == 3)
        m.Add(sum(x[j]) == 3)

    def bool_and(vars_, name):
        v = m.NewBoolVar(name)
        m.AddBoolAnd(vars_).OnlyEnforceIf(v)
        m.AddBoolOr([w.Not() for w in vars_]).OnlyEnforceIf(v.Not())
        return v

    # pairwise intersections
    pairs = list(itertools.combinations(range(pop), 2))
    tpair = {}
    epair = {}
    for i, j in pairs:
        tvars = [bool_and([y[i][q], y[j][q]], f"t{i}_{j}_{q}")
                 for q in range(7)]
        evars = [bool_and([x[i][p], x[j][p]], f"e{i}_{j}_{p}")
                 for p in range(9)]
        tpair[(i, j)] = tvars
        epair[(i, j)] = evars
        # (P1) pair law
        m.Add(sum(tvars) + sum(evars) <= 4)

    # (P2) fiber cap: no 4 equal root triples.  same_ij <=> sum tpair = 3
    same = {}
    for i, j in pairs:
        s = m.NewBoolVar(f"same{i}_{j}")
        m.Add(sum(tpair[(i, j)]) == 3).OnlyEnforceIf(s)
        m.Add(sum(tpair[(i, j)]) <= 2).OnlyEnforceIf(s.Not())
        same[(i, j)] = s
    for quad in itertools.combinations(range(pop), 4):
        qpairs = [same[(a, b)] for a, b in itertools.combinations(quad, 2)]
        m.AddBoolOr([s.Not() for s in qpairs])

    # balanced reification per triple
    triples = list(itertools.combinations(range(pop), 3))
    bal = {}
    for i, j, k in triples:
        uni = [m.NewBoolVar(f"u{i}_{j}_{k}_{p}") for p in range(9)]
        for p in range(9):
            m.AddBoolOr([x[i][p], x[j][p], x[k][p]]).OnlyEnforceIf(uni[p])
            m.AddBoolAnd([x[i][p].Not(), x[j][p].Not(),
                          x[k][p].Not()]).OnlyEnforceIf(uni[p].Not())
        cap = [bool_and([y[i][q], y[j][q], y[k][q]], f"c{i}_{j}_{k}_{q}")
               for q in range(7)]
        b = m.NewBoolVar(f"bal{i}_{j}_{k}")
        m.Add(sum(uni) <= 5 + sum(cap)).OnlyEnforceIf(b)
        m.Add(sum(uni) >= 6 + sum(cap)).OnlyEnforceIf(b.Not())
        bal[(i, j, k)] = b

    if mode == "zero":
        for b in bal.values():
            m.Add(b == 0)
    else:
        # (W2): each unordered pair has <= 2 balanced witnesses
        for a, b_ in pairs:
            wit = []
            for c in range(pop):
                if c == a or c == b_:
                    continue
                key = tuple(sorted((a, b_, c)))
                wit.append(bal[key])
            m.Add(sum(wit) <= 2)

    # light symmetry breaking: fix signature 0, order signatures by their
    # 16-bit incidence integer (strictly increasing is wrong under relabel;
    # use non-strict lexicographic chain on rows to cut some symmetry).
    for q in range(3):
        m.Add(y[0][q] == 1)
    for q in range(3, 7):
        m.Add(y[0][q] == 0)
    for p in range(3):
        m.Add(x[0][p] == 1)
    for p in range(3, 9):
        m.Add(x[0][p] == 0)
    # value-based ordering on encoded signature integers
    enc = []
    for j in range(pop):
        v = m.NewIntVar(0, 2 ** 16 - 1, f"enc{j}")
        m.Add(v == sum(y[j][q] * (2 ** q) for q in range(7)) +
              sum(x[j][p] * (2 ** (7 + p)) for p in range(9)))
        enc.append(v)
    for j in range(pop - 1):
        m.Add(enc[j] < enc[j + 1])

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = timeout_s
    solver.parameters.num_search_workers = 4
    solver.parameters.log_search_progress = False
    status = solver.Solve(m)
    print(f"pop={pop} mode={mode}: {solver.StatusName(status)} "
          f"(walltime {solver.WallTime():.1f}s)")
    if status in (cp_model.FEASIBLE, cp_model.OPTIMAL):
        sigs = []
        for j in range(pop):
            T = sorted(q for q in range(7) if solver.Value(y[j][q]))
            E = sorted(p for p in range(9) if solver.Value(x[j][p]))
            sigs.append((T, E))
            print(f"  sig{j}: T={T} E={E}")
        verify(sigs, mode)
        return sigs
    return None


def verify(sigs, mode):
    n = len(sigs)
    fs = [(frozenset(t), frozenset(e)) for t, e in sigs]
    for i, j in itertools.combinations(range(n), 2):
        assert len(fs[i][0] & fs[j][0]) + len(fs[i][1] & fs[j][1]) <= 4, \
            (i, j)
    from collections import Counter
    fib = Counter(t for t, _ in fs)
    assert all(v <= 3 for v in fib.values())
    nbal = 0
    wit = Counter()
    for i, j, k in itertools.combinations(range(n), 3):
        if len(fs[i][1] | fs[j][1] | fs[k][1]) <= 5 + \
                len(fs[i][0] & fs[j][0] & fs[k][0]):
            nbal += 1
            wit[(i, j)] += 1
            wit[(i, k)] += 1
            wit[(j, k)] += 1
    maxw = max(wit.values()) if wit else 0
    print(f"  VERIFY: balanced={nbal} max_witnesses={maxw}")
    if mode == "zero":
        assert nbal == 0
    else:
        assert maxw <= 2


if __name__ == "__main__":
    pop = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    mode = sys.argv[2] if len(sys.argv) > 2 else "maxw"
    timeout = float(sys.argv[3]) if len(sys.argv) > 3 else 1200.0
    build(pop, mode, timeout)
