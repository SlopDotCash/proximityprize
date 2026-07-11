#!/usr/bin/env python3
"""Probe (W6 lane): source-six saturated-stratum witness search (#466,
rate-1/4, n=16, k=4, no-eight residual, source core SIX).

Saturated source-six outsiders have root triples T in the 6-coordinate
source core and missed 4-sets E in the 10-coordinate complement, with

  (Q1) pair law:  3 + |T_i n T_j| <= |E_i u E_j|
       (three_add_root_inter_le_sourceMissed_union_of_noEight_source_six)
  balanced(i,j,k) := |E_i u E_j u E_k| <= 6 + |T_i n T_j n T_k|
       (third_outside_mem_pointsOn_secant_of_sourceSix_root_missed_balance)
  five points on one line impossible
       (false_of_five_sourceSix_outsiders_root_missed_balance)

Question: do 14 saturated signatures exist with (Q1) and at most 2 balanced
witnesses per pair?  SAT refutes the source-six three-witness pigeonhole.

Usage: probe_w6_kfour_sourcesix_cpsat.py [pop] [timeout_s]
"""

import sys
import itertools

from ortools.sat.python import cp_model


def build(pop, timeout_s):
    m = cp_model.CpModel()
    y = [[m.NewBoolVar(f"y{j}_{q}") for q in range(6)] for j in range(pop)]
    x = [[m.NewBoolVar(f"x{j}_{p}") for p in range(10)] for j in range(pop)]
    for j in range(pop):
        m.Add(sum(y[j]) == 3)
        m.Add(sum(x[j]) == 4)

    def bool_and(vars_, name):
        v = m.NewBoolVar(name)
        m.AddBoolAnd(vars_).OnlyEnforceIf(v)
        m.AddBoolOr([w.Not() for w in vars_]).OnlyEnforceIf(v.Not())
        return v

    def bool_or(vars_, name):
        v = m.NewBoolVar(name)
        m.AddBoolOr(vars_).OnlyEnforceIf(v)
        m.AddBoolAnd([w.Not() for w in vars_]).OnlyEnforceIf(v.Not())
        return v

    pairs = list(itertools.combinations(range(pop), 2))
    for i, j in pairs:
        tvars = [bool_and([y[i][q], y[j][q]], f"t{i}_{j}_{q}")
                 for q in range(6)]
        evars = [bool_or([x[i][p], x[j][p]], f"e{i}_{j}_{p}")
                 for p in range(10)]
        # (Q1): 3 + |TnT| <= |EuE|
        m.Add(3 + sum(tvars) <= sum(evars))

    triples = list(itertools.combinations(range(pop), 3))
    bal = {}
    for i, j, k in triples:
        uni = [bool_or([x[i][p], x[j][p], x[k][p]], f"u{i}_{j}_{k}_{p}")
               for p in range(10)]
        cap = [bool_and([y[i][q], y[j][q], y[k][q]], f"c{i}_{j}_{k}_{q}")
               for q in range(6)]
        b = m.NewBoolVar(f"bal{i}_{j}_{k}")
        m.Add(sum(uni) <= 6 + sum(cap)).OnlyEnforceIf(b)
        m.Add(sum(uni) >= 7 + sum(cap)).OnlyEnforceIf(b.Not())
        bal[(i, j, k)] = b

    def B(a, b, c):
        return bal[tuple(sorted((a, b, c)))]

    for i, j in pairs:
        others = [c for c in range(pop) if c != i and c != j]
        m.Add(sum(B(i, j, c) for c in others) <= 2)

    # symmetry: fix signature 0; order encodings strictly
    for q in range(3):
        m.Add(y[0][q] == 1)
    for q in range(3, 6):
        m.Add(y[0][q] == 0)
    for p in range(4):
        m.Add(x[0][p] == 1)
    for p in range(4, 10):
        m.Add(x[0][p] == 0)
    enc = []
    for j in range(pop):
        v = m.NewIntVar(0, 2 ** 16 - 1, f"enc{j}")
        m.Add(v == sum(y[j][q] * (2 ** q) for q in range(6)) +
              sum(x[j][p] * (2 ** (6 + p)) for p in range(10)))
        enc.append(v)
    for j in range(pop - 1):
        m.Add(enc[j] < enc[j + 1])

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = timeout_s
    solver.parameters.num_search_workers = 4
    status = solver.Solve(m)
    print(f"source-six pop={pop}: {solver.StatusName(status)} "
          f"(walltime {solver.WallTime():.1f}s)")
    if status in (cp_model.FEASIBLE, cp_model.OPTIMAL):
        sigs = []
        for j in range(pop):
            T = sorted(q for q in range(6) if solver.Value(y[j][q]))
            E = sorted(p for p in range(10) if solver.Value(x[j][p]))
            sigs.append((T, E))
            print(f"  sig{j}: T={T} E={E}")
        verify(sigs)
        return sigs
    return None


def verify(sigs):
    n = len(sigs)
    fs = [(frozenset(t), frozenset(e)) for t, e in sigs]
    for i, j in itertools.combinations(range(n), 2):
        assert 3 + len(fs[i][0] & fs[j][0]) <= len(fs[i][1] | fs[j][1])
    from collections import Counter
    wit = Counter()
    nbal = 0
    for i, j, k in itertools.combinations(range(n), 3):
        if len(fs[i][1] | fs[j][1] | fs[k][1]) <= 6 + \
                len(fs[i][0] & fs[j][0] & fs[k][0]):
            nbal += 1
            wit[(i, j)] += 1
            wit[(i, k)] += 1
            wit[(j, k)] += 1
    maxw = max(wit.values()) if wit else 0
    print(f"  VERIFY: balanced={nbal} max_witnesses={maxw}")
    assert maxw <= 2


if __name__ == "__main__":
    pop = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    timeout = float(sys.argv[2]) if len(sys.argv) > 2 else 1800.0
    build(pop, timeout)
