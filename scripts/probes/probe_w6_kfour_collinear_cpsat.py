#!/usr/bin/env python3
"""Probe (W6 lane): CP-SAT for the no-eight source-seven regular stratum with
the FULL derived collinearity geometry (#466, rate-1/4, n=16, k=4).

Balanced regular triples are exactly collinear triples (both directions
derivable from in-tree theorems: balanced => third point on secant
[_...NoEightSevenRootFiber.third_regular_mem_pointsOn_secant_of_root_missed_balance];
conversely three points on one relevant line have pairwise full-agreement
intersections equal to the line core, which forces the balance inequality).
Hence the following are all sound cardinal shadows of proven RS geometry:

  (P1)  pair law |T_i n T_j| + |E_i n E_j| <= 4
  (P2)  fiber cap: no 4 signatures share a root triple
  (CL)  closure: bal(i,j,k) & bal(i,j,l) -> bal(i,k,l) & bal(j,k,l)
  (W2)  every pair has <= 2 balanced witnesses (5 points on a line are
        impossible at threshold 9 under global core cap 7)
  (EQ)  bal(i,j,k) -> pairwise root intersections are EQUAL as sets and
        pairwise missed unions are EQUAL as sets
  (T3)  bal(i,j,k) -> each inner pair has |T n T| + |E n E| in {3, 4}
        (line core is 6 or 7)
  (T4)  bal(i,j,k) & bal(i,j,l) -> all six pairs of {i,j,k,l} have
        |T n T| + |E n E| = 4 (a 4-point line has core exactly 7)

Question: does a 13-signature model satisfying ALL of the above exist?
SAT -> even the full currently-derived collinearity geometry cannot close
the regular stratum by cardinal counting.  UNSAT -> the regular-saturated
branch is closed by finite combinatorics.

Usage: probe_w6_kfour_collinear_cpsat.py [pop] [timeout_s]
"""

import sys
import itertools

from ortools.sat.python import cp_model


def build(pop, timeout_s):
    m = cp_model.CpModel()
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

    def bool_or(vars_, name):
        v = m.NewBoolVar(name)
        m.AddBoolOr(vars_).OnlyEnforceIf(v)
        m.AddBoolAnd([w.Not() for w in vars_]).OnlyEnforceIf(v.Not())
        return v

    pairs = list(itertools.combinations(range(pop), 2))
    tint = {}   # tint[(i,j)][q] : q in T_i n T_j
    eint = {}   # eint[(i,j)][p] : p in E_i n E_j
    euni = {}   # euni[(i,j)][p] : p in E_i u E_j
    for i, j in pairs:
        tint[(i, j)] = [bool_and([y[i][q], y[j][q]], f"ti{i}_{j}_{q}")
                        for q in range(7)]
        eint[(i, j)] = [bool_and([x[i][p], x[j][p]], f"ei{i}_{j}_{p}")
                        for p in range(9)]
        euni[(i, j)] = [bool_or([x[i][p], x[j][p]], f"eu{i}_{j}_{p}")
                        for p in range(9)]
        # (P1)
        m.Add(sum(tint[(i, j)]) + sum(eint[(i, j)]) <= 4)

    # (P2) fiber cap
    same = {}
    for i, j in pairs:
        s = m.NewBoolVar(f"same{i}_{j}")
        m.Add(sum(tint[(i, j)]) == 3).OnlyEnforceIf(s)
        m.Add(sum(tint[(i, j)]) <= 2).OnlyEnforceIf(s.Not())
        same[(i, j)] = s
    for quad in itertools.combinations(range(pop), 4):
        m.AddBoolOr(
            [same[(a, b)].Not()
             for a, b in itertools.combinations(quad, 2)])

    # balanced booleans
    triples = list(itertools.combinations(range(pop), 3))
    bal = {}
    for i, j, k in triples:
        uni = [bool_or([x[i][p], x[j][p], x[k][p]], f"u{i}_{j}_{k}_{p}")
               for p in range(9)]
        cap = [bool_and([y[i][q], y[j][q], y[k][q]], f"c{i}_{j}_{k}_{q}")
               for q in range(7)]
        b = m.NewBoolVar(f"bal{i}_{j}_{k}")
        m.Add(sum(uni) <= 5 + sum(cap)).OnlyEnforceIf(b)
        m.Add(sum(uni) >= 6 + sum(cap)).OnlyEnforceIf(b.Not())
        bal[(i, j, k)] = b

    def B(a, b, c):
        return bal[tuple(sorted((a, b, c)))]

    # (CL) closure + (T4) four-point tightness
    for i, j in pairs:
        others = [c for c in range(pop) if c != i and c != j]
        for k, l in itertools.combinations(others, 2):
            pre = [B(i, j, k), B(i, j, l)]
            m.AddBoolAnd([B(i, k, l)]).OnlyEnforceIf(pre)
            m.AddBoolAnd([B(j, k, l)]).OnlyEnforceIf(pre)
            for a, b in itertools.combinations(sorted((i, j, k, l)), 2):
                m.Add(sum(tint[(a, b)]) + sum(eint[(a, b)]) == 4
                      ).OnlyEnforceIf(pre)

    # (W2)
    for i, j in pairs:
        others = [c for c in range(pop) if c != i and c != j]
        m.Add(sum(B(i, j, c) for c in others) <= 2)

    # (EQ) + (T3) on balanced triples
    for i, j, k in triples:
        b = bal[(i, j, k)]
        pij, pik, pjk = tuple(sorted((i, j))), tuple(sorted((i, k))), \
            tuple(sorted((j, k)))
        for q in range(7):
            m.Add(tint[pij][q] == tint[pik][q]).OnlyEnforceIf(b)
            m.Add(tint[pij][q] == tint[pjk][q]).OnlyEnforceIf(b)
        for p in range(9):
            m.Add(euni[pij][p] == euni[pik][p]).OnlyEnforceIf(b)
            m.Add(euni[pij][p] == euni[pjk][p]).OnlyEnforceIf(b)
        m.Add(sum(tint[pij]) + sum(eint[pij]) >= 3).OnlyEnforceIf(b)

    # symmetry: fix signature 0 to the minimum, order encodings
    for q in range(3):
        m.Add(y[0][q] == 1)
    for q in range(3, 7):
        m.Add(y[0][q] == 0)
    for p in range(3):
        m.Add(x[0][p] == 1)
    for p in range(3, 9):
        m.Add(x[0][p] == 0)
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
    solver.parameters.num_search_workers = 6
    status = solver.Solve(m)
    print(f"pop={pop} full-geometry: {solver.StatusName(status)} "
          f"(walltime {solver.WallTime():.1f}s)")
    if status in (cp_model.FEASIBLE, cp_model.OPTIMAL):
        sigs = []
        for j in range(pop):
            T = sorted(q for q in range(7) if solver.Value(y[j][q]))
            E = sorted(p for p in range(9) if solver.Value(x[j][p]))
            sigs.append((T, E))
            print(f"  sig{j}: T={T} E={E}")
        verify(sigs)
        return sigs
    return None


def verify(sigs):
    n = len(sigs)
    fs = [(frozenset(t), frozenset(e)) for t, e in sigs]
    for i, j in itertools.combinations(range(n), 2):
        assert len(fs[i][0] & fs[j][0]) + len(fs[i][1] & fs[j][1]) <= 4
    from collections import Counter
    fib = Counter(t for t, _ in fs)
    assert all(v <= 3 for v in fib.values())

    def balanced(i, j, k):
        return len(fs[i][1] | fs[j][1] | fs[k][1]) <= 5 + \
            len(fs[i][0] & fs[j][0] & fs[k][0])

    nbal, wit = 0, Counter()
    for i, j, k in itertools.combinations(range(n), 3):
        if balanced(i, j, k):
            nbal += 1
            wit[(i, j)] += 1
            wit[(i, k)] += 1
            wit[(j, k)] += 1
            # EQ check
            tij = fs[i][0] & fs[j][0]
            tik = fs[i][0] & fs[k][0]
            tjk = fs[j][0] & fs[k][0]
            assert tij == tik == tjk, (i, j, k)
            uij = fs[i][1] | fs[j][1]
            uik = fs[i][1] | fs[k][1]
            ujk = fs[j][1] | fs[k][1]
            assert uij == uik == ujk, (i, j, k)
            s = len(tij) + len(fs[i][1] & fs[j][1])
            assert s in (3, 4), (i, j, k, s)
    maxw = max(wit.values()) if wit else 0
    # closure check
    for i, j in itertools.combinations(range(n), 2):
        others = [c for c in range(n) if c not in (i, j)]
        for k, l in itertools.combinations(others, 2):
            if balanced(i, j, k) and balanced(i, j, l):
                assert balanced(i, k, l) and balanced(j, k, l)
                for a, b in itertools.combinations((i, j, k, l), 2):
                    aa, bb = min(a, b), max(a, b)
                    assert len(fs[aa][0] & fs[bb][0]) + \
                        len(fs[aa][1] & fs[bb][1]) == 4
    print(f"  VERIFY OK: balanced={nbal} max_witnesses={maxw}")


if __name__ == "__main__":
    pop = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    timeout = float(sys.argv[2]) if len(sys.argv) > 2 else 3000.0
    build(pop, timeout)
