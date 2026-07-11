#!/usr/bin/env python3
"""Probe (W6 lane): FULL mixture model for the no-eight source-seven branch
(#466, rate-1/4, n=16, k=4): regular AND long outsiders together.

Signatures (T_j, E_j) with T_j subset of the 7-coordinate source core and
E_j subset of the 9-coordinate complement, |E_j| <= |T_j| <= 3
(sourceSeven_missed_card_le_root_card, sourceSeven_root_card_le_three).
Regular type = (|T|,|E|) = (3,3).

Sound cardinal shadows of proven in-tree RS geometry (all-outsider forms):

  (P1)  pair law  2 + |T_i n T_j| <= |E_i u E_j|
        (two_add_root_inter_le_missed_union_of_noEight_source_seven)
  (P2)  regular fiber cap: no 4 regular signatures share a root triple
        (regularRootFiber_card_le_three_of_noEight_source_seven)
  bal(i,j,k) := |E_i u E_j u E_k| <= 5 + |T_i n T_j n T_k|
        (third_outside_mem_pointsOn_secant_of_root_missed_balance,
         all-outsider version, no cardinality hypotheses)
  (W2)  <= 2 balanced witnesses per pair
        (false_of_five_outsiders_root_missed_balance)
  (CL)  bal(i,j,k) & bal(i,j,l) -> bal on every triple of {i,j,k,l}
        (four points determine the same secant line)
  (EQ)  bal(i,j,k) -> pairwise T-intersections equal as sets and pairwise
        E-unions equal as sets (fullAgreement_inter_eq_jointCore on the
        common line)
  (T3)  bal(i,j,k) -> for each inner pair |T n T| + |E n E| >=
        |E_a| + |E_b| - 3   (three points force line core >= 6)
  (T4)  two witnesses on a pair -> all six pairs of the four points have
        |T n T| + |E n E| = |E_a| + |E_b| - 2  (four points force core 7)
  (X1)  cross-secant core cap: the secant of any two outsiders is a
        relevant line whose core is exactly (T_a n T_b) u (V \\ (E_a u E_b));
        distinct relevant lines have cores meeting in <= 3
        (relevant_jointCore_inter_card_le_three_of_distinct).  Hence for
        pairs {a,b}, {c,d} sharing at most one index, UNLESS the involved
        points are collinear (equivalent to the balance predicate),
        |T_a n T_b n T_c n T_d| + (9 - |E_a u E_b u E_c u E_d|) <= 3.

Question: does a 13-signature mixture exist?  UNSAT closes the whole
source-seven no-eight branch combinatorially (its formalization then being
a finite counting theorem); SAT localizes the surviving configurations.

Usage: probe_w6_kfour_mixture_cpsat.py [pop] [timeout_s]
"""

import sys
import itertools

from ortools.sat.python import cp_model


def build(pop, timeout_s):
    m = cp_model.CpModel()
    y = [[m.NewBoolVar(f"y{j}_{q}") for q in range(7)] for j in range(pop)]
    x = [[m.NewBoolVar(f"x{j}_{p}") for p in range(9)] for j in range(pop)]
    tsz = [m.NewIntVar(0, 3, f"tsz{j}") for j in range(pop)]
    esz = [m.NewIntVar(0, 3, f"esz{j}") for j in range(pop)]
    reg = [m.NewBoolVar(f"reg{j}") for j in range(pop)]
    for j in range(pop):
        m.Add(sum(y[j]) == tsz[j])
        m.Add(sum(x[j]) == esz[j])
        m.Add(esz[j] <= tsz[j])
        # regular <=> |E| = 3 (then |T| = 3 forced by esz<=tsz<=3)
        m.Add(esz[j] == 3).OnlyEnforceIf(reg[j])
        m.Add(esz[j] <= 2).OnlyEnforceIf(reg[j].Not())

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
    tint, eint, euni = {}, {}, {}
    for i, j in pairs:
        tint[(i, j)] = [bool_and([y[i][q], y[j][q]], f"ti{i}_{j}_{q}")
                        for q in range(7)]
        eint[(i, j)] = [bool_and([x[i][p], x[j][p]], f"ei{i}_{j}_{p}")
                        for p in range(9)]
        euni[(i, j)] = [bool_or([x[i][p], x[j][p]], f"eu{i}_{j}_{p}")
                        for p in range(9)]
        # (P1)
        m.Add(2 + sum(tint[(i, j)]) <= sum(euni[(i, j)]))

    # (P2) regular fiber cap: no 4 regulars with identical T
    same = {}
    for i, j in pairs:
        s = m.NewBoolVar(f"same{i}_{j}")
        # same <=> T_i = T_j as sets (pointwise equality)
        eqs = []
        for q in range(7):
            e = m.NewBoolVar(f"teq{i}_{j}_{q}")
            m.Add(y[i][q] == y[j][q]).OnlyEnforceIf(e)
            m.Add(y[i][q] != y[j][q]).OnlyEnforceIf(e.Not())
            eqs.append(e)
        m.AddBoolAnd(eqs).OnlyEnforceIf(s)
        m.AddBoolOr([e.Not() for e in eqs]).OnlyEnforceIf(s.Not())
        same[(i, j)] = s
    for quad in itertools.combinations(range(pop), 4):
        lits = [same[(a, b)].Not()
                for a, b in itertools.combinations(quad, 2)]
        lits += [reg[a].Not() for a in quad]
        m.AddBoolOr(lits)

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

    for i, j in pairs:
        others = [c for c in range(pop) if c != i and c != j]
        # (W2)
        m.Add(sum(B(i, j, c) for c in others) <= 2)
        # (CL) + (T4)
        for k, l in itertools.combinations(others, 2):
            pre = [B(i, j, k), B(i, j, l)]
            m.AddBoolAnd([B(i, k, l)]).OnlyEnforceIf(pre)
            m.AddBoolAnd([B(j, k, l)]).OnlyEnforceIf(pre)
            for a, b in itertools.combinations(sorted((i, j, k, l)), 2):
                m.Add(sum(tint[(a, b)]) + sum(eint[(a, b)]) ==
                      esz[a] + esz[b] - 2).OnlyEnforceIf(pre)

    # (EQ) + (T3)
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
        for (a, bb), pp in ((pij, pij), (pik, pik), (pjk, pjk)):
            m.Add(sum(tint[pp]) + sum(eint[pp]) >=
                  esz[pp[0]] + esz[pp[1]] - 3).OnlyEnforceIf(b)

    # symmetry: order by (esz desc, encoding) is unsound with types; use
    # encoding order only within nothing — keep plain encoding order, which
    # is a pure index permutation and always sound.
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
    print(f"mixture pop={pop}: {solver.StatusName(status)} "
          f"(walltime {solver.WallTime():.1f}s)")
    if status in (cp_model.FEASIBLE, cp_model.OPTIMAL):
        sigs = []
        for j in range(pop):
            T = sorted(q for q in range(7) if solver.Value(y[j][q]))
            E = sorted(p for p in range(9) if solver.Value(x[j][p]))
            sigs.append((T, E))
            print(f"  sig{j}: T={T} E={E} "
                  f"{'REG' if solver.Value(reg[j]) else 'long'}")
        verify(sigs)
        return sigs
    return None


def verify(sigs):
    n = len(sigs)
    fs = [(frozenset(t), frozenset(e)) for t, e in sigs]
    for t, e in fs:
        assert len(e) <= len(t) <= 3
    for i, j in itertools.combinations(range(n), 2):
        assert 2 + len(fs[i][0] & fs[j][0]) <= len(fs[i][1] | fs[j][1])
    from collections import Counter
    fib = Counter(t for t, e in fs if len(e) == 3)
    assert all(v <= 3 for v in fib.values())

    def balanced(i, j, k):
        return len(fs[i][1] | fs[j][1] | fs[k][1]) <= 5 + \
            len(fs[i][0] & fs[j][0] & fs[k][0])

    wit = Counter()
    nbal = 0
    for i, j, k in itertools.combinations(range(n), 3):
        if balanced(i, j, k):
            nbal += 1
            wit[(i, j)] += 1
            wit[(i, k)] += 1
            wit[(j, k)] += 1
            tij = fs[i][0] & fs[j][0]
            assert tij == fs[i][0] & fs[k][0] == fs[j][0] & fs[k][0]
            uij = fs[i][1] | fs[j][1]
            assert uij == fs[i][1] | fs[k][1] == fs[j][1] | fs[k][1]
            for a, b in ((i, j), (i, k), (j, k)):
                s = len(fs[a][0] & fs[b][0]) + len(fs[a][1] & fs[b][1])
                assert s >= len(fs[a][1]) + len(fs[b][1]) - 3
    maxw = max(wit.values()) if wit else 0
    print(f"  VERIFY OK: balanced={nbal} max_witnesses={maxw}")
    assert maxw <= 2


if __name__ == "__main__":
    pop = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    timeout = float(sys.argv[2]) if len(sys.argv) > 2 else 3000.0
    build(pop, timeout)
