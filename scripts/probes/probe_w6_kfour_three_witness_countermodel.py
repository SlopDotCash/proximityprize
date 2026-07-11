#!/usr/bin/env python3
"""Probe (W6 lane): the no-eight source-seven cross-triple signature problem.

Context (#466, rate-1/4, n=16, k=4, threshold 9, no-eight residual,
source core seven).  Regular outsiders carry signatures (T, E) with
T a 3-subset of the 7-coordinate source core and E a 3-subset of the
9-coordinate complement.  Proven cardinal constraints
(_HalfPredecessorRateQuarterKFourNoEightSevenRootFiber.lean /
 ...MultiplicityRefuted.lean):

  (P1) pair law:   |T_i cap T_j| + |E_i cap E_j| <= 4   (i != j)
  (P2) fiber cap:  at most 3 signatures share one root triple T
  (P3') balanced triple (i,j,k):  |E_i u E_j u E_k| <= 5 + |T_i n T_j n T_k|
        forces collinearity of the three polynomial points; three balanced
        witnesses on one pair give 5 points on one relevant line, which is
        impossible (pointsOn packing at threshold 9 vs global core cap 7).

The still-open "sharp assertion" is: any 13 signatures satisfying (P1)+(P2)
have a pair with >= 3 balanced witnesses.

This probe searches for a countermodel: 13 signatures with (P1)+(P2) and
ZERO balanced triples (which kills every balanced-witness route at once),
falling back to "every pair has <= 2 balanced witnesses" if zero-balanced
is infeasible.
"""

import itertools
import random
import sys

TRIPLES7 = [frozenset(c) for c in itertools.combinations(range(7), 3)]
TRIPLES9 = [frozenset(c) for c in itertools.combinations(range(9), 3)]


def pair_ok(sig1, sig2):
    (t1, e1), (t2, e2) = sig1, sig2
    return len(t1 & t2) + len(e1 & e2) <= 4


def balanced(sig1, sig2, sig3):
    (t1, e1), (t2, e2), (t3, e3) = sig1, sig2, sig3
    return len(e1 | e2 | e3) <= 5 + len(t1 & t2 & t3)


def check_family(sigs, verbose=False):
    """Return (pair_law_ok, fiber_ok, n_balanced_triples, max_witness)."""
    n = len(sigs)
    pair_law = all(
        pair_ok(sigs[i], sigs[j]) for i in range(n) for j in range(i + 1, n)
    )
    fibers = {}
    for t, _ in sigs:
        fibers[t] = fibers.get(t, 0) + 1
    fiber_ok = all(v <= 3 for v in fibers.values())
    nbal = 0
    witness = {}
    for i, j, k in itertools.combinations(range(n), 3):
        if balanced(sigs[i], sigs[j], sigs[k]):
            nbal += 1
            for a, b, c in ((i, j, k), (i, k, j), (j, k, i)):
                witness[(a, b)] = witness.get((a, b), 0) + 1
    maxw = max(witness.values()) if witness else 0
    if verbose and nbal:
        worst = sorted(witness.items(), key=lambda kv: -kv[1])[:5]
        print("  worst witness pairs:", worst)
    return pair_law, fiber_ok, nbal, maxw


# ---------------------------------------------------------------------------
# Step 0: reproduce the in-tree 13-signature model (sanity check).
IN_TREE_ROOT = [
    {1, 3, 4}, {0, 1, 3}, {0, 5, 6}, {0, 3, 6}, {1, 2, 4},
    {0, 4, 5}, {2, 3, 6}, {2, 5, 6}, {3, 4, 6}, {4, 5, 6},
    {0, 1, 6}, {1, 2, 4}, {0, 1, 2},
]
IN_TREE_MISSED = [
    {1, 2, 3}, {1, 5, 6}, {2, 3, 5}, {0, 1, 8}, {0, 4, 5},
    {0, 3, 6}, {3, 6, 7}, {1, 3, 4}, {2, 4, 8}, {1, 5, 7},
    {0, 4, 7}, {3, 7, 8}, {2, 6, 8},
]


def step0():
    sigs = [
        (frozenset(t), frozenset(e))
        for t, e in zip(IN_TREE_ROOT, IN_TREE_MISSED)
    ]
    res = check_family(sigs, verbose=True)
    print("in-tree 13-model: pair_law=%s fiber<=3=%s balanced_triples=%d "
          "max_witnesses_on_a_pair=%d" % res)


# ---------------------------------------------------------------------------
# Step 1: hand construction — E's = 12 lines of AG(2,3) (+1 extra),
# T's chosen to kill all balanced triples.

AG_LINES = []
# points of AG(2,3) = (x,y) in F3^2, numbered 3*x+y in 0..8
for a in range(3):
    for b in range(3):
        for c in range(3):
            if (a, b) == (0, 0):
                continue
            line = frozenset(
                3 * x + y
                for x in range(3) for y in range(3)
                if (a * x + b * y) % 3 == c
            )
            if line not in AG_LINES:
                AG_LINES.append(line)
assert len(AG_LINES) == 12, len(AG_LINES)


def classify_triples(lines):
    """For each 3-subset of the 12 AG lines, |union| in {6,7,9}."""
    hist = {}
    for i, j, k in itertools.combinations(range(len(lines)), 3):
        u = len(lines[i] | lines[j] | lines[k])
        hist[u] = hist.get(u, 0) + 1
    return hist


def step1_random_search(pop_target=13, tries=200000, seed=0):
    """Random/greedy: E's from AG(2,3) lines + extras, T's random distinct,
    then local repair: kill balanced triples by reassigning T's."""
    rng = random.Random(seed)
    lines = list(AG_LINES)
    best = None
    for attempt in range(tries):
        # missed sets: the 12 lines + (pop_target-12) random further triples
        missed = list(lines)
        while len(missed) < pop_target:
            e = rng.choice(TRIPLES9)
            missed.append(e)
        roots = rng.sample(TRIPLES7, pop_target)
        sigs = list(zip(roots, missed))
        # quick pair law check
        ok = all(
            pair_ok(sigs[i], sigs[j])
            for i in range(pop_target) for j in range(i + 1, pop_target)
        )
        if not ok:
            continue
        pl, fib, nbal, maxw = check_family(sigs)
        if best is None or nbal < best[0]:
            best = (nbal, maxw, sigs)
            if nbal == 0:
                print(f"  attempt {attempt}: ZERO balanced triples found")
                return sigs
    print(f"  best over random tries: balanced={best[0]} maxw={best[1]}")
    return None


def step1_targeted():
    """Deterministic: E's = 12 AG(2,3) lines + one extra; choose T's by
    backtracking so that no triple is balanced and pair law holds."""
    # For AG lines: |union of 3 lines| = 9 (parallel class), 7 (concurrent,
    # or 2 parallel + 1), 6 (triangle).  Balanced needs
    # |T triple cap| >= |union| - 5, so: union 6 -> need cap >= 1 forbidden;
    # union 7 -> cap >= 2 forbidden; union 9 -> cap >= 4 impossible anyway.
    missed = list(AG_LINES)
    extra = frozenset({0, 1, 2})  # a line already? ensure distinct signature
    # actually use a non-line triple for the 13th:
    extra = frozenset({0, 1, 3})
    assert extra not in AG_LINES
    missed.append(extra)
    n = len(missed)

    # precompute union sizes for triples of missed sets
    union3 = {}
    for i, j, k in itertools.combinations(range(n), 3):
        union3[(i, j, k)] = len(missed[i] | missed[j] | missed[k])
    inter2 = {}
    for i, j in itertools.combinations(range(n), 2):
        inter2[(i, j)] = len(missed[i] & missed[j])

    # backtracking over root triples
    roots = [None] * n
    used = {}

    def ok_prefix(m):
        # pair law + fiber for prefix of length m (last added index m-1)
        i = m - 1
        for j in range(i):
            if len(roots[i] & roots[j]) + inter2[(j, i)] > 4:
                return False
        if sum(1 for j in range(m) if roots[j] == roots[i]) > 3:
            return False
        for j, k in itertools.combinations(range(i), 2):
            u = union3[(j, k, i)]
            cap = len(roots[j] & roots[k] & roots[i])
            if u <= 5 + cap:
                return False
        return True

    order = list(TRIPLES7)

    def bt(m):
        if m == n:
            return True
        for t in order:
            roots[m] = t
            if ok_prefix(m + 1):
                if bt(m + 1):
                    return True
        roots[m] = None
        return False

    if bt(0):
        sigs = list(zip(roots, missed))
        pl, fib, nbal, maxw = check_family(sigs)
        print(f"  targeted: pair_law={pl} fiber={fib} balanced={nbal} "
              f"maxw={maxw}")
        if pl and fib and nbal == 0:
            return sigs
    else:
        print("  targeted backtracking failed with AG(2,3) missed sets")
    return None


def main():
    print("== step 0: in-tree model sanity ==")
    step0()
    print("== step 1: targeted zero-balanced construction ==")
    sigs = step1_targeted()
    if sigs is None:
        print("== step 1b: random search ==")
        sigs = step1_random_search()
    if sigs is not None:
        print("ZERO-BALANCED 13-SIGNATURE COUNTERMODEL:")
        for t, e in sigs:
            print("  T=%s  E=%s" % (sorted(t), sorted(e)))
        pl, fib, nbal, maxw = check_family(sigs, verbose=True)
        print("verify: pair_law=%s fiber=%s balanced=%d maxw=%d"
              % (pl, fib, nbal, maxw))
        sys.exit(0)
    print("no zero-balanced model found by these methods")
    sys.exit(1)


if __name__ == "__main__":
    main()
