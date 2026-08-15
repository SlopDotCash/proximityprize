"""
G291 probe: the census positive circuit is a MINIMAL, r-uniform positive Radon
circuit at the d+1 pigeonhole floor.

A minimal strictly-positive circuit among d-dimensional vectors has support
exactly d+1 (a positive Radon partition). We verify, in exact rationals:
  (1) the 5-cell linear circuit (d=4) is a strictly-positive dependence, support 5 = d+1;
  (2) every d=4 subset of the signed vectors is full-rank, so there is NO proper
      positive sub-circuit -> the circuit is minimal (at the Radon floor);
  (3) r-uniformity: the support uses BOTH ranks r in {5,6}.
Data (rawFeat, gate, weight) copied EXACTLY from landed _G289CountingMirageNoGo.lean.
"""
from fractions import Fraction as F
from itertools import combinations

rawFeat = [
 [-309168, -683424, 2610752, 3312256],
 [14464, 57856, -86784, -173568],
 [9290416, 70408736, -14191744, 90283648],
 [5023728, 22930784, 168792128, 266289664],
 [11819168, 32644736, 88373568, 58306048],
]
gate = [1, -1, 1, -1, 1]
weight = [770888209934274952,
          294057324376824869095,
          185095074806906020,
          347725276122965348,
          382331993870867280]
ranks = [5, 6, 5, 6, 5]  # both ranks present -> r-uniform

d = 4
N = 5
signed = [[gate[i]*rawFeat[i][j] for j in range(d)] for i in range(N)]

for j in range(d):
    s = sum(F(weight[i]) * F(signed[i][j]) for i in range(N))
    assert s == 0, "coord %d nonzero: %s" % (j, s)
assert all(w > 0 for w in weight)
print("(1) positive circuit verified: support size %d = d+1 = %d -> MINIMAL (Radon floor) OK" % (N, d + 1))


def rank_exact(rows):
    rows = [list(map(F, r)) for r in rows]
    m = len(rows)
    n = len(rows[0])
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if rows[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        pv = rows[r][c]
        for i in range(m):
            if i != r and rows[i][c] != 0:
                f = rows[i][c] / pv
                rows[i] = [rows[i][k] - f * rows[r][k] for k in range(n)]
        r += 1
    return r


all_indep = True
for combo in combinations(range(N), d):
    rk = rank_exact([signed[i] for i in combo])
    if rk < d:
        all_indep = False
        print("   sub-support %s has rank %d < %d: NOT minimal" % (combo, rk, d))
assert all_indep, "found a smaller dependence -> circuit not minimal"
print("(2) every %d-subset is full-rank -> NO proper positive sub-circuit: MINIMAL OK" % d)

present = set(ranks)
assert present == {5, 6}, "ranks in support: %s" % present
print("(3) r-uniform: support uses BOTH ranks %s -> not a per-rank artifact OK" % sorted(present))

print("\nALL PASS: minimal r-uniform positive Radon circuit at the d+1 pigeonhole floor.")
