"""
Work out the EXACT inclusion-exclusion arithmetic for
  N(n) = |union over 15 matchings M of  A_M|,
where A_M = { t : Z/n^6 : for each pair (i,j) in M, t_i - t_j = n/2 mod n }.

|A_M| = n^3 (choose 3 free, 3 forced).
We want N(n) = 15 n^3 - 45 n^2 + 40 n.

Strategy: classify the OVERLAPS A_M cap A_M'. Two matchings M, M' of {0..5}.
Their "union graph" (edges from both) decomposes into paths/cycles. The constraint
t_i - t_j = n/2 along every edge. Along a path of length L edges the endpoints are
forced; along an EVEN cycle constraints are consistent (alternating), along ODD cycle
they may be inconsistent (but with the antipodal value n/2, two edges i-j and j-i give
t_i - t_j = n/2 AND t_j - t_i = n/2 => n = 0 mod n... for a 2-cycle it's the same edge).
The combined constraint graph on 6 vertices: each connected component of size s with
the antipodal (difference = n/2) constraints has solution count = n if consistent
(the n choices for one representative, n/2 propagates, must be consistent around cycles),
0 if inconsistent. A union of two perfect matchings is a disjoint union of EVEN cycles
(alternating M / M'). The difference-n/2 constraint around an even cycle of length 2L:
going around, total difference = L*(n/2) - L*(n/2) = 0 (alternating +/-)... must equal 0.
=> always consistent for even cycles. So |A_M cap A_M'| = n^{#components}.

Let's just compute the full Mobius/inclusion-exclusion numerically to UNDERSTAND the
+40n and -45n^2 terms, by grouping matchings by intersection pattern. But the cleanest:
N(n) is a polynomial in n of degree 3; determine it from values. Already did: 15n^3-45n^2+40n.

Here instead we verify the COMPONENT-COUNT view gives the same, which is the proof skeleton:
For a family, |intersection of A_M over M in family| = n^{c(family)} where c = # connected
components of the combined edge multigraph (when all even-cycle-consistent, else 0).
Then inclusion-exclusion N = sum over nonempty families (-1)^{|family|+1} n^{c}.
We compute that sum and confirm = 15n^3-45n^2+40n as a polynomial.
"""
from itertools import product
import sympy

n = sympy.symbols('n')


def all_perfect_matchings(positions):
    positions = list(positions)
    if not positions:
        yield frozenset()
        return
    first = positions[0]
    rest = positions[1:]
    for i in range(len(rest)):
        pair = frozenset((first, rest[i]))
        remaining = rest[:i] + rest[i + 1:]
        for sub in all_perfect_matchings(remaining):
            yield frozenset({pair}) | sub


M6 = list(all_perfect_matchings([0, 1, 2, 3, 4, 5]))
assert len(M6) == 15


def components_and_consistent(edge_set, nval):
    # edge_set: set of frozenset pairs, each an antipodal constraint t_i - t_j = nval/2
    # build graph, assign values via BFS with the +/- nval/2 offset; check consistency.
    from collections import defaultdict
    adj = defaultdict(list)
    verts = set()
    for e in edge_set:
        a, b = tuple(e)
        adj[a].append(b)
        adj[b].append(a)
        verts.add(a); verts.add(b)
    # also isolated vertices 0..5
    for v in range(6):
        verts.add(v)
    val = {}
    comps = 0
    half = nval // 2
    for v in range(6):
        if v in val:
            continue
        comps += 1
        val[v] = 0
        stack = [v]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                # constraint t_u - t_w = half  (antipodal). edge undirected; from u side
                # t_w = t_u - half ; from w side t_u = t_w - half => t_w = t_u + half.
                # Both must hold => only consistent if 2*half = 0 mod n, i.e. n | n. True.
                # so the offset is well-defined as +half either way (since -half = +half mod n
                # because 2half = n = 0). Use +half.
                target = (val[u] + half) % nval
                if w in val:
                    if val[w] != target:
                        return None  # inconsistent
                else:
                    val[w] = target
                    stack.append(w)
    return comps


# Inclusion-exclusion over nonempty subsets of the 15 matchings is 2^15-1 ~ 32767 terms.
# For a FIXED n we can compute. Then fit polynomial. Use a few n values.
def N_via_incl_excl(nval):
    from itertools import combinations
    total = 0
    # too many subsets; but |A_M cap ...| depends only on combined edge set.
    # Use the union directly is easier, but to validate the component view we do
    # incl-excl over PAIRS only would be wrong. Instead just brute the union (already done).
    # Here: validate the component formula by computing |intersection| for all subsets
    # via combined edges, summing signed. 32767 subsets * tiny work = fine.
    idxs = list(range(15))
    for k in range(1, 16):
        for combo in combinations(idxs, k):
            edges = set()
            for ci in combo:
                edges |= set(M6[ci])
            c = components_and_consistent(edges, nval)
            if c is None:
                contrib = 0
            else:
                contrib = nval ** c
            total += ((-1) ** (k + 1)) * contrib
    return total


for nval in [2, 4, 8, 16]:
    val = N_via_incl_excl(nval)
    pred = 15 * nval**3 - 45 * nval**2 + 40 * nval
    print(f" n={nval}: incl-excl(component formula)={val}, 15n^3-45n^2+40n={pred}, match={val==pred}")
