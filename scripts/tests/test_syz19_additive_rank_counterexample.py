"""Exact replay of the counterexample to SYZ19's additive aggregate (audit finding L120).

The SYZ19 probe models the aggregate rank budget as sum_i (s_i - k) <= n - k.  Per-core
codimensions do not add when constraint spaces overlap.  At rate 1/2 on the delta = 1/3
boundary (F_1009, n=18, k=9, t=12) five genuinely contributing pencil families have summed
cost 10 > 9 = n - k.  This test checks every equation of that example so the probe's
header claim stays reproducible.
"""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_syz19_lp_dual_certificate as probe

P, N, K, T = 1009, 18, 9, 12
SLOPES = [1, 2, 4, 8, 16]
G_ROOTS = list(range(100, 107))
HOLE = 0


def g_poly(x):
    out = 1
    for z in G_ROOTS:
        out = out * (x - z) % P
    return out


class AdditiveAggregateCounterexample(unittest.TestCase):
    def setUp(self):
        self.pairs = [(i, j) for i in range(5) for j in range(i + 1, 5)]
        self.x = {pr: (-SLOPES[pr[0]] - SLOPES[pr[1]]) % P for pr in self.pairs}
        self.dom = list(self.x.values()) + [HOLE] + G_ROOTS
        self.u0 = {x: 0 for x in self.dom}
        self.u0[HOLE] = g_poly(HOLE)
        self.u1 = {x: 0 for x in self.dom}
        for (i, j), x in self.x.items():
            self.u1[x] = (-g_poly(x) * SLOPES[i] * SLOPES[j]) % P

    def v1(self, m, x):
        return g_poly(x) * (m * x + m * m) % P

    def test_domain_is_distinct(self):
        self.assertEqual(len(set(self.dom)), N)

    def test_five_contributing_families_overspend_additive_budget(self):
        cores, gammas = [], []
        for a, m in enumerate(SLOPES):
            # the pair (v0, v1) = (0, G*(mX+m^2)) has degree 8 < k
            core = {x for x in self.dom if self.u0[x] == 0 and self.u1[x] == self.v1(m, x)}
            incident = {self.x[pr] for pr in self.pairs if a in pr}
            self.assertEqual(core, incident | set(G_ROOTS))
            self.assertEqual(len(core), 11)
            gamma = pow(m * m, P - 2, P)
            agree = {x for x in self.dom
                     if gamma * self.v1(m, x) % P == (self.u0[x] + gamma * self.u1[x]) % P}
            self.assertEqual(agree, core | {HOLE})
            self.assertEqual(len(agree), T)
            # nonjoint: a degree<9 u0-explainer vanishing on 11 core points is zero,
            # but u0(HOLE) != 0
            self.assertNotEqual(self.u0[HOLE], 0)
            cores.append(core)
            gammas.append(gamma)
        self.assertEqual(gammas, [1, 757, 946, 741, 942])
        self.assertEqual(len(set(gammas)), 5)
        overlaps = [len(cores[a] & cores[b]) for a in range(5) for b in range(a + 1, 5)]
        self.assertEqual(max(overlaps), 8)
        self.assertLess(max(overlaps), K)
        summed = sum(probe.rank_cost(K, len(c)) for c in cores)
        self.assertEqual(summed, 10)
        self.assertGreater(summed, N - K)


if __name__ == '__main__':
    unittest.main()
