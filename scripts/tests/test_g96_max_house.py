"""Regression: G96 max-house must not assume the feasible spike heights form an interval.

Analytic counterexample to monotone bisection: n=1, m=2, (P0,P1,P2)=(2,0,2) (unit atoms at
-1 and +1).  Removing a unit atom at H in [0,1) leaves second moment 2-H^2 > 1 for mass 1 on
[-1,1], so the feasible set is {1} and the maximum is 1 (the old bisection returned 0).
"""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))

try:
    import numpy as np
    import probe_g96_extremal as ext  # noqa: E402
    import probe_g96_integrality as integ  # noqa: E402
except ImportError:  # numpy missing
    np = None


@unittest.skipIf(np is None, 'numpy unavailable')
class MaxHouseFeasibleSetGaps(unittest.TestCase):
    def test_isolated_endpoint_feasible_set(self):
        value, rejected = ext.max_house([2, 0, 2], 2, 1, 2)
        self.assertAlmostEqual(value, 1.0, places=12)
        self.assertEqual(rejected, [])

    def test_depth3_isolated_endpoint(self):
        self.assertAlmostEqual(integ.relax_depth3([2, 0, 2, 0], 2, 1), 1.0, places=12)

    def test_scan_does_not_assume_monotonicity(self):
        # feasible set [0, 0.1] U {0.75}: bisection from [0, 1] would return about 0.1
        def feas(h):
            return h <= 0.1 or h == 0.75
        best, _ = ext.scan_max_feasible(feas, 1, grid=4)
        self.assertEqual(best, 0.75)

    def test_result_contains_known_period_measure(self):
        for n, p, D in [(8, 41, 10), (8, 73, 12), (8, 89, 12)]:
            m = (p - 1) // n
            vals = ext.period_values(p, n)
            M = float(np.abs(vals).max())
            P = [np.sum(vals ** r) for r in range(D + 1)]
            value, rejected = ext.max_house(P, m, n, D, known=(M,))
            self.assertGreaterEqual(value, M, (n, p, D))
            self.assertEqual(rejected, [], (n, p, D))


if __name__ == '__main__':
    unittest.main()
