"""Regression tests for G286's convex-hull separator (audit L104).

When 0 lies in the affine hull but not the convex hull of V, a strict linear separator still
exists; the pre-fix code reported the constant w = 0, c = 1 instead.
"""
from fractions import Fraction as F
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import g286_hull_zero_probe as probe


def as_q(rows):
    return [[F(x) for x in row] for row in rows]


class StrictSeparator(unittest.TestCase):
    def assert_strict_separator(self, V, w, margin):
        self.assertTrue(any(w), "separator normal must be nonzero")
        values = [sum(wx * vx for wx, vx in zip(w, v)) for v in V]
        self.assertEqual(min(values), margin)
        self.assertGreater(margin, 0)  # phi(0) = 0 < min_v phi(v)

    def test_affine_in_convex_out_line(self):
        V = as_q([[1], [2]])
        self.assertTrue(probe.affine_separator(V))  # 0 = 2*1 - 1*2 is affine
        self.assertEqual(probe.zero_in_convex_hull(V), (False, None))
        self.assertIsNone(probe.exact_max_margin_separator(V))
        (w, margin), why = probe.build_and_verify_separator(V)
        self.assertIsNone(why)
        self.assert_strict_separator(V, w, margin)

    def test_centered_reflection_symmetric_rows(self):
        V = as_q([[-2, 1, 1], [-4, 2, 2]])
        self.assertTrue(probe.affine_separator(V))
        self.assertEqual(probe.zero_in_convex_hull(V)[0], False)
        self.assertIsNone(probe.exact_max_margin_separator(V))
        (w, margin), _ = probe.build_and_verify_separator(V)
        self.assert_strict_separator(V, w, margin)

    def test_zero_in_convex_hull_has_no_separator(self):
        V = as_q([[1, 0], [-1, 0], [0, 3]])
        feasible, lam = probe.zero_in_convex_hull(V)
        self.assertTrue(feasible)
        self.assertEqual(sum(lam), 1)
        self.assertTrue(all(x >= 0 for x in lam))
        self.assertIsNone(probe.strict_linear_separator(V))
        self.assertEqual(probe.build_and_verify_separator(V)[0], None)

    def test_affine_out_projection_is_valid(self):
        V = as_q([[1, 1], [1, 3]])
        w, c, margin = probe.exact_max_margin_separator(V)
        self.assertEqual(c, 0)
        self.assert_strict_separator(V, w, margin)

    def test_constant_is_not_a_separator(self):
        self.assertIsNone(probe.normalize_and_check([F(0)], F(1), as_q([[1], [2]])))

    def test_iteration_cap_is_unknown_not_infeasible(self):
        V = as_q([[1], [2]])
        self.assertEqual(probe.zero_in_convex_hull(V, max_iter=0), (None, "unknown"))
        self.assertEqual(probe.strict_linear_separator(V, max_iter=0), "unknown")
        self.assertEqual(probe.build_and_verify_separator(V, max_iter=0), (None, "unknown"))


if __name__ == '__main__':
    unittest.main()
