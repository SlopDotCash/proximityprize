"""Regression tests for the SYZ18 budget-violation metric (audit finding L119).

Any stack whose truly-bad set exceeds the budget refutes the SYZ18 budget claim, whatever
other scalars are pairJoint-rescued.  The probe once required, in addition, that no scalar
anywhere in F be rescued, and so could label an over-budget cell clean.
"""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_syz18_pairjoint_self_exclusion as probe


class ClassifyStack(unittest.TestCase):
    def test_rescue_elsewhere_does_not_cancel_violation(self):
        c = probe.classify_stack(bad=[1, 2, 3, 4, 5, 6], rescued=[9],
                                 planted=[1, 2, 3, 4, 5], budget=4)
        self.assertTrue(c['violation'])
        self.assertFalse(c['planted_rescued'])
        self.assertTrue(c['any_rescued'])

    def test_planted_rescue_does_not_cancel_violation(self):
        c = probe.classify_stack(bad=[2, 3, 4, 5, 6], rescued=[1],
                                 planted=[1, 2, 3, 4, 5], budget=4)
        self.assertTrue(c['violation'])
        self.assertTrue(c['planted_rescued'])

    def test_within_budget_is_not_violation(self):
        c = probe.classify_stack(bad=[1, 2, 3, 4], rescued=[], planted=[1, 2], budget=4)
        self.assertFalse(c['violation'])
        self.assertFalse(c['any_rescued'])


class StripCellS1(unittest.TestCase):
    def setUp(self):
        self.cell = probe.Cell(10, 5, 11, 3)

    def test_headline_stack_bad_set(self):
        u0 = [8, 8, 5, 6, 4, 0, 0, 0, 0, 0]
        u1 = [6, 3, 0, 5, 3, 0, 0, 0, 0, 0]
        bad, rescued = probe.full_bad_scan(
            self.cell, probe.synd(self.cell, u0), probe.synd(self.cell, u1))
        self.assertEqual(bad, [0, 1, 2, 3, 6, 7, 8, 9, 10])
        self.assertEqual(rescued, [])

    def test_every_overbudget_stack_is_a_violation(self):
        best, stats, violations = probe.phase1_direct_construction(self.cell)
        self.assertEqual(stats['overbudget'], len(violations))
        for _s0, _s1, bad, _rescued in violations:
            self.assertGreater(len(bad), self.cell.budget)
        # The seeded default run has one over-budget stack with a planted label rescued,
        # which the legacy zero-rescue-anywhere metric did not count.
        self.assertEqual(stats['overbudget'], 7)
        self.assertEqual(stats['overbudget_zero_rescue_anywhere'], 6)
        self.assertEqual(stats['overbudget_planted_rescued'], 1)
        self.assertLessEqual(stats['basis_vectors_tested'], stats['basis_vectors_total'])


if __name__ == '__main__':
    unittest.main()
