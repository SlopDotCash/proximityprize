"""Regression tests for the hd1 ledger radius search (audit L105).

The joint predicate (interpolation gate AND ledger budget) is not monotone in the agreement a,
so endpoint-skip plus bisection lost the only certified radius in a small valid family.
"""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import hd1_line_ledger as ledger


class NonMonotoneLedger(unittest.TestCase):
    def test_audit_example_is_not_monotone(self):
        # (n, w, m, s, L, budget) = (6, 2, 2, 1, 2, 5711), exact ranks: integer comparisons.
        total5, gap5, _ = ledger.ledger(6, 2, 5, 2, 1, 2)
        total6, gap6, _ = ledger.ledger(6, 2, 6, 2, 1, 2)
        self.assertEqual((total5, gap5 * gap5), (51390, 9))
        self.assertEqual((total6, gap6 * gap6), (119856, 16))
        self.assertTrue(ledger.certify(6, 2, 5, 2, 1, 2, 5711, exact=True)[0])
        self.assertFalse(ledger.certify(6, 2, 6, 2, 1, 2, 5711, exact=True)[0])

    def test_best_radius_finds_interior_certificate(self):
        best = ledger.best_radius(6, 2, 5711, [2], [1], [2], exact=True)
        self.assertIsNotNone(best)
        a, m, s, L, info = best
        self.assertEqual((a, m, s, L), (5, 2, 1, 2))
        self.assertTrue(info['least_proved'])
        self.assertEqual(info['search'], 'exhaustive')

    def test_least_passing_exhaustive_and_bisection(self):
        def ok(a):
            return a in (5, 9, 10)
        self.assertEqual(ledger.least_passing(ok, 0, 10), (5, True))
        self.assertEqual(ledger.least_passing(lambda a: False, 0, 10), (None, True))
        # bisection fallback: certified (ok holds) but not proved least
        a, proved = ledger.least_passing(ok, 0, 10, exhaustive_limit=2)
        self.assertTrue(ok(a))
        self.assertFalse(proved)
        self.assertEqual(ledger.least_passing(lambda a: a == 3, 0, 10, exhaustive_limit=2),
                         (None, False))


if __name__ == '__main__':
    unittest.main()
