"""Johnson family caps in the D-charge ledger must stay nonnegative.

`johnson_count` is the integer form of
`L <= n*(a-(k-1)) / (a^2 - n*(k-1))` used to decide whether the rate-quarter
derecursion ledger is closed. On a domain shorter than the agreement, with the
pairwise cap still above that agreement, the ratio is negative. Floor division
then returns a negative "maximum", and `1 + cap * riders` can fall under the
budget even though no such pencil exists.
"""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "probes"))
import probe_rate_quarter_p1_dcharge_derecursion as probe


class JohnsonCountEdge(unittest.TestCase):
    def test_agreement_longer_than_the_domain_caps_at_zero(self):
        # Domain of 3 points, agreement 6, pairwise cap k-1 = 10.
        # den = 36 - 30 = 6, num = 3*(6-10) = -12. Floor division yields -2.
        self.assertEqual(probe.johnson_count(6, 3, 11), 0)
        # A ledger that multiplies the cap by a positive rider count must not
        # go negative and report a closed budget.
        self.assertGreaterEqual(1 + probe.johnson_count(6, 3, 11) * 5, 1)

    def test_zero_numerator_is_an_empty_family(self):
        # a = k-1 and the denominator is already positive: the ratio is 0.
        # n=1, k=3, a=2: den = 4 - 2 = 2, num = 0.
        self.assertEqual(probe.johnson_count(2, 1, 3), 0)

    def test_exact_integer_bound_is_kept(self):
        # n=6, k=3, a=4: den = 16 - 12 = 4, num = 12. The greatest L with
        # L*den <= num is 3, and 3 meets the inequality with equality.
        self.assertEqual(probe.johnson_count(4, 6, 3), 3)
        den = 4 * 4 - 6 * (3 - 1)
        num = 6 * (4 - (3 - 1))
        cap = probe.johnson_count(4, 6, 3)
        self.assertEqual(cap * den, num)
        self.assertGreater((cap + 1) * den, num)

    def test_nonpositive_denominator_stays_unbounded(self):
        # a^2 = 4, n*(k-1) = 5, so Johnson does not apply.
        self.assertIsNone(probe.johnson_count(2, 5, 2))

    def test_production_numerator_is_unchanged(self):
        # The P1 parameters sit far above this edge: the cap stays the
        # positive floor used by the published ledger.
        n, k, t = 2**30, 2**28, 592794966
        cap = probe.johnson_count(t, n // 2, k)
        den = t * t - (n // 2) * (k - 1)
        num = (n // 2) * (t - (k - 1))
        self.assertGreater(num, 0)
        self.assertEqual(cap, num // den)


if __name__ == "__main__":
    unittest.main()
