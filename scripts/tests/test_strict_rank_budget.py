"""The strict syndrome budget keeps every admissible degenerate subset.

Each subset of agreement margin ``m = t - k`` spends ``m`` rows in a space of
dimension ``n - k`` (equivalently ``2m`` rows in dimension ``2(n - k)``).
A non-codeword stack exists only while that product is strictly smaller than
the dimension, so the largest count is ``floor((budget - 1) / cost)``.

``floor(budget / cost) - 1`` matches that count only when ``cost`` divides
``budget``. Otherwise it drops one subset that still fits. The rate-1/2 strip
scan prints that count as the channel yield bound, and the syzygy probe uses
it for the production extrapolation ``n = 2^30``, ``t - k = 2^24 + 1``.
"""
from pathlib import Path
import random
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "probes"))
import probe_syzygy_configuration_bad_counts as bad_counts  # noqa: E402
import probe_syz7_strip_scan as syz7  # noqa: E402


class StrictRankBudget(unittest.TestCase):
    def test_strip_cap_keeps_the_last_admissible_subset(self):
        # n=32, k=16, t=21: m=5 and n-k=16. 3*5=15 < 16, but 4*5=20 is not.
        # floor(16/5)-1 = 2, so the old cap drops D=3 and the printed channel
        # yield 2*(n-t) = 22 instead of 3*11 = 33.
        domain = bad_counts.Domain(32, 16, 21, 97)
        _best, dmax = syz7.scan_threshold(domain, random.Random(0), [])
        self.assertEqual(dmax, 3)
        self.assertLess(3 * 5, 16)
        self.assertGreaterEqual(4 * 5, 16)

    def test_in_strip_margin_is_not_short_one_subset(self):
        # delta = 10/32 = 0.3125 sits in (1 - sqrt(1/2), 1/3).
        # m = 6. floor(16/6) - 1 = 1, but 2*6 = 12 < 16, so the channel
        # yield is 2*(n-t) = 20 rather than 10.
        domain = bad_counts.Domain(32, 16, 22, 97)
        _best, dmax = syz7.scan_threshold(domain, random.Random(0), [])
        self.assertEqual(dmax, 2)
        self.assertEqual(dmax * (32 - 22), 20)

    def test_divisible_margin_stays_one_below_the_quotient(self):
        # m=2 divides n-k=16. Equality 8*2 = 16 fills the space, so D=7.
        domain = bad_counts.Domain(32, 16, 18, 97)
        _best, dmax = syz7.scan_threshold(domain, random.Random(0), [])
        self.assertEqual(dmax, 7)

    def test_generic_planting_cap_and_production_extrapolation(self):
        # 2(n-k)=32, m=3: 10*3=30 < 32 and 11*3=33 is not.
        # floor(32/3)-1 = 9 drops the tenth witness.
        self.assertEqual(bad_counts.generic_planting_cap(32, 16, 3), 10)
        self.assertEqual(bad_counts.generic_planting_cap(32, 16, 2), 15)

        n, k, m = 1 << 30, 1 << 29, (1 << 24) + 1
        dmax = bad_counts.degenerate_subset_cap(n, k, m)
        self.assertEqual(dmax, 31)
        self.assertLess(dmax * m, n - k)
        self.assertGreaterEqual((dmax + 1) * m, n - k)
        self.assertEqual((n - k) // m - 1, 30)


if __name__ == "__main__":
    unittest.main()
