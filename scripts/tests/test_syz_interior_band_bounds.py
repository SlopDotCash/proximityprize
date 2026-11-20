"""The strict interior band is every integer s with 2n/3 < s < 3n/4.

`floor(3n/4) - 1` is that top size only when 4 divides n. Otherwise it drops
the greatest admissible core size, and for some n (14, 18, ...) the band
comes back empty. SYZ50's `band_bounds` already uses the closed form
`(3n - 1) // 4`. The SYZ27 sweep and the SYZ28 enumerator must use it too:
SYZ31's strict-interior crack sits on that dropped size.
"""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_syz27_interior_gluing as syz27  # noqa: E402
import probe_syz28_d3_coplanar_crack as syz28  # noqa: E402
import probe_syz50_witness_realizability as syz50  # noqa: E402


def open_interior_sizes(n):
    """Integers s with 3s > 2n and 4s < 3n."""
    return [s for s in range(1, n + 1) if 3 * s > 2 * n and 4 * s < 3 * n]


class InteriorBandBounds(unittest.TestCase):
    def test_band_sizes_is_the_full_open_interval(self):
        for n in range(1, 97):
            self.assertEqual(syz28.band_sizes(n), open_interior_sizes(n), n)

    def test_band_sizes_matches_syz50_bounds(self):
        for n in range(1, 97):
            lo, hi = syz50.band_bounds(n)
            expected = list(range(lo, hi + 1)) if hi >= lo else []
            self.assertEqual(syz28.band_sizes(n), expected, n)

    def test_dropped_top_size_is_restored(self):
        # n = 18: 2n/3 = 12 and 3n/4 = 13.5, so the only interior size is 13.
        # floor(3n/4) - 1 = 12, and the enumerator returned no interior size.
        self.assertEqual(syz28.band_sizes(18), [13])
        found = syz28.enumerate_d3(18, trials=0, include_boundary=False)
        self.assertIsNotNone(found)
        self.assertEqual(found['sizes'], [13])
        # n = 22: floor(3n/4) - 1 keeps 15 and drops 16, the SYZ31 crack size.
        self.assertEqual(syz28.band_sizes(22), [15, 16])
        self.assertEqual(syz28.band_sizes(14), [10])

    def test_published_multiples_of_four_stay_put(self):
        self.assertEqual(
            [syz28.band_sizes(n) for n in (16, 20, 24, 28, 32)],
            [[11], [14], [17], [19, 20], [22, 23]])

    def test_sweep_uses_the_same_open_interval(self):
        for n in range(4, 65):
            expected = open_interior_sizes(n)
            result = syz27.band_sweep(n, trials=0)
            if not expected:
                self.assertIsNone(result, n)
            else:
                self.assertEqual((result['lo'], result['hi']),
                                 (expected[0], expected[-1]), n)


if __name__ == '__main__':
    unittest.main()
