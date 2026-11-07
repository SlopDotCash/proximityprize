"""G92 direction canonicalization and search-only verdict wording (audit T127)."""
from pathlib import Path
import sys
import unittest

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_g92_spread_excess_c3 as probe


class CanonicalDirection(unittest.TestCase):
    def test_classes(self):
        self.assertEqual(probe.canonical_direction(0, 1, 5, 2), ('code', None))
        self.assertEqual(probe.canonical_direction(0, 4, 1, 2), ('mono', 4))
        self.assertEqual(probe.canonical_direction(1, 4, 3, 2), ('mono', 4))
        self.assertEqual(probe.canonical_direction(2, 4, 3, 2), ('spread', (2, 4, 3)))

    def test_rejects_bad_input(self):
        with self.assertRaises(ValueError):
            probe.canonical_direction(3, 3, 1, 2)
        with self.assertRaises(ValueError):
            probe.canonical_direction(0, 3, 0, 2)

    def test_translate_and_scaling_preserve_bad_counts(self):
        # 1 + 2*X^4 is the X^4 class modulo RS_2: for every offset tried, its
        # exact bad-scalar count equals that of X^4 (the archived G92 n=16,
        # k=2 cell compared exactly such a translate against monomial search).
        amb = probe.Ambient(8, 2, 17)
        rng = np.random.default_rng(7)
        mono = amb.mono(4)
        translate = (amb.codeword([1]) + 2 * mono) % amb.q
        for _ in range(6):
            u0 = rng.integers(0, amb.q, size=amb.n)
            self.assertEqual(amb.brute_count(u0, translate, 3),
                             amb.brute_count(u0, mono, 3))


class SeparationFlag(unittest.TestCase):
    def test_never_claims_refutation(self):
        for ratio in (0.5, 2.0, 2.5, 3.0, 3.833, float('inf')):
            flag = probe.separation_flag(ratio)
            self.assertNotIn('VIOLATED', flag.upper())
            self.assertNotIn('KILL', flag.upper())
            if ratio > 2:
                self.assertIn('unresolved', flag)
        self.assertEqual(probe.separation_flag(1.5), '')
        self.assertIn('C=3', probe.separation_flag(3.833))
        self.assertIn('C=2', probe.separation_flag(2.5))


if __name__ == '__main__':
    unittest.main()
