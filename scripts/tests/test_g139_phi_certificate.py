"""Regression cases for the G139 probe's exact arithmetic helpers."""
import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_g139_phi_certificate as probe


class G139Arithmetic(unittest.TestCase):
    def test_twelve_base_pseudoprime_is_rejected(self):
        composite = 318665857834031151167461
        self.assertEqual(399165290221 * 798330580441, composite)
        self.assertFalse(probe.is_prime(composite))

    def test_strict_certified_limit(self):
        with self.assertRaises(ValueError):
            probe.is_prime(probe.DETERMINISTIC_MR_LIMIT)

    def test_rounding_compares_root_midpoint(self):
        for n, numerator, denominator, expected in [
            (4, 1, 3, 2), (3, 1, 3, 1), (8, 1, 3, 2),
            (6, 1, 2, 2), (7, 1, 2, 3), (0, 1, 3, 0),
            (2, 3, 1, 8),
        ]:
            with self.subTest(n=n, numerator=numerator, denominator=denominator):
                self.assertEqual(probe.rounded_rational_power(n, numerator, denominator), expected)


if __name__ == '__main__':
    unittest.main()
