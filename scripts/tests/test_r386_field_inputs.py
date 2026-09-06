"""Regression for composite moduli accepted by the prime-field census."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
from probe_r386_unique_root_strata import validate_field


class CensusFieldInputs(unittest.TestCase):
    def test_composite_with_dyadic_order_is_rejected(self):
        # 8 has order four modulo 65, so an order check alone is insufficient.
        self.assertEqual(pow(8, 4, 65), 1)
        self.assertNotEqual(pow(8, 2, 65), 1)
        with self.assertRaisesRegex(ValueError, 'prime'):
            validate_field(4, 65)

    def test_valid_field_and_invalid_orders(self):
        validate_field(16, 65617)
        for n, p in [(3, 13), (1, 17), (8, 19), (4, -3)]:
            with self.assertRaises(ValueError):
                validate_field(n, p)


if __name__ == '__main__':
    unittest.main()
