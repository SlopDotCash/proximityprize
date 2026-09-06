"""Regression coverage for the leaf-prime check in the Pocklington contract."""
import math
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "probes"))
import verify_g139_n2e30_arithmetic_contract as contract


class ArithmeticContractPrimality(unittest.TestCase):
    def test_seven_base_composite_is_rejected(self):
        composite = 10670053 * 32010157
        self.assertEqual(composite, 341550071728321)
        self.assertFalse(contract.is_prime_u64(composite))

    def test_small_values_match_trial_division(self):
        for n in range(1000):
            expected = n >= 2 and all(n % d for d in range(2, math.isqrt(n) + 1))
            self.assertEqual(contract.is_prime_u64(n), expected, n)

    def test_out_of_range_is_not_certified(self):
        with self.assertRaises(ValueError):
            contract.is_prime_u64(1 << 64)

    def test_complete_arithmetic_contract(self):
        self.assertEqual(contract.verify_arithmetic(), (True, True, True))


if __name__ == "__main__":
    unittest.main()
