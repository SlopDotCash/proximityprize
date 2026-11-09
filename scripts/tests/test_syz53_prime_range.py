# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""The exact SYZ53 p-sweep must not select a composite as its prime field."""
from math import isqrt
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_syz53_p_scaling as probe


class SYZ53PrimeRange(unittest.TestCase):
    def test_known_twelve_base_pseudoprime_is_rejected(self):
        composite = 399165290221 * 798330580441
        self.assertEqual(composite, 318665857834031151167461)
        with self.assertRaises(ValueError):
            probe.is_prime(composite)
        with self.assertRaises(ValueError):
            probe.next_prime_1modn(composite, 2)

    def test_prime_search_and_small_classifications_remain_exact(self):
        for n in range(500):
            expected = n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))
            self.assertEqual(probe.is_prime(n), expected, n)
        self.assertTrue(probe.is_prime(2147483647))
        self.assertFalse(probe.is_prime(3215031751))
        for target, order, expected in ((29, 14, 29), (30, 14, 43), (100, 16, 113)):
            self.assertEqual(probe.next_prime_1modn(target, order), expected)


if __name__ == '__main__':
    unittest.main()
