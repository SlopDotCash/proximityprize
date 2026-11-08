"""Regression for the odd-order control of probe_oc_kernel_formula (audit 2026-10-28, L113).

The probe once printed that odd-order zero-sum counts "vary with p" like a generic n^r/q
quantity.  For n = 3, r = 3 the count is exactly 6 for every prime p = 1 (mod 3): the
relation 1 + g + g^2 = 0 holds in every characteristic.
"""
from collections import Counter
import itertools
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
from probe_oc_kernel_formula import (  # noqa: E402
    A_formula, C_prime_order, S0_exact, find_gen, is_prime)


class OddOrderControl(unittest.TestCase):
    def test_order_three_triples_are_field_independent(self):
        primes = [p for p in range(7, 1500) if is_prime(p) and p % 3 == 1]
        self.assertGreater(len(primes), 50)
        for p in primes:
            self.assertEqual(S0_exact(p, find_gen(p, 3), 3, 3), 6, p)
        self.assertEqual(C_prime_order(3, 3), 6)

    def test_prime_order_char0_count(self):
        self.assertEqual(C_prime_order(5, 5), 120)
        self.assertEqual(C_prime_order(3, 6), 90)  # 6!/(2!)^3
        for n, r in [(3, 2), (3, 4), (5, 3)]:
            self.assertEqual(C_prime_order(n, r), 0)
        # large-p S0 equals the char-0 count
        p = 601  # 601 = 1 mod 3 and 1 mod 5
        self.assertEqual(S0_exact(p, find_gen(p, 3), 3, 6), 90)
        self.assertEqual(S0_exact(p, find_gen(p, 5), 5, 5), 120)

    def test_antipodal_formula_matches_brute_count(self):
        for n in (4, 8):
            m = n // 2
            for r in (2, 3, 4):
                brute = 0
                for t in itertools.product(range(n), repeat=r):
                    c = Counter(t)
                    brute += all(c[j] == c[j + m] for j in range(m))
                self.assertEqual(A_formula(n, r), brute)


if __name__ == '__main__':
    unittest.main()
