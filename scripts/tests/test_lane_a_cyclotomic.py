"""Exact characteristic-zero regressions for the Lane A wrap census."""
import math
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import _skeptic_466r10_laneA_spotcheck as probe


class CyclotomicEnergy(unittest.TestCase):
    def test_two_roots_matches_binomial_identity(self):
        for r in range(1, 7):
            self.assertEqual(probe.char0_energy(2, r), math.comb(2 * r, r))

    def test_opposite_roots_cancel(self):
        self.assertEqual(probe.cyclotomic_sum((0, 4), 8), (0, 0, 0, 0))
        self.assertNotEqual(probe.cyclotomic_sum((0,), 8), probe.cyclotomic_sum((1,), 8))

    def test_non_dyadic_input_rejected(self):
        for n in (0, 1, 3, 6):
            with self.assertRaises(ValueError):
                probe.cyclotomic_sum((), n)

    def test_finite_reduction_can_add_solutions(self):
        self.assertEqual(probe.char0_energy(8, 3), 5120)
        self.assertEqual(probe.brute_Er(8, 17, 3) - probe.char0_energy(8, 3), 10440)


if __name__ == '__main__':
    unittest.main()
