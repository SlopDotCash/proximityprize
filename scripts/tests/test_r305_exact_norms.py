"""Independent integer checks for the depth-three bad-prime norm census."""
from fractions import Fraction
from pathlib import Path
import sys
import unittest

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "probes"))
import probe_r305_complete_census as probe


def multiplication_determinant(row):
    """Norm as det(multiplication by f) in Z[X]/(X^m+1)."""
    m = len(row)
    matrix = [[Fraction(0) for _ in range(m)] for _ in range(m)]
    for col in range(m):
        for index, coefficient in enumerate(row):
            degree = index + col
            matrix[degree % m][col] += coefficient * (-1 if degree >= m else 1)
    determinant = Fraction(1)
    for col in range(m):
        pivot = next((r for r in range(col, m) if matrix[r][col]), None)
        if pivot is None:
            return 0
        if pivot != col:
            matrix[col], matrix[pivot] = matrix[pivot], matrix[col]
            determinant = -determinant
        value = matrix[col][col]
        determinant *= value
        for r in range(col + 1, m):
            factor = matrix[r][col] / value
            matrix[r] = [a - factor * b for a, b in zip(matrix[r], matrix[col])]
    assert determinant.denominator == 1
    return determinant.numerator


class ExactNorms(unittest.TestCase):
    def test_actual_depth_three_difference_exceeds_int64(self):
        # Difference of the three-sums (1,1,1) and (-1,-1,-1) in mu_64.
        rows = np.zeros((1, 32), dtype=np.int8)
        rows[0, 0] = 6
        self.assertEqual(int(probe.norms_of(rows, 64)[0]), 6 ** 32)

    def test_norms_match_an_independent_rational_determinant(self):
        for row in ([3, 1], [1, -2, 1, 2], [3, 0, 0, 1],
                    [2, -1, 0, 1, 0, 0, 1, 1]):
            with self.subTest(row=row):
                actual = probe.norms_of(np.asarray([row]), 2 * len(row))[0]
                self.assertEqual(actual, multiplication_determinant(row))

    def test_non_dyadic_norm_domain_is_rejected(self):
        with self.assertRaises(ValueError):
            probe.norms_of(np.asarray([[1, 2, 3]]), 6)

    def test_exact_excess_accepts_first_prize_field_modulus(self):
        # P1, also used by the multicore-ladder probe. At n=4 all nonzero
        # difference norms are at most 6^2, so this prime adds no collisions.
        prime = 365375409332725729550921208179070755120141565953
        keys, counts = probe.build_n3(4)
        char0 = sum(int(count) ** 2 for count in counts)
        self.assertEqual(probe.exact_excess(prime, 4, keys, counts, char0), 0)
