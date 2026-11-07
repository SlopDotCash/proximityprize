"""Independent integer checks for the depth-three bad-prime norm census."""
from contextlib import redirect_stdout
from fractions import Fraction
from io import StringIO
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "probes"))
import probe_r305_complete_census as probe


FIRST_PRIZE_FIELD = 365375409332725729550921208179070755120141565953


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
        keys, counts = probe.build_n3(4)
        char0 = sum(int(count) ** 2 for count in counts)
        self.assertEqual(probe.exact_excess(FIRST_PRIZE_FIELD, 4, keys, counts, char0), 0)


    def test_norms_preserve_unbounded_integral_object_coefficients(self):
        for a in (2 ** 80, np.int64(-(2 ** 63))):
            with self.subTest(a=a):
                rows = np.array([[a, 1]], dtype=object)
                self.assertEqual(probe.norms_of(rows, 4).tolist(), [int(a) ** 2 + 1])
        with self.assertRaises(TypeError):
            probe.norms_of(np.array([[1.5, 0]]), 4)

    def test_norms_preserve_order_two(self):
        self.assertEqual(probe.norms_of(np.array([[-3], [3]]), 2).tolist(), [-3, 3])

    def test_invalid_n_rejected(self):
        for n in (0, 1, 3, 6, 12, 48, -8):
            with self.assertRaises(ValueError):
                probe.validate_n(n)
        with self.assertRaises(ValueError):
            probe.norms_of(np.zeros((1, 3), dtype=np.int8), 8)

    def test_norms_match_determinants_across_tower_sizes(self):
        rng = np.random.default_rng(20261028)
        for n in (4, 8, 16, 32, 64, 128):
            with self.subTest(n=n):
                rows = rng.integers(-6, 7, size=(2, n // 2), dtype=np.int8)
                expected = [multiplication_determinant(row.tolist()) for row in rows]
                self.assertEqual(probe.norms_of(rows, n).tolist(), expected)

    def test_exact_excess_rejects_bad_moduli(self):
        keys = np.zeros((1, 8), dtype=np.int8)
        counts = np.ones(1, dtype=np.int64)
        for p in (65, 19, 97 * 113):
            with self.assertRaises(ValueError):
                probe.exact_excess(p, 16, keys, counts, 1)


class CertifiedFactorization(unittest.TestCase):
    def test_known_small_height_norm(self):
        # Norm(3 + zeta_32) = 3^16 + 1 = 2 * 21523361.
        row = np.zeros((1, 16), dtype=np.int8)
        row[0, :2] = [3, 1]
        self.assertEqual(probe.norms_of(row, 32).tolist(), [3 ** 16 + 1])
        self.assertEqual(probe.factorize(3 ** 16 + 1), ([2, 21523361], True))

    def test_factorization_and_primality_domain(self):
        factors, certified = probe.factorize(2 ** 10 * 3 ** 5 * 641 * 6700417)
        self.assertTrue(certified)
        self.assertEqual(factors, [2] * 10 + [3] * 5 + [641, 6700417])
        self.assertTrue(probe.is_prime_certified(3487801441))
        # The least strong pseudoprime to the first twelve prime bases.
        self.assertFalse(probe.is_prime_certified(318665857834031151167461))
        self.assertFalse(probe.is_prime_certified(3215031751))
        with self.assertRaises(ValueError):
            probe.is_prime_certified(probe.MR_DETERMINISTIC_BOUND)

    def test_out_of_range_factor_keeps_census_diagnostic(self):
        self.assertEqual(probe.factorize(FIRST_PRIZE_FIELD), ([FIRST_PRIZE_FIELD], False))
        out = StringIO()
        with patch.object(sys, "argv", ["r305", "--n", "4"]):
            with patch.object(probe, "norms_of", return_value=np.array([FIRST_PRIZE_FIELD])):
                with redirect_stdout(out):
                    self.assertEqual(probe.main(), 2)
        self.assertIn("DIAGNOSTIC (uncertified)", out.getvalue())
        self.assertIn("Skipped 1 unresolved candidates", out.getvalue())
        self.assertNotIn("overall", out.getvalue())
        self.assertNotIn("all beta", out.getvalue())
