"""Regression for the R305 census norms (audit 2026-10-28, finding L114).

The census once computed cyclotomic norms by rounding complex128 products and casting
to int64: for n = 64 the valid difference z = 6 (three copies of 1 minus three copies
of -1) came back as 9223372036854775807 instead of 6^32.  Norms must be exact integers.
"""
from pathlib import Path
import sys
import unittest

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
from probe_r305_complete_census import (  # noqa: E402
    MR_DETERMINISTIC_BOUND, exact_excess, factorize, is_prime_certified, norms_of,
    validate_n)


def negacyclic_det(z):
    """Independent exact norm: det of multiplication by z on Z[x]/(x^m + 1) (Bareiss)."""
    m = len(z)
    M = [[0] * m for _ in range(m)]
    for i in range(m):
        for j, c in enumerate(z):
            k = i + j
            if k < m:
                M[k][i] += c
            else:
                M[k - m][i] -= c
    prev, sign = 1, 1
    for k in range(m - 1):
        if M[k][k] == 0:
            for i in range(k + 1, m):
                if M[i][k]:
                    M[k], M[i] = M[i], M[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, m):
            for j in range(k + 1, m):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[-1][-1]


class ExactNorms(unittest.TestCase):
    def test_n64_constant_six_is_exact(self):
        z = np.zeros((1, 32), dtype=np.int8)
        z[0, 0] = 6
        self.assertEqual(norms_of(z, 64), [6 ** 32])
        self.assertEqual(6 ** 32, 7958661109946400884391936)

    def test_known_small_height_norm(self):
        # Norm(3 + zeta_32) = 3^16 + 1 = 2 * 21523361 (the R305 beta = 4.87 violator)
        z = np.zeros((1, 16), dtype=np.int8)
        z[0, 0], z[0, 1] = 3, 1
        self.assertEqual(norms_of(z, 32), [3 ** 16 + 1])
        self.assertEqual(factorize(3 ** 16 + 1), ([2, 21523361], True))

    def test_matches_independent_resultant(self):
        rng = np.random.default_rng(20261028)
        for n in (4, 8, 16, 32, 64, 128):
            zs = rng.integers(-6, 7, size=(12, n // 2)).astype(np.int8)
            zs = zs[np.any(zs != 0, axis=1)]
            expected = [negacyclic_det([int(c) for c in row]) for row in zs]
            self.assertEqual(norms_of(zs, n), expected)
            self.assertTrue(all(v > 0 for v in expected))

    def test_invalid_n_rejected(self):
        for n in (0, 2, 3, 6, 12, 48, -8):
            with self.assertRaises(ValueError):
                validate_n(n)
        with self.assertRaises(ValueError):
            norms_of(np.zeros((1, 3), dtype=np.int8), 8)

    def test_factorization_and_primality_domain(self):
        factors, certified = factorize(2 ** 10 * 3 ** 5 * 641 * 6700417)
        self.assertTrue(certified)
        self.assertEqual(factors, [2] * 10 + [3] * 5 + [641, 6700417])
        self.assertTrue(is_prime_certified(3487801441))
        # psi_12: the least strong pseudoprime to every prime base 2..37; base 41 exposes it.
        self.assertFalse(is_prime_certified(318665857834031151167461))
        self.assertFalse(is_prime_certified(3215031751))  # spsp(2, 3, 5, 7)
        with self.assertRaises(ValueError):
            is_prime_certified(MR_DETERMINISTIC_BOUND)

    def test_exact_excess_rejects_bad_moduli(self):
        keys = np.zeros((1, 8), dtype=np.int8)
        cnts = np.ones(1, dtype=np.int64)
        for p in (65, 19, 97 * 113):
            with self.assertRaises(ValueError):
                exact_excess(p, 16, keys, cnts, 1)


if __name__ == '__main__':
    unittest.main()
