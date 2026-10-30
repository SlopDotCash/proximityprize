# Copyright (c) 2026 Oz-0s. All rights reserved.
# Released under the MIT and Apache 2.0 licenses. See LICENSE-MIT and LICENSE.
# Authors: Oz-0s

"""Check the R387 linear-algebra certificates using unbounded integer arithmetic."""
from pathlib import Path
import sys
import unittest

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_half_radius_grassmann as probe


class LargeFieldCertificates(unittest.TestCase):
    def test_dependent_rows_do_not_acquire_a_second_pivot(self):
        p = 2**61 - 1
        matrix = [[p - 1, p - 2], [1, 2]]
        reduced, pivots = probe.np_rref(matrix, p)
        self.assertEqual(pivots, [0])
        self.assertEqual(reduced.tolist(), [[1, 2], [0, 0]])
        kernel = probe.np_nullspace(matrix, p)
        self.assertEqual(kernel.shape, (1, 2))
        self.assertTrue(all(sum(x * int(y) for x, y in zip(row, kernel[0])) % p == 0
                            for row in matrix))

    def test_inverse_and_noncanonical_integer_representatives(self):
        p = 2**61 - 1
        matrix = [[p - 1, p - 2], [1, 3]]
        lifted = [[x + 2**80 * p for x in row] for row in matrix]
        inverse = probe.np_inverse(lifted, p)
        product = np.asarray(matrix, dtype=object) @ inverse % p
        self.assertEqual(product.tolist(), [[1, 0], [0, 1]])

    def test_agreement_checks_annihilate_actual_rs_codewords(self):
        for p in (17, 2**31 - 1, 2**61 - 1):
            with self.subTest(p=p):
                domain = [1, 2, 3, 4, p - 2, p - 1]
                checks = probe.agreement_parity(domain, 4, range(6), p)
                for degree in range(4):
                    word = [pow(x, degree, p) for x in domain]
                    residual = checks.astype(object) @ np.asarray(word, dtype=object) % p
                    self.assertFalse(residual.any(), (p, degree, residual))
                # A change outside the interpolation base cannot be another fit.
                word[-1] = (word[-1] + 1) % p
                self.assertTrue((checks.astype(object) @ word % p).any())

    def test_small_fields_keep_the_vectorized_storage(self):
        self.assertEqual(probe.np_rref([[1, 2], [2, 4]], 17)[0].dtype, np.int64)


if __name__ == '__main__':
    unittest.main()
