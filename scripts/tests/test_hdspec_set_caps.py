# Copyright (c) 2026 cerapmen7.
# Released under MIT and Apache-2.0; see LICENSE-MIT and LICENSE.
"""Spectral cells denote a set of monomials, never extra copies of a basis."""

from collections import Counter
from itertools import product
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "probes"))
import hdspec_search as spectral


def enumerate_counts(d, n, k, m, omega, agreement, line_degree=None):
    """Count actual basis tuples and contact rows without the spectral DP."""
    w, degree = k - 1, m * agreement
    cap = set(omega)
    smax = max(s for s, _ in cap)
    columns = Counter()
    dimension = 0
    for bs in product(range(smax + 1), repeat=d):
        s = sum(bs)
        j = sum(index * exponent for index, exponent in enumerate(bs, start=1))
        if (s, j) not in cap:
            continue
        for b0 in range(degree // w + 1):
            line_exponents = range(line_degree - b0 + 1) if line_degree is not None else (0,)
            for ell in line_exponents:
                for a in range(degree):
                    if a + w * b0 + sum((w - index) * exponent
                                       for index, exponent in enumerate(bs, start=1)) >= degree:
                        continue
                    dimension += 1
                    if a < m:
                        columns[b0 + s + ell, a - j] += 1

    rows = Counter()
    largest_block = max(g1 for g1, _ in columns)
    for exponents in product(range(largest_block + 1), repeat=d + 1):
        total = sum(exponents)
        if total > largest_block:
            continue
        shift = sum(index * exponent
                    for index, exponent in enumerate(exponents, start=1))
        line_exponents = range(line_degree + 1) if line_degree is not None else (0,)
        for ell in line_exponents:
            for a in range(m):
                rows[total + ell, a - shift] += 1
    rank_bound = sum(min(count, rows[block]) for block, count in columns.items())
    return dimension > n * rank_bound, dimension, n * rank_bound


class SpectralSetCaps(unittest.TestCase):
    def test_repetition_cannot_create_plain_certificate(self):
        for copies in (1, 2, 3, 10):
            with self.subTest(copies=copies):
                self.assertEqual(
                    spectral.verify_exact_int(1, 8, 4, 2, [(0, 0)] * copies, 4),
                    (False, 15, 24),
                )

    def test_repetition_cannot_create_line_certificate(self):
        for copies in (1, 2, 3, 10):
            with self.subTest(copies=copies):
                self.assertEqual(
                    spectral.line_feasible_int(1, 8, 4, 2, [(0, 0)] * copies, 4, 1),
                    (False, 21, 40),
                )

    def test_counts_match_independent_monomial_enumeration(self):
        for d, m, agreement in product((1, 2), (1, 2), (3, 4, 5)):
            k, n = 5, 10
            unique = spectral.wedge(d, 1)
            repeated = unique + list(reversed(unique)) + [unique[0]]
            for line_degree in (None, 0, 1):
                expected = enumerate_counts(d, n, k, m, unique, agreement, line_degree)
                for cap in (unique, repeated, iter(repeated)):
                    with self.subTest(d=d, m=m, agreement=agreement,
                                      line_degree=line_degree, cap_type=type(cap).__name__):
                        if line_degree is None:
                            actual = spectral.verify_exact_int(d, n, k, m, cap, agreement)
                        else:
                            actual = spectral.line_feasible_int(
                                d, n, k, m, cap, agreement, line_degree,
                            )
                        self.assertEqual(actual, expected)

    def test_search_threshold_uses_set_semantics(self):
        evaluator = spectral.SpectralEvaluator(1, 8, 4, 2, smax=1, jmax=1)
        self.assertEqual(evaluator.threshold([(0, 0)]), 6)
        self.assertEqual(evaluator.threshold([(0, 0), (0, 0)]), 6)

    def test_registered_rate_half_certificate_keeps_its_exact_threshold(self):
        cap = spectral.trunc_wedge(12, 102, 205)
        for cells in (cap, cap + cap):
            with self.subTest(repeated=len(cells) != len(cap)):
                self.assertEqual(
                    spectral.verify_exact_int(12, 2**18, 2**17, 128, cells, 173562),
                    (False, 173572981830130088670, 173574747307010686976),
                )
                self.assertEqual(
                    spectral.verify_exact_int(12, 2**18, 2**17, 128, cells, 173563),
                    (True, 173575795916105963870, 173574747307010686976),
                )


if __name__ == "__main__":
    unittest.main()
