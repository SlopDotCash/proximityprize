"""Exhaustive small-field check of the parity checker used for R387 witnesses."""
from itertools import combinations, product
from pathlib import Path
import sys
import unittest
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
from probe_half_radius_grassmann import agreement_parity


class AgreementParity(unittest.TestCase):
    def test_all_words_against_all_linear_polynomials(self):
        p, domain = 5, [1, 2, 3, 4]
        code = [tuple((a + b*x) % p for x in domain)
                for a, b in product(range(p), repeat=2)]
        for support in combinations(range(4), 3):
            checks = agreement_parity(domain, 2, support, p)
            for word in product(range(p), repeat=4):
                expected = any(all(word[i] == c[i] for i in support) for c in code)
                actual = not (checks @ np.asarray(word) % p).any()
                self.assertEqual(actual, expected, (support, word))


if __name__ == '__main__':
    unittest.main()
