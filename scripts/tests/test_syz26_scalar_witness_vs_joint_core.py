"""Exact replay of the SYZ26 scalar-witness / joint-core counterexample (audit finding L121).

A strip event's scalar witness S (|S| >= t) does not force a joint codeword-pair core of size
>= t - 1.  Over F_17 with domain mu_16, k = 8, delta = 5/16 (t = 11), u1 = X^8 and u0 = -u1:
gamma = 1 is bad, but every pencil pair through its witnesses has joint core <= 8 < 10.
"""
from itertools import combinations
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_syz26_lifting_test as probe

P, N, K, T = 17, 16, 8, 11
DOM = list(range(1, P))  # mu_16 = F_17^*


def vandermonde_rows(points, degree_bound):
    return [[pow(x, d, P) for d in range(degree_bound)] for x in points]


class ScalarWitnessIsNotJointCore(unittest.TestCase):
    def setUp(self):
        self.u1 = [pow(x, 8, P) for x in DOM]
        self.u0 = [(-v) % P for v in self.u1]

    def test_line_at_gamma_one_is_zero_codeword(self):
        self.assertEqual([(a + b) % P for a, b in zip(self.u0, self.u1)], [0] * N)

    def test_eleven_point_witness_only_explained_by_zero(self):
        # degree<8 polynomials vanishing on 11 points: kernel of an 11x8 Vandermonde is {0}
        for S in [tuple(range(11)), tuple(range(5, 16))]:
            rows = vandermonde_rows([DOM[i] for i in S], K)
            self.assertEqual(probe.rank(rows, K, P), K)

    def test_full_set_is_nonjoint(self):
        # X^8 is not a degree<8 polynomial on the 16 points
        rows = vandermonde_rows(DOM, K)
        aug = [r + [u] for r, u in zip(rows, self.u1)]
        self.assertEqual(probe.rank(rows, K, P), K)
        self.assertEqual(probe.rank(aug, K + 1, P), K + 1)

    def test_every_joint_core_has_at_most_eight_points(self):
        # A joint pair through the gamma=1 witness has v0 = -v1, so its joint core is where
        # v1 = X^8.  On any 9 points the 9x9 Vandermonde with columns 1..X^8 is invertible,
        # so X^8 agrees with a degree<8 polynomial on at most 8 points (< t - 1 = 10).
        for S in combinations(range(N), 9):
            rows = vandermonde_rows([DOM[i] for i in S], K + 1)
            self.assertEqual(probe.rank(rows, K + 1, P), K + 1)
        self.assertLess(8, T - 1)


if __name__ == '__main__':
    unittest.main()
