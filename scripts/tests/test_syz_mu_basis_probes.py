"""Regression tests for the SYZ37 / SYZ39 / SYZ45 probe fixes (audit L125, L126, L127)."""
from fractions import Fraction
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_syz37_rate_half_assembly as syz37
import probe_syz39_sylvester_badprime_structure as syz39
import probe_syz45_imbalance_bound as syz45
import probe_syz47_geometric_balance as syz47


class Syz37ModuleGenerators(unittest.TestCase):
    """L125: X*h must not be counted as a second module generator."""

    P_A = [3, 16, 14, 1]
    P_C = [11, 11, 8, 1]
    P_B = [12, 4, 3, 1]

    def test_split_locator_triple_is_unbalanced(self):
        dom = syz37.roots_of_unity(16, 17)
        self.assertEqual(dom[1], 3)
        A, B, C = {0, 1, 8}, {2, 9, 10}, {3, 5, 7}
        locs = [syz37.poly_from_roots([dom[i] for i in sorted(X)], 17) for X in (A, C, B)]
        self.assertEqual(locs, [self.P_A, self.P_C, self.P_B])
        dims = [syz37.inbudget_syzygy_dim(*locs, D, D, D, 17) for D in range(4)]
        self.assertEqual(dims, [1, 2, 3, 5])
        self.assertEqual(syz37.min_syzygy_degree(*locs, 17, 3), (0, 3))

    def test_band_cores_and_deficiency_preserved(self):
        dom = syz37.roots_of_unity(16, 17)
        A, B, C = {0, 1, 8}, {2, 9, 10}, {3, 5, 7}
        T = {4, 6, 11, 12}
        cores = [sorted(T | A | C | {13}), sorted(T | A | B | {14}), sorted(T | B | C | {15})]
        sets = [set(c) for c in cores]
        self.assertEqual([len(c) for c in cores], [11, 11, 11])
        self.assertEqual([len(sets[i] & sets[j]) for i, j in ((0, 1), (0, 2), (1, 2))],
                         [7, 7, 7])
        self.assertEqual(len(sets[0] | sets[1] | sets[2]), 16)
        self.assertEqual(syz37.gen_deficiency(dom, 8, 17, cores), 1)

    def test_generic_balanced_triple(self):
        # Two independent generators at the same degree must both be recorded.
        p = 101
        f, g, h = (syz37.poly_from_roots(r, p) for r in ([1, 2], [3, 4], [5, 6]))
        mu1, mu2 = syz37.min_syzygy_degree(f, g, h, p, 2)
        self.assertEqual((mu1, mu2), (1, 1))


def sylvester_resultant(A, B):
    """Independent exact Res(A,B): Fraction Gaussian elimination on the Sylvester matrix."""
    m, n = len(A) - 1, len(B) - 1
    size = m + n
    if size == 0:
        return 1
    rows = []
    for i in range(n):
        rows.append([0] * i + list(reversed(A)) + [0] * (size - m - 1 - i))
    for i in range(m):
        rows.append([0] * i + list(reversed(B)) + [0] * (size - n - 1 - i))
    M = [[Fraction(x) for x in r] for r in rows]
    det = Fraction(1)
    for c in range(size):
        piv = next((r for r in range(c, size) if M[r][c] != 0), None)
        if piv is None:
            return 0
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            det = -det
        det *= M[c][c]
        for r in range(c + 1, size):
            f = M[r][c] / M[c][c]
            M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return int(det)


class Syz39Arithmetic(unittest.TestCase):
    """L126: norm candidates vs common prime-ideal obstructions; bounded CRT."""

    def test_crt_resultant_needs_a_bound(self):
        B = 11992411764462614086353260819346129198106
        self.assertEqual(syz39.crt_resultant([-1, 1], [B]), B)
        self.assertEqual(syz39.crt_resultant([-1, 1], [-B]), B)

    def test_crt_resultant_matches_exact_resultant(self):
        cases = [([1, 0, 1], [-2, 1]), ([1, 1, 1, 1, 1], [3, -7, 0, 5]),
                 ([2, 0, 0, 3], [1, 4, 9]), ([-1, 0, 0, 0, 1], [5, 1, 1])]
        for A, B in cases:
            exact = sylvester_resultant(A, B)
            self.assertEqual(syz39.resultant_int(A, B), exact)
            self.assertEqual(syz39.crt_resultant(A, B), abs(exact))
            self.assertGreaterEqual(syz39.resultant_hadamard_bound(A, B), abs(exact))

    def test_norm_candidate_is_not_a_common_ideal_obstruction(self):
        n = 4
        phi = syz39.cyclotomic(n)
        self.assertEqual(phi, [1, 0, 1])
        minors = [[-2, 1], [2, 1]]                      # i - 2, i + 2
        self.assertEqual([syz39.resultant_int(phi, m) for m in minors], [5, 5])
        self.assertIn(5, syz39.norm_candidate_primes(phi, minors, syz39.SMALLPRIMES))
        Mc = [[syz39.Cyc(n, phi, m)] for m in minors]   # 2x1 matrix over Z[i]
        self.assertEqual(syz39.common_ideal_rank_deficient_embeddings(Mc, 1, n, 5), [])
        self.assertIsNone(syz39.common_ideal_rank_deficient_embeddings(Mc, 1, n, 3))
        # A genuine common obstruction: both entries vanish at i = 2 mod 5.
        Md = [[syz39.Cyc(n, phi, [-2, 1])], [syz39.Cyc(n, phi, [-4, 2])]]
        self.assertEqual(syz39.common_ideal_rank_deficient_embeddings(Md, 1, n, 5), [2])

    def test_no_minors_gives_no_candidates(self):
        self.assertEqual(syz39.norm_candidate_primes([1, 0, 1], [], syz39.SMALLPRIMES), [])


class Syz45BandCounterexample(unittest.TestCase):
    """L127: proper/full-cover band geometry admits iota = 2."""

    def test_exact_counterexample(self):
        self.assertEqual(syz45.test_D(), 2)

    def test_triangle_floor_still_holds(self):
        p, n, k, dom, cores, (f, g, h), (a, b, c), t = syz45.l127_counterexample()
        self.assertTrue(syz47.is_band_triangle(a, b, c))
        d1 = syz47.delta1(f, g, h, a, b, c, p)
        self.assertGreaterEqual(d1, max(a, b, c))
        # It lies in the balanced interior, outside SYZ47's covered strip.
        self.assertLess(max(a, b, c), (a + b + c) // 2 - 1)


if __name__ == '__main__':
    unittest.main()
