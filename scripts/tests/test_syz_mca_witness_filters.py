"""Regression tests for the SYZ28/SYZ29/SYZ32 MCA-badness filters (audit L122, L123, L124).

MCA badness (ArkLib `mcaEvent`) is existential over close witnesses: a scalar is bad iff SOME
close codeword's agreement set is not jointly explained by the pair.  Closeness alone, a first
(joint) close codeword, or a stack-level correlated-agreement set elsewhere must not decide it.
"""
from itertools import combinations
from math import prod
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_syz28_verify_classification as syz28
import probe_syz29_yield_law_accounting as syz29
import probe_syz32_cluster_routing as syz32

N, K, S, P = 16, 8, 11, 17
U0 = [0] * 11 + [1, 0, 0, 0, 0]
U1 = [0] * 11 + [4, 12, 9, 1, 4]
NONJOINT_WITNESS = frozenset(list(range(7)) + list(range(11, 16)))


def interpolate(word, nodes, x):
    total = 0
    for t in nodes:
        num = den = 1
        for t2 in nodes:
            if t2 != t:
                num = num * (x - t2) % P
                den = den * (t - t2) % P
        total += word[t] * num * pow(den, P - 2, P)
    return total % P


def brute_close_codewords(word):
    """Window-free complete decoder: interpolate on every k-subset of the whole domain."""
    out = {}
    for nodes in combinations(range(N), K):
        cw = tuple(interpolate(word, nodes, x) for x in range(N))
        agree = frozenset(j for j in range(N) if cw[j] == word[j] % P)
        if len(agree) >= S:
            out[cw] = agree
    return out


class MCAWitnessFilters(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.mats = syz28.build_interp_mats(N, K, S, P)

    def line(self, z):
        return [(a + z * b) % P for a, b in zip(U0, U1)]

    def test_fixture_has_joint_and_nonjoint_close_codewords_at_gamma1(self):
        cws = syz28.close_codewords(self.line(1), self.mats, N, K, S, P)
        zero = tuple([0] * N)
        poly = tuple(prod(j - a for a in range(7)) % P for j in range(N))
        self.assertEqual(cws[zero], frozenset(range(11)))
        self.assertEqual(cws[poly], NONJOINT_WITNESS)
        self.assertTrue(syz28.pair_joint_on(cws[zero], U0, U1, K, P))
        self.assertFalse(syz28.pair_joint_on(cws[poly], U0, U1, K, P))

    def test_windowed_decoder_matches_window_free_decoder(self):
        for z in (0, 1, 2, 4):
            word = self.line(z)
            self.assertEqual(syz28.close_codewords(word, self.mats, N, K, S, P),
                             brute_close_codewords(word))

    def test_syz29_keeps_gamma1_bad(self):
        bad = dict(syz29.bad_scalars(U0, U1, N, K, S, P))
        self.assertIn(1, bad)
        self.assertIn(NONJOINT_WITNESS, bad[1])

    def test_syz28_separates_closeness_from_mca_badness(self):
        close, inf_close, bad = syz28.classify_line([0] * N, [1] * N, self.mats, N, K, S, P)
        self.assertEqual(close, list(range(P)))
        self.assertTrue(inf_close)
        self.assertEqual(bad, [])

    def test_syz32_global_correlation_does_not_suppress_scalar_badness(self):
        counts = syz32.lift_counts(U0, U1)
        self.assertTrue(counts['global_corr'])
        self.assertIn(1, counts['mca_bad'])
        self.assertNotIn('inf', counts['mca_bad'])

    def test_incomplete_window_is_rejected(self):
        with self.assertRaises(ValueError):
            syz28.build_interp_mats(32, 16, 22, 97)


if __name__ == '__main__':
    unittest.main()
