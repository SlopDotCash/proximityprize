"""Pencil agreement alone does not establish the nonjoint MCA bad event."""
from itertools import product
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "probes"))
import probe_fsmf_predecessor_miniature_census as probe
import probe_fsmf_predecessor_m10_threeline as m10


def exhaustive_bad(first, second):
    code = [tuple((a + b * x) % 5 for x in (1, 2, 3, 4))
            for a, b in product(range(5), repeat=2)]
    bad = set()
    for gamma in range(5):
        word = [(a + gamma * b) % 5 for a, b in zip(first, second)]
        for candidate in code:
            support = [i for i in range(4) if candidate[i] == word[i]]
            if len(support) < 3:
                continue
            joint = all(any(all(row[i] == c[i] for i in support) for c in code)
                        for row in (first, second))
            if not joint:
                bad.add(gamma)
    return bad


class WitnessJointness(unittest.TestCase):
    def test_codeword_pair_has_no_bad_scalar(self):
        first, second = [0] * 4, [1] * 4
        bad, _ = probe.witness_census(5, [1, 2, 3, 4], 3, [([0], [0])],
                                      [set()], first, second, k=2)
        self.assertEqual(bad, exhaustive_bad(first, second))
        self.assertEqual(bad, set())

    def test_genuine_nonjoint_witness_is_retained(self):
        first, second = [0] * 4, [0, 0, 1, 2]
        bad, _ = probe.witness_census(5, [1, 2, 3, 4], 3, [([0], [0])],
                                      [{0, 1}], first, second, k=2)
        self.assertEqual(bad, exhaustive_bad(first, second))
        self.assertEqual(bad, {0})

    def test_wrong_core_and_noncodeword_pencil_are_rejected(self):
        with self.assertRaises(ValueError):
            probe.witness_census(5, [1, 2, 3, 4], 3, [([0], [0])],
                                 [{0}], [0] * 4, [1] * 4, k=2)
        with self.assertRaises(ValueError):
            probe.witness_census(5, [1, 2, 3, 4], 3, [([0, 0, 1], [0])],
                                 [set()], [1, 4, 4, 1], [1] * 4, k=2)

    def test_recorded_m4_witness_count_is_preserved(self):
        xs, first, second, lines, cores = probe.build_config_B()
        bad, _ = probe.witness_census(probe.P4, xs, probe.T4, lines, cores,
                                      first, second, k=probe.K4)
        self.assertEqual(len(bad), 58)

    def test_recorded_m10_witness_count_is_preserved(self):
        xs, first, second, lines, cores = m10.build()
        bad, _ = probe.witness_census(m10.P, xs, m10.T, lines, cores,
                                      first, second, k=m10.K)
        self.assertEqual(len(bad), 155)
