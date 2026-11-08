"""Support-four t=6 checker validates its premise and keeps the threshold (audit L118)."""
import importlib.util
import itertools
import json
from pathlib import Path
import unittest

import numpy as np

path = Path(__file__).resolve().parents[1] / 'probes/probe_rate_quarter_support4_t6_f17.py'
spec = importlib.util.spec_from_file_location('support4_t6', path)
probe = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe)


class CandidateValidation(unittest.TestCase):
    def test_zero_direction_rejected(self):
        # Formerly accepted: INV[0] = 0 made every ratio 0 and reported bad_scalars=[0],
        # although the true maximum agreement over all 17^4 codewords is 8 < 9.
        zeros = np.zeros(16, dtype=np.int64)
        self.assertEqual(int(np.max(np.sum(probe.VALUES == probe.KNOWN_U0, axis=1))), 8)
        with self.assertRaises(ValueError):
            probe.score(probe.KNOWN_U0, zeros, details=True)

    def test_malformed_inputs_rejected(self):
        u0, u1 = probe.KNOWN_U0, probe.KNOWN_U1
        off_support = u1.copy()
        off_support[7] = 3
        one_zero = u1.copy()
        one_zero[2] = 0
        bad = [(u0, off_support), (u0, one_zero), (u0[:15], u1), (u0 + 17, u1),
               (u0 - 1, u1), (u0.astype(float), u1)]
        for v0, v1 in bad:
            with self.subTest(v0=v0, v1=v1), self.assertRaises(ValueError):
                probe.score(v0, v1)
        for threshold in (6, 11, 9.0, True):
            with self.subTest(threshold=threshold), self.assertRaises(ValueError):
                probe.score(u0, u1, threshold=threshold)


class ThresholdConsistency(unittest.TestCase):
    def test_known_certificate_default_threshold(self):
        result = probe.score(probe.KNOWN_U0, probe.KNOWN_U1, details=True)
        self.assertEqual((result['threshold'], result['model']), (9, 't6'))
        self.assertEqual(result['stratum_t6_card'], 5)
        self.assertEqual(result['bad_scalars'], [2, 5, 10, 12, 15])
        for witness in result['witnesses']:
            self.assertTrue(witness['checks'])
            for check in witness['checks']:
                self.assertGreaterEqual(check['agreement'], 9)
                self.assertTrue(check['nonjoint'])

    def test_threshold_ten_selection_matches_bad_scalars(self):
        # Formerly stratum_t6_card stayed 5 while bad_scalars was [] at threshold 10.
        result = probe.score(probe.KNOWN_U0, probe.KNOWN_U1, details=True, threshold=10)
        self.assertEqual(result['bad_scalars'], [])
        self.assertEqual(result['stratum_t6_card'], 0)

    def test_bad_scalars_match_exhaustive_enumeration(self):
        for u0, u1 in ((probe.KNOWN_U0, probe.KNOWN_U1), (probe.BEST_BAD_U0, probe.BEST_BAD_U1)):
            for threshold in (8, 9, 10):
                expected = []
                for gamma in range(17):
                    line = (u0 + gamma * u1) % 17
                    if int(np.max(np.sum(probe.VALUES == line, axis=1))) >= threshold:
                        expected.append(gamma)
                result = probe.score(u0, u1, details=True, threshold=threshold)
                self.assertEqual(result['bad_scalars'], expected)

    def test_custom_threshold_certificate_round_trips(self):
        for threshold in (8, 10):
            result = probe.score(probe.KNOWN_U0, probe.KNOWN_U1, details=True,
                                 threshold=threshold)
            saved = json.loads(json.dumps(result))
            self.assertEqual(probe.verify_certificate(saved), saved)
            legacy = {k: v for k, v in saved.items() if k not in ('threshold', 'model')}
            with self.assertRaises(ValueError):
                probe.verify_certificate(legacy)
            tampered = dict(saved, threshold=9 if threshold != 9 else 10)
            with self.assertRaises(ValueError):
                probe.verify_certificate(tampered)

    def test_witness_checker_is_independent(self):
        coeffs = [0, 3, 8, 1]
        evals = [probe.evaluate(coeffs, x) for x in range(1, 17)]
        table_row = next(i for i, c in enumerate(itertools.product(range(17), repeat=4))
                         if list(c) == coeffs)
        self.assertEqual(evals, probe.VALUES[table_row].tolist())
        with self.assertRaises(AssertionError):  # wrong scalar: agreement below 9
            probe.check_witness(probe.KNOWN_U0, probe.KNOWN_U1, coeffs, 2, 9)


if __name__ == '__main__':
    unittest.main()
