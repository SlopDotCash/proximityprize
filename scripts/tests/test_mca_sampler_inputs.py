"""Invalid field/embedding inputs must not produce prize lower-bound reports."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import proximity_prize_mca_sampler as sampler


class SamplerInputs(unittest.TestCase):
    def test_codebook_rejects_nonfields_and_repeated_domain_points(self):
        for q, n, k in ((9, 4, 1), (65, 4, 2), (5, 6, 2), (3, 2, 3)):
            with self.subTest(q=q, n=n, k=k), self.assertRaises(ValueError):
                sampler.vandermonde_codewords(q, n, k)

    def test_cli_rejects_invalid_reports_before_creating_artifact(self):
        source = Path(sampler.__file__)
        for q, pairs in ((9, 1), (5, 0)):
            with self.subTest(q=q, pairs=pairs), tempfile.TemporaryDirectory() as folder:
                output = Path(folder) / "report.json"
                result = subprocess.run([sys.executable, str(source), "--q", str(q),
                                         "--n", "4", "--k", "1", "--pairs-per-family",
                                         str(pairs), "--out", str(output)],
                                        capture_output=True, text=True, timeout=30)
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertFalse(output.exists())

    def test_valid_prime_codebook_and_exact_small_bad_set(self):
        code = sampler.vandermonde_codewords(5, 4, 1)
        self.assertEqual(code.shape, (5, 4))
        first, second = np.array([0, 0, 1, 2]), np.array([0, 1, 0, 1])
        # For degree-zero codewords, a support is jointly explained iff both
        # rows are constant on it. Directly enumerating equal-value groups
        # gives the bad scalar set {0,1,3,4} at agreement threshold two.
        self.assertEqual(sampler.bad_gammas_for_pair(first, second, code, 5, 4, 1, 2), 4)
