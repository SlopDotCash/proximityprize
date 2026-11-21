# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""G84's independent refutation recount remains enforced under optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = (
    Path(__file__).resolve().parents[1]
    / "probes"
    / "probe_rate_half_predecessor_count_small_scale.py"
)


class SmallScaleRecountOptimization(unittest.TestCase):
    def run_probe(self, flag, recount_matches):
        recount_expression = (
            "set(range(self.n + 1))" if recount_matches else "set(range(1, self.n + 2))"
        )
        code = (
            "import runpy\n"
            f"m = runpy.run_path({str(PROBE)!r})\n"
            "g = m['run'].__globals__\n"
            "class FakeCell:\n"
            "    def __init__(self, n, p, t, label):\n"
            "        self.n, self.p, self.t, self.label = n, p, t, label\n"
            "        self.exact, self.pool, self.g = False, [0], 1\n"
            "    def bad_gammas(self, u0, u1):\n"
            "        return set(range(self.n + 1))\n"
            f"    def recount(self, u0, u1): return {recount_expression}\n"
            "g['Cell'] = FakeCell\n"
            "g['primes_1_mod_n'] = lambda n, count: [n + 1] * count\n"
            "g['make_stacks'] = lambda cell: [('recount-regression', [], [])]\n"
            "m['run']()\n"
        )
        return subprocess.run(
            [sys.executable, flag, "-c", code],
            capture_output=True,
            text=True,
            check=False,
        )

    def test_matching_recount_passes_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, recount_matches=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("independent recount confirms: 9 bad gammas", result.stdout)

    def test_mismatching_recount_fails_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, recount_matches=False)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("independent recount mismatch: 9 recounted, 9 reported", result.stderr)


if __name__ == "__main__":
    unittest.main()
