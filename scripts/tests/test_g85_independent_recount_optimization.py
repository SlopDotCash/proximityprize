# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""G85's independent witness recount remains enforced under Python optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = (
    Path(__file__).resolve().parents[1]
    / "probes"
    / "probe_rate_half_predecessor_count_largefield.py"
)


class IndependentRecountOptimization(unittest.TestCase):
    def run_recount(self, flag, corrupt):
        alternate_verifies = "not alt" if corrupt else "True"
        code = (
            "import random, runpy, types\n"
            f"m = runpy.run_path({str(PROBE)!r})\n"
            "g = m['analyze_stack'].__globals__\n"
            f"g['verify_bad'] = lambda dom, u0, u1, gam, subset, alt=False: {alternate_verifies}\n"
            "dom = types.SimpleNamespace(n=1, p=3)\n"
            "checks = types.SimpleNamespace(\n"
            "    pool=[[0], [1]],\n"
            "    candidates=lambda u0, u1: ({0: 0, 1: 1}, []),\n"
            ")\n"
            "result = m['analyze_stack'](dom, checks, 'recount-regression', [], [], random.Random(0))\n"
            "print(result)\n"
        )
        return subprocess.run(
            [sys.executable, flag, "-c", code],
            capture_output=True,
            text=True,
            check=False,
        )

    def test_consistent_recount_passes_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_recount(flag, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("'certified': 2", result.stdout)

    def test_mismatched_recount_fails_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_recount(flag, corrupt=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("recount mismatch 0 != 2", result.stderr)


if __name__ == "__main__":
    unittest.main()
