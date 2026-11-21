# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""G302's exact Lean witness pins must remain active under Python optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "g302_common_order7_normal_nogo.py"


class G302OrderSevenWitnessOptimization(unittest.TestCase):
    def run_probe(self, flag, corrupt):
        code = (
            "import runpy\n"
            f"m = runpy.run_path({str(PROBE)!r}, run_name='g302_probe')\n"
        )
        if corrupt:
            code += (
                "original_run_cell = m['run_cell']\n"
                "calls = [0]\n"
                "def corrupt_run_cell(n, p):\n"
                "    rows = original_run_cell(n, p)\n"
                "    if (n, p) == (16, 113):\n"
                "        calls[0] += 1\n"
                "        if calls[0] == 2:\n"
                "            rows = [(r, target + (r == 5), normal) for r, target, normal in rows]\n"
                "    return rows\n"
                "m['main'].__globals__['run_cell'] = corrupt_run_cell\n"
            )
        code += (
            "try:\n"
            "    m['main']()\n"
            "except SystemExit as result:\n"
            "    if result.code != 0:\n"
            "        raise\n"
        )
        return subprocess.run(
            [sys.executable, flag, "-c", code],
            capture_output=True,
            text=True,
            check=False,
        )

    def test_valid_sponsor_census_passes_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("PASS: the unique common nonprincipal bounded sponsor order is seven", result.stdout)

    def test_corrupted_exact_witness_is_rejected_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("G302 exact Lean witness pin failed", result.stderr)


if __name__ == "__main__":
    unittest.main()
