# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""G316's finite antipodal formula checks survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "g316_antipodal_closed_formula.py"


class G316Optimization(unittest.TestCase):
    def run_probe(self, flag, corrupt):
        code = (
            "import runpy\n"
            f"m = runpy.run_path({str(PROBE)!r}, run_name='g316_probe')\n"
        )
        if corrupt:
            code += (
                "g = m['main'].__globals__\n"
                "original = g['coeff2_antipodal_dot']\n"
                "g['coeff2_antipodal_dot'] = lambda h, r: original(h, r) + (h == 8 and r == 5)\n"
            )
        code += "m['main']()\n"
        return subprocess.run(
            [sys.executable, flag, "-c", code],
            capture_output=True,
            text=True,
            check=False,
        )

    def test_valid_formula_passes_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("n=16 coefficient=2 all ranks", result.stdout)
                self.assertIn("PASS: coefficient 1 vanishes", result.stdout)

    def test_corrupted_rank_five_formula_is_rejected_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("G316 n=16 rank-5 formula/brute pin failed", result.stderr)


if __name__ == "__main__":
    unittest.main()
