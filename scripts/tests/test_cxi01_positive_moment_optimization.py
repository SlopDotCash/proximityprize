# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""CXI01's full-depth null-column check must survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "probe_cxi01_positive_moment_cone.py"


class CXI01PositiveMomentOptimization(unittest.TestCase):
    def run_probe(self, flag, corrupt):
        code = (
            "import runpy\n"
            f"m = runpy.run_path({str(PROBE)!r}, run_name='cxi01_probe')\n"
        )
        if corrupt:
            code += (
                "original_falling = m['falling']\n"
                "def corrupt_falling(n, order):\n"
                "    return original_falling(n, order) + (n == 0)\n"
                "m['audit'].__globals__['falling'] = corrupt_falling\n"
            )
        code += "m['audit'](8)\n"
        return subprocess.run(
            [sys.executable, flag, "-c", code],
            capture_output=True,
            text=True,
            check=False,
        )

    def test_valid_moment_cone_passes_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("full_depth_column=ZERO", result.stdout)

    def test_corrupted_full_depth_column_is_rejected_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("full-depth column is not zero", result.stderr)


if __name__ == "__main__":
    unittest.main()
