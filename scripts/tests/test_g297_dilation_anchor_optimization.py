# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""G297's coefficient conservation check must survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "g297_dilation_anchor_nogo.py"


class G297DilationAnchorOptimization(unittest.TestCase):
    def run_probe(self, flag, corrupt):
        code = (
            "import runpy\n"
            f"m = runpy.run_path({str(PROBE)!r}, run_name='g297_probe')\n"
        )
        if corrupt:
            code += (
                "original_alignment = m['alignment']\n"
                "calls = [0]\n"
                "def corrupt_alignment(W, R, p, n):\n"
                "    value = original_alignment(W, R, p, n)\n"
                "    calls[0] += 1\n"
                "    return value + (calls[0] == 1)\n"
                "m['main'].__globals__['alignment'] = corrupt_alignment\n"
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

    def test_valid_certificate_passes_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("G297 PASS", result.stdout)

    def test_corrupted_coefficient_family_is_rejected_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("full coefficient family is not zero-sum", result.stderr)


if __name__ == "__main__":
    unittest.main()
