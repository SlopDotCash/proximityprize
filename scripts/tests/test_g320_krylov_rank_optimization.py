# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""G320's exact Krylov rank and determinant pins survive optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "g320_krylov_d2_countermodel_stdlib.py"


class G320KrylovRankOptimization(unittest.TestCase):
    def run_probe(self, flag, corrupt):
        code = (
            "import runpy\n"
            f"m = runpy.run_path({str(PROBE)!r}, run_name='g320_probe')\n"
        )
        if corrupt:
            code += (
                "g = m['main'].__globals__\n"
                "original_rank = g['rank_int']\n"
                "changed = [False]\n"
                "def corrupt_rank(matrix):\n"
                "    rank = original_rank(matrix)\n"
                "    if matrix and len(matrix[0]) == 4 and not changed[0]:\n"
                "        changed[0] = True\n"
                "        return rank + 1\n"
                "    return rank\n"
                "g['rank_int'] = corrupt_rank\n"
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

    def test_valid_krylov_rank_certificates_pass_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("rank structure CHECKED at both cells", result.stdout)
                self.assertIn("det=-285768", result.stdout)

    def test_corrupted_augmented_rank_is_rejected_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("rank_aug=5, expected 4", result.stderr)


if __name__ == "__main__":
    unittest.main()
