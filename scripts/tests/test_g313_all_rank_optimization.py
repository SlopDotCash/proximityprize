# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""G313's exact all-rank scale checks survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "g313_all_rank_window_scale_audit.py"


class G313AllRankOptimization(unittest.TestCase):
    def run_probe(self, flag, corrupt):
        code = (
            "import runpy\n"
            f"m = runpy.run_path({str(PROBE)!r}, run_name='g313_probe')\n"
        )
        if corrupt:
            code += (
                "g = m['main'].__globals__\n"
                "original_alignments = g['alignments']\n"
                "changed = [False]\n"
                "def corrupt_alignments(group, p, max_r, coefficients):\n"
                "    rows = original_alignments(group, p, max_r, coefficients)\n"
                "    if p == g['PROTH_P'] and not changed[0]:\n"
                "        changed[0] = True\n"
                "        rows[2][0] = rows[2][0][0] + 1, rows[2][0][1]\n"
                "    return rows\n"
                "g['alignments'] = corrupt_alignments\n"
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

    def test_valid_all_rank_scale_audit_passes_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("coefficient 2 is positive for every adjacent rank", result.stdout)

    def test_corrupted_first_rank_is_rejected_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("G313 alignment formula failed at r=1", result.stderr)


if __name__ == "__main__":
    unittest.main()
