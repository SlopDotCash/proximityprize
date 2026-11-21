# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""G315's n=32 model and live-rank pins survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "g315_n32_antipodal_live_ranks.py"


class G315LiveRankOptimization(unittest.TestCase):
    def run_probe(self, flag, corrupt):
        code = (
            "import runpy\n"
            f"m = runpy.run_path({str(PROBE)!r}, run_name='g315_probe')\n"
        )
        if corrupt:
            code += (
                "g = m['main'].__globals__\n"
                "original_dot = g['antipodal_model_dot']\n"
                "changed = [False]\n"
                "def corrupt_dot(n, r, coefficient):\n"
                "    value = original_dot(n, r, coefficient)\n"
                "    if not changed[0]:\n"
                "        changed[0] = True\n"
                "        return value + 1\n"
                "    return value\n"
                "g['antipodal_model_dot'] = corrupt_dot\n"
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

    def test_valid_n32_live_rank_audit_passes_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("exact field dot table matches the antipodal-pair model", result.stdout)

    def test_corrupted_model_dot_is_rejected_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("G315 exact model dot pin failed", result.stderr)


if __name__ == "__main__":
    unittest.main()
