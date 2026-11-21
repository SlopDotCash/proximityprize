# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""G315's n=32 model dot pins survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "g315_n32_antipodal_live_ranks.py"


class G315ModelOptimization(unittest.TestCase):
    def run_model(self, flag, corrupt):
        code = (
            "import io, runpy\n"
            f"m = runpy.run_path({str(PROBE)!r}, run_name='g315_probe')\n"
        )
        if corrupt:
            code += (
                "g = m['verify_model'].__globals__\n"
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
        code += "m['verify_model'](io.StringIO())\n"
        return subprocess.run(
            [sys.executable, flag, "-c", code],
            capture_output=True,
            text=True,
            check=False,
        )

    def test_valid_model_dots_pass_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_model(flag, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("model coefficient=2 r=6 dot=200992512", result.stdout)

    def test_corrupted_model_dot_is_rejected_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_model(flag, corrupt=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("G315 exact model dot pin failed", result.stderr)


if __name__ == "__main__":
    unittest.main()
