# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""G314's exact antipodal model comparisons survive Python optimization."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "g314_antipodal_relation_model.py"


class G314AntipodalModelOptimization(unittest.TestCase):
    def run_probe(self, flag, corrupt):
        code = (
            "import runpy\n"
            f"m = runpy.run_path({str(PROBE)!r}, run_name='g314_probe')\n"
        )
        if corrupt:
            code += (
                "g = m['main'].__globals__\n"
                "original_model_dot = g['antipodal_model_dot']\n"
                "changed = [False]\n"
                "def corrupt_model_dot(n, r, coefficient):\n"
                "    value = original_model_dot(n, r, coefficient)\n"
                "    if not changed[0]:\n"
                "        changed[0] = True\n"
                "        return value + 1\n"
                "    return value\n"
                "g['antipodal_model_dot'] = corrupt_model_dot\n"
            )
        code += (
            "try:\n"
            "    m['main']()\n"
            "except SystemExit as result:\n"
            "    if result.code != 0:\n"
            "        raise\n"
        )
        with tempfile.TemporaryDirectory() as temp_dir:
            return subprocess.run(
                [sys.executable, flag, "-c", code],
                env={**os.environ, "TMPDIR": temp_dir},
                capture_output=True,
                text=True,
                check=False,
            )

    def test_valid_model_relations_pass_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("exactly the antipodal-pair relation model", result.stdout)

    def test_corrupted_model_table_is_rejected_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("G314 exact antipodal model table changed", result.stderr)


if __name__ == "__main__":
    unittest.main()
