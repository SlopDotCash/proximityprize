# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""G311's exact small and Proth-scale witness checks survive optimization."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "g311_dilation_anchor_scale_audit.py"


class G311ScaleWitnessOptimization(unittest.TestCase):
    def run_probe(self, flag, corrupt):
        code = (
            "import runpy\n"
            f"m = runpy.run_path({str(PROBE)!r}, run_name='g311_probe')\n"
        )
        if corrupt:
            code += (
                "original_alignment = m['sparse_alignment']\n"
                "changed = [False]\n"
                "def corrupt_alignment(group, p, r, coefficient):\n"
                "    result = original_alignment(group, p, r, coefficient)\n"
                "    if p == m['PROTH_P'] and coefficient == 2 and not changed[0]:\n"
                "        changed[0] = True\n"
                "        return result[0] + 1, result[1]\n"
                "    return result\n"
                "m['main'].__globals__['sparse_alignment'] = corrupt_alignment\n"
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

    def test_valid_scale_audit_passes_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("PASS: coefficient-1 sign does not transport", result.stdout)

    def test_corrupted_proth_scale_witness_is_rejected_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("G311 sparse exact witness pin failed", result.stderr)


if __name__ == "__main__":
    unittest.main()
