# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""G307's exact trace feature and positive circuit pins survive optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "g307_sponsor_two_conductor15_span_nogo.py"


class G307CircuitCertificateOptimization(unittest.TestCase):
    def run_probe(self, flag, corrupt):
        code = (
            "import runpy\n"
            f"m = runpy.run_path({str(PROBE)!r}, run_name='g307_probe')\n"
        )
        if corrupt:
            code += (
                "g = m['main'].__globals__\n"
                "original_cell = g['run_cell']\n"
                "changed = [False]\n"
                "def corrupt_cell(n, p, r):\n"
                "    target, features = original_cell(n, p, r)\n"
                "    if not changed[0]:\n"
                "        changed[0] = True\n"
                "        features = (features[0] + 1, *features[1:])\n"
                "    return target, features\n"
                "g['run_cell'] = corrupt_cell\n"
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

    def test_valid_positive_circuit_passes_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("exact positive circuit forbids every fixed separator", result.stdout)

    def test_corrupted_trace_feature_is_rejected_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("G307 exact trace feature pin failed", result.stderr)


if __name__ == "__main__":
    unittest.main()
