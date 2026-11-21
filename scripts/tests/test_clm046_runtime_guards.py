# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""CLM-046 exact certificate pins remain active under Python optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = (
    Path(__file__).resolve().parents[1]
    / "probes"
    / "probe_clm046_f41_two_label_fingerprint.py"
)


class CLM046RuntimeGuards(unittest.TestCase):
    def run_probe(self, flag, corrupt):
        code = (
            "import runpy\n"
            f"m = runpy.run_path({str(PROBE)!r}, run_name='clm046_probe')\n"
        )
        if corrupt:
            code += (
                "m['main'].__globals__['EXPECTED_EXTRAS'] = (41, 42, 43, 44, 45, 46, 47)\n"
            )
        code += "m['main']()\n"
        return subprocess.run(
            [sys.executable, flag, "-c", code],
            capture_output=True,
            text=True,
            check=False,
        )

    def test_valid_exact_certificate_passes_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("fingerprints: inputs=225", result.stdout)
                self.assertIn("PASS: all exact runtime checks reproduced", result.stdout)

    def test_corrupted_exact_pin_fails_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("CLM-046 runtime check failed", result.stderr)


if __name__ == "__main__":
    unittest.main()
