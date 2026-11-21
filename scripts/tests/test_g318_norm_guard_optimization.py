# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""G318's Proth-prime norm guard remains enforced under Python optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "g318_n64_r6_norm_guard.py"


class G318NormGuardOptimization(unittest.TestCase):
    def run_probe(self, flag, fake_prime):
        code = (
            "import runpy\n"
            f"m = runpy.run_path({str(PROBE)!r}, run_name='g318_probe')\n"
        )
        if fake_prime:
            code += "m['main'].__globals__['L1_BOUND'] = 1 << 20\n"
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

    def test_valid_norm_guard_passes_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, fake_prime=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("p > 14^32", result.stdout)
                self.assertIn("forced to equal the antipodal-model count", result.stdout)

    def test_prime_below_norm_bound_is_rejected_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, fake_prime=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("norm guard failed", result.stderr)


if __name__ == "__main__":
    unittest.main()
