# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""G317's finite-field certificate checks survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "g317_n64_r5_targeted_audit.py"


class G317Optimization(unittest.TestCase):
    def run_certificate(self, flag, corrupt):
        code = (
            "import io, runpy\n"
            f"m = runpy.run_path({str(PROBE)!r}, run_name='g317_probe')\n"
            "g = m['verify_large_field'].__globals__\n"
            "g['subgroup_proth'] = lambda n: [1] * 64\n"
            "g['subset_hist_sparse'] = lambda group, p, max_r: [{} for _ in range(max_r + 1)]\n"
        )
        if corrupt:
            code += (
                "g['quotient_weighted_dot'] = lambda group, dp, p, c: "
                "m['EXPECTED_DOTS'][c] + (c == 2)\n"
            )
        else:
            code += (
                "g['quotient_weighted_dot'] = lambda group, dp, p, c: m['EXPECTED_DOTS'][c]\n"
            )
        code += (
            "out = io.StringIO()\n"
            "m['verify_large_field'](out)\n"
            "print(out.getvalue())\n"
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
                result = self.run_certificate(flag, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("coefficient=2 r=5", result.stdout)

    def test_corrupted_dot_is_rejected_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_certificate(flag, corrupt=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("G317 coefficient-2 dot changed", result.stderr)


if __name__ == "__main__":
    unittest.main()
