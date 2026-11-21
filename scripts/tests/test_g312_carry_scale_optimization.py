# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""G312's exact carry census pins survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "g312_carry_scale_audit.py"


class G312CarryScaleOptimization(unittest.TestCase):
    def run_probe(self, flag, corrupt):
        code = (
            "import runpy\n"
            f"m = runpy.run_path({str(PROBE)!r}, run_name='g312_probe')\n"
        )
        if corrupt:
            code += (
                "g = m['main'].__globals__\n"
                "original_census = g['carry_census']\n"
                "changed = [False]\n"
                "def corrupt_census(group, p, r):\n"
                "    row = original_census(group, p, r)\n"
                "    if p == g['PROTH_P'] and r == 5 and not changed[0]:\n"
                "        changed[0] = True\n"
                "        return {**row, 'J': row['J'] + 1}\n"
                "    return row\n"
                "g['carry_census'] = corrupt_census\n"
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

    def test_valid_carry_scale_audit_passes_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("all checked large-cell mass is carry 0", result.stdout)

    def test_corrupted_proth_census_is_rejected_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("G312 carry total disagrees with direct modular count", result.stderr)


if __name__ == "__main__":
    unittest.main()
