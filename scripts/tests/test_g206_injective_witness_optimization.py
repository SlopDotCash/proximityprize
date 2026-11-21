# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""G206's exact injective-cell witness pins must survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "g206_weighted_kernel_injective_nogo.py"


class G206InjectiveWitnessOptimization(unittest.TestCase):
    def run_probe(self, flag, corrupt):
        code = (
            "import runpy\n"
            f"m = runpy.run_path({str(PROBE)!r}, run_name='g206_probe')\n"
        )
        if corrupt:
            code += (
                "late = m['late']\n"
                "original_row = late.row\n"
                "changed = [False]\n"
                "def corrupt_row(n, p, r):\n"
                "    row = original_row(n, p, r)\n"
                "    if not changed[0]:\n"
                "        changed[0] = True\n"
                "        return {**row, 'A': row['A'] + 1}\n"
                "    return row\n"
                "late.row = corrupt_row\n"
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

    def test_valid_injective_cells_pass_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("collision_free=True maxW=1", result.stdout)

    def test_corrupted_exact_witness_is_rejected_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("G206 exact A5/A6 witness pin failed", result.stderr)


if __name__ == "__main__":
    unittest.main()
