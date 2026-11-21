# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""G309's exact nonnegative-row counterexample survives Python optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "g309_target_oriented_cubic_generic_row_nogo.py"


class G309GenericRowOptimization(unittest.TestCase):
    def run_probe(self, flag, corrupt):
        code = (
            "import runpy\n"
            f"m = runpy.run_path({str(PROBE)!r}, run_name='g309_probe')\n"
        )
        if corrupt:
            code += (
                "g = m['main'].__globals__\n"
                "mod = g['MOD']\n"
                "subgroup = mod.subgroup(73, 8, mod.primitive_root(73))\n"
                "kernel2 = mod.weighted_kernel(subgroup, 73, 2)\n"
                "original_alignment = mod.alignment\n"
                "changed = [False]\n"
                "def corrupt_alignment(kernel, row, p, n):\n"
                "    value = original_alignment(kernel, row, p, n)\n"
                "    if p == 73 and n == 8 and kernel == kernel2 and row[4] == 1 and sum(row) == 1 and not changed[0]:\n"
                "        changed[0] = True\n"
                "        return value + 1\n"
                "    return value\n"
                "mod.alignment = corrupt_alignment\n"
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

    def test_valid_nonnegative_row_control_passes_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("nonnegative delta-row counterexamples: 8", result.stdout)
                self.assertIn("generic nonnegative-row transfer is false", result.stdout)

    def test_corrupted_targeted_witness_is_rejected_optimized(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_probe(flag, corrupt=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("G309 exact target-oriented cubic witness pin failed", result.stderr)


if __name__ == "__main__":
    unittest.main()
