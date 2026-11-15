# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""G272's exact witnesses for the Lean no-go must remain checked under -O/-OO."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "g272_single_character_dominance_probe.py"


class G272SingleCharacterOptimization(unittest.TestCase):
    def test_exact_witnesses_pass_under_optimization(self):
        code = f"import runpy; m=runpy.run_path({str(PROBE)!r}); m['main']()"
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = subprocess.run(
                    [sys.executable, flag, "-c", code],
                    capture_output=True,
                    text=True,
                    check=False,
                )
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("all Lean witnesses match exactly", result.stdout)

    def test_corrupted_lean_witness_is_rejected_under_optimization(self):
        code = (
            "import runpy\n"
            f"m = runpy.run_path({str(PROBE)!r}, run_name='g272_probe')\n"
            "original_cell = m['cell']\n"
            "def corrupt_cell(n, p, r):\n"
            "    result = original_cell(n, p, r)\n"
            "    if p == 929:\n"
            "        result = dict(result)\n"
            "        result['A'] += 1\n"
            "    return result\n"
            "m['main'].__globals__['cell'] = corrupt_cell\n"
            "m['main']()\n"
        )
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = subprocess.run(
                    [sys.executable, flag, "-c", code],
                    capture_output=True,
                    text=True,
                    check=False,
                )
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("G272 exact witness pin failed for p=929", result.stderr)


if __name__ == "__main__":
    unittest.main()
