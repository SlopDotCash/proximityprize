# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""G310's exact tail-floor certificate checks must survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "g310_tail_floor_scale_audit.py"


class G310TailFloorOptimization(unittest.TestCase):
    def test_valid_small_cell_passes_optimized(self):
        code = (
            "import runpy; "
            f"m=runpy.run_path({str(PROBE)!r}); "
            "r=m['analyze'](97, 8, 33)\n"
            "if r['sumsq'] != r['floor'] or r['floor'] != 13:\n"
            "    raise RuntimeError('unexpected n=8 cell')"
        )
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = subprocess.run(
                    [sys.executable, flag, "-c", code],
                    capture_output=True,
                    text=True,
                    check=False,
                )
                self.assertEqual(result.returncode, 0, result.stderr)

    def test_corrupted_floor_is_rejected_optimized(self):
        source = PROBE.read_text(encoding="utf-8")
        expression = "sumsq = sum(k * k for k in ks)"
        self.assertEqual(source.count(expression), 1)
        corrupt = source.replace(expression, expression + " + 1")
        with tempfile.TemporaryDirectory() as directory:
            corrupt_probe = Path(directory) / PROBE.name
            corrupt_probe.write_text(corrupt, encoding="utf-8")
            code = (
                "import runpy; "
                f"m=runpy.run_path({str(corrupt_probe)!r}); "
                "m['analyze'](97, 8, 33)"
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
                    self.assertIn("tail-floor equivalence failed", result.stderr)


if __name__ == "__main__":
    unittest.main()
