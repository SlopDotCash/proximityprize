# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""The shared-fresh-triple coset certificate checks must survive optimization."""
from pathlib import Path
import subprocess
import sys
import textwrap
import unittest


PROBE = (
    Path(__file__).resolve().parents[1]
    / "probes"
    / "probe_rate_quarter_p1_shared_fresh_triple_refuted.py"
)


def run_probe(flag, corrupt_fresh_coordinate=False):
    code = textwrap.dedent(
        f"""
        from pathlib import Path
        source = Path({str(PROBE)!r}).read_text(encoding="utf-8")
        if {corrupt_fresh_coordinate!r}:
            old, new = "I_RESIDUE = 5", "I_RESIDUE = 1"
            if source.count(old) != 1:
                raise RuntimeError("expected exactly one source substitution")
            source = source.replace(old, new)
        namespace = {{"__name__": "__main__"}}
        exec(compile(source, {str(PROBE)!r}, "exec"), namespace)
        """
    )
    return subprocess.run(
        [sys.executable, flag, "-c", code],
        capture_output=True,
        text=True,
        check=False,
    )


class SharedFreshTripleRefutedOptimization(unittest.TestCase):
    def test_corrupted_fresh_coordinate_is_rejected_under_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe(flag, corrupt_fresh_coordinate=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("fresh coordinate is not shared", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)

    def test_valid_certificate_output_is_unchanged_under_optimization(self):
        outputs = []
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe(flag)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("ALL CHECKS PASSED", result.stdout)
                outputs.append(result.stdout)
        self.assertEqual(outputs[0], outputs[1])


if __name__ == "__main__":
    unittest.main()
