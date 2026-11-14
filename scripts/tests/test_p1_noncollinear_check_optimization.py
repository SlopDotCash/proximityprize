# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""P1 non-collinear witness checks must survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import textwrap
import unittest


PROBES = Path(__file__).resolve().parents[1] / "probes"


class P1NoncollinearCheckOptimization(unittest.TestCase):
    def test_corrupted_witness_is_rejected_under_optimization(self):
        code = textwrap.dedent(
            f"""
            import sys
            sys.path.insert(0, {str(PROBES)!r})
            import probe_rate_quarter_p1_noncollinear_triple as probe

            cert = probe.build()
            cert["u0"][0] = (cert["u0"][0] + 1) % probe.Q
            probe.check(cert)
            print("ALL CHECKS PASSED")
            """
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
                self.assertIn("(1, 0)", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)


if __name__ == "__main__":
    unittest.main()
