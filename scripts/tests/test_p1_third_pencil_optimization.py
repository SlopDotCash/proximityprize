"""The P1 third-pencil certificate checks must survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import textwrap
import unittest


PROBES = Path(__file__).resolve().parents[1] / "probes"


class P1ThirdPencilOptimization(unittest.TestCase):
    def test_jointly_explainable_witness_is_rejected_under_optimization(self):
        code = textwrap.dedent(
            f"""
            import sys
            sys.path.insert(0, {str(PROBES)!r})
            import probe_rate_quarter_p1_third_pencil as probe

            probe.explainable = lambda *args, **kwargs: True
            probe.part1_midscale()
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
                self.assertIn("witness 0 jointly explainable", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)


if __name__ == "__main__":
    unittest.main()
