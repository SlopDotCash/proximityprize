"""The shared-fresh-coordinate countermodel checks must survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import textwrap
import unittest


PROBE = (
    Path(__file__).resolve().parents[1]
    / "probes"
    / "probe_rate_quarter_p1_shared_fresh_coordinate.py"
)


def run_probe_with(flag, old, new):
    """Run the probe's main() with one source line changed."""
    code = textwrap.dedent(
        f"""
        source = open({str(PROBE)!r}, encoding="utf-8").read()
        assert source.count({old!r}) == 1
        source = source.replace({old!r}, {new!r})
        namespace = {{"__name__": "probe"}}
        exec(compile(source, "probe", "exec"), namespace)
        namespace["main"]()
        """
    )
    return subprocess.run(
        [sys.executable, flag, "-c", code],
        capture_output=True,
        text=True,
        check=False,
    )


class RateQuarterSharedFreshCoordinateOptimization(unittest.TestCase):
    def test_absorbed_shared_coordinate_is_rejected_under_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe_with(
                    flag, "A_VAL, B_VAL = 1, 1 ", "A_VAL, B_VAL = 9, 7 "
                )
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("the joint pair agrees with the stack", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)

    def test_wrong_threshold_is_rejected_under_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe_with(
                    flag,
                    "    T = 592794966            # predecessorThreshold\n",
                    "    T = 592794967            # predecessorThreshold\n",
                )
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("N - T is not 480946858", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)


if __name__ == "__main__":
    unittest.main()
