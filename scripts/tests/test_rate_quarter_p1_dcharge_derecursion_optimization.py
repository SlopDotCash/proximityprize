"""The rate-quarter D-charge derecursion checks must survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import textwrap
import unittest


PROBE = (
    Path(__file__).resolve().parents[1]
    / "probes"
    / "probe_rate_quarter_p1_dcharge_derecursion.py"
)


def run_probe_with(flag, old, new):
    """Import the probe with one constant changed; the module runs its MDS-pool check."""
    code = textwrap.dedent(
        f"""
        source = open({str(PROBE)!r}, encoding="utf-8").read()
        assert source.count({old!r}) == 1
        source = source.replace({old!r}, {new!r})
        exec(compile(source, "probe", "exec"), {{"__name__": "probe"}})
        print("ALL CHECKS PASSED")
        """
    )
    return subprocess.run(
        [sys.executable, flag, "-c", code],
        capture_output=True,
        text=True,
        check=False,
    )


class RateQuarterDChargeDerecursionOptimization(unittest.TestCase):
    def test_wrong_threshold_is_rejected_under_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe_with(flag, "T = 592794966\n", "T = 592794967\n")
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("max level-2 threshold is not 193887475", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)

    def test_wrong_dimension_is_rejected_under_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe_with(flag, "K = 2**28\n", "K = 2**28 + 4\n")
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("floor(sqrt(T(k-1))) is not 398907491", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)


if __name__ == "__main__":
    unittest.main()
