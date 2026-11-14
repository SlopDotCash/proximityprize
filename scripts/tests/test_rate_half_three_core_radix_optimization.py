"""The three-core rate-half radix certificate checks must survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import textwrap
import unittest


PROBE = (
    Path(__file__).resolve().parents[1]
    / "probes"
    / "probe_rate_half_three_core_radix_counterexample.py"
)


def run_probe_with(flag, old, new):
    """Run the probe (all checks are at module level) with one source line changed."""
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


class RateHalfThreeCoreRadixOptimization(unittest.TestCase):
    def test_wrong_generator_is_rejected_under_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe_with(
                    flag,
                    "G = 303645430271030343624574566109998498685964493478\n",
                    "G = 303645430271030343624574566109998498685964493479\n",
                )
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("base generator", result.stderr)
                self.assertNotIn("hyperplane_avoidance_budget=PASS", result.stdout)

    def test_wrong_core_size_is_rejected_under_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe_with(
                    flag, "    542424784538028885,\n", "    542424784538028884,\n"
                )
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("a core does not have 33 points", result.stderr)
                self.assertNotIn("hyperplane_avoidance_budget=PASS", result.stdout)


if __name__ == "__main__":
    unittest.main()
