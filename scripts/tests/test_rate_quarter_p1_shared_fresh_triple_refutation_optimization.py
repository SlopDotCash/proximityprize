"""The shared-fresh-triple refutation checks must survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import textwrap
import unittest


PROBE = (
    Path(__file__).resolve().parents[1]
    / "probes"
    / "probe_rate_quarter_p1_shared_fresh_triple_refutation.py"
)


def run_probe(flag, old=None, new=None):
    """Run the probe, optionally with one source line replaced."""
    if old is None:
        return subprocess.run(
            [sys.executable, flag, str(PROBE)],
            capture_output=True,
            text=True,
            check=False,
        )
    code = textwrap.dedent(
        f"""
        source = open({str(PROBE)!r}, encoding="utf-8").read()
        assert source.count({old!r}) == 1
        source = source.replace({old!r}, {new!r})
        exec(compile(source, "probe", "exec"), {{"__name__": "__main__"}})
        print("ALL CHECKS PASSED")
        """
    )
    return subprocess.run(
        [sys.executable, flag, "-c", code],
        capture_output=True,
        text=True,
        check=False,
    )


class RateQuarterSharedFreshTripleRefutationOptimization(unittest.TestCase):
    def test_published_certificate_passes_under_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe(flag)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn('"T": 592794966', result.stdout)
                self.assertIn('"pair_intersection_floor": 111848108', result.stdout)
                self.assertIn('"shared_fresh_fiber_size": 480946859', result.stdout)
                self.assertIn("ALL CHECKS PASSED", result.stdout)

    def test_two_exceptional_points_are_rejected_under_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe(
                    flag,
                    "exceptional = fiber_points[:3]\n",
                    "exceptional = fiber_points[:2]\n",
                )
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("expected 3 distinct gammas", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)

    def test_wrong_q0_coefficient_is_rejected_under_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe(
                    flag,
                    "q0 = poly_mul([0, 1], q1, prime)\n",
                    "q0 = poly_mul([0, 2], q1, prime)\n",
                )
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn(
                    "line does not agree with the stack on the witness",
                    result.stderr,
                )
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)


if __name__ == "__main__":
    unittest.main()
