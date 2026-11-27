"""The P1 pencil-count charge checks must survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import textwrap
import unittest


PROBE = (
    Path(__file__).resolve().parents[1]
    / "probes"
    / "probe_rate_quarter_p1_pencil_count_charge.py"
)
PROBES = PROBE.parent

# Stdout of the published certificate. A successful optimized run must match it.
PUBLISHED_STDOUT = """\
  one-pencil: riders=3, aligned=112: vote bounds verified
part 1 verified
  pencil-A: riders=2, aligned=64: vote bounds verified
  pencil-B: riders=2, aligned=64: vote bounds verified
part 2 verified: BasePencilImageCap boundary (image card = 2) is attained by a genuine bad family
part 3 verified: literal P1 constants
  N*(K-1) = 288230375077969920
  10-rider floor 539356427, square 290905355346206329
  9-rider floor 532676609, square 283744369775738881
ALL CHECKS PASSED
"""


def run_probe_with(flag, old, new):
    """Run main() with one source line changed."""
    code = textwrap.dedent(
        f"""
        source = open({str(PROBE)!r}, encoding="utf-8").read()
        count = source.count({old!r})
        if count != 1:
            raise AssertionError(f"expected one occurrence, found {{count}}")
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


def run_imported(flag, body):
    """Import the published probe and run body under an optimization flag."""
    code = textwrap.dedent(
        f"""
        import sys
        sys.path.insert(0, {str(PROBES)!r})
        import probe_rate_quarter_p1_pencil_count_charge as probe
        """
    ) + textwrap.dedent(body)
    return subprocess.run(
        [sys.executable, flag, "-c", code],
        capture_output=True,
        text=True,
        check=False,
    )


class RateQuarterPencilCountChargeOptimization(unittest.TestCase):
    def test_published_certificate_passes_under_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = subprocess.run(
                    [sys.executable, flag, str(PROBE)],
                    capture_output=True,
                    text=True,
                    check=False,
                )
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout, PUBLISHED_STDOUT)
                self.assertEqual(result.stderr, "")

    def test_shifted_threshold_is_rejected_under_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe_with(flag, "T = 592794966\n", "T = 592794967\n")
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("N - T is not 480946858", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)
                self.assertNotIn("part 3 verified", result.stdout)

    def test_short_witness_threshold_is_rejected_under_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe_with(flag, "T_SMALL = 142\n", "T_SMALL = 145\n")
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("witness shorter than threshold", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)
                self.assertNotIn("part 1 verified", result.stdout)

    def test_rider_off_the_pencil_is_rejected_under_optimization(self):
        body = """
            domain = 4
            support = [0]
            # Riders 1 and 2 span the zero pencil and agree with the zero word.
            # Rider 3 agrees at the witness coordinate and leaves the pencil later.
            riders = {
                1: (support, [0, 0, 0, 0]),
                2: (support, [0, 0, 0, 0]),
                3: (support, [0, 0, 0, 9]),
            }
            probe.check_pencil_bounds(
                [0] * domain, [0] * domain, riders, domain, 1,
                [1, 2, 3, 4], "off-pencil")
            print("ALL CHECKS PASSED")
            """
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_imported(flag, body)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("off-pencil: rider 3 not on the common pencil", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)


if __name__ == "__main__":
    unittest.main()
