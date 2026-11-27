"""The P1 layer-cake certificate checks must survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import textwrap
import unittest


PROBE = (
    Path(__file__).resolve().parents[1]
    / "probes"
    / "probe_rate_quarter_p1_layer_cake.py"
)


def run_probe(flag, old=None, new=None):
    """Run the probe, optionally with one source constant replaced."""
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


class RateQuarterP1LayerCakeOptimization(unittest.TestCase):
    def test_published_certificate_passes_under_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe(flag)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("Johnson threshold isqrt(N(k-1)) = 536870910", result.stdout)
                self.assertIn("10 : 539356427  above=True  J(A_phi) = 108", result.stdout)
                self.assertIn("9 : 532676609  above=False", result.stdout)
                self.assertIn(
                    "1 + 3*(N-T) = 1442840575 > N = 1073741824",
                    result.stdout,
                )
                self.assertIn(
                    "greedy heavy-side layer-cake maximum (info only): 2404735416",
                    result.stdout,
                )
                self.assertIn("ALL CHECKS PASSED", result.stdout)

    def test_wrong_threshold_is_rejected_under_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe(flag, "T = 592794966\n", "T = 592794967\n")
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn(
                    "10-rider alignment floor is not 539356427",
                    result.stderr,
                )
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)

    def test_wrong_domain_is_rejected_under_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe(flag, "N = 2**30\n", "N = 2**30 + 1\n")
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("Johnson threshold is not 536870910", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)


if __name__ == "__main__":
    unittest.main()
