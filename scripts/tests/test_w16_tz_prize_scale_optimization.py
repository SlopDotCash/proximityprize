"""The W16 TZ prime-witness checks must survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import textwrap
import unittest


PROBES = Path(__file__).resolve().parents[1] / "probes"


def run_probe(flag, body):
    code = textwrap.dedent(
        f"""
        import sys
        sys.path.insert(0, {str(PROBES)!r})
        import probe_w16_tz_prize_scale as probe
        """
    ) + textwrap.dedent(body)
    return subprocess.run(
        [sys.executable, flag, "-c", code],
        capture_output=True,
        text=True,
        check=False,
    )


class W16TZPrizeScaleOptimization(unittest.TestCase):
    def test_composite_witness_is_rejected_under_optimization(self):
        body = """
            probe.is_prime = lambda n: n % 2 == 1 and n > 1
            probe.sieve_rung(16)
            print("ALL CHECKS PASSED")
            """
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe(flag, body)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("Fermat check fails for p=4295032833", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)

    def test_number_above_the_deterministic_limit_is_rejected_under_optimization(self):
        body = """
            probe.is_prime(probe.DET_LIMIT)
            print("ALL CHECKS PASSED")
            """
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe(flag, body)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("above the deterministic Miller-Rabin limit", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)


if __name__ == "__main__":
    unittest.main()
