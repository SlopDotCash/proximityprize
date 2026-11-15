"""The G268 antipodal census and formula checks must survive optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "g268_antipodal_floor_wraparound_gap.py"


class RuntimeCertificateChecks(unittest.TestCase):
    def run_probe(self, optimization, corrupt):
        mutation = """
original = globals_dict["exact_alignments"]
globals_dict["exact_alignments"] = lambda n, p: (0, 0) if n == 32 else original(n, p)
""" if corrupt else ""
        code = f"""
import runpy
namespace = runpy.run_path({str(PROBE)!r}, run_name="g268_probe")
globals_dict = namespace["main"].__globals__
{mutation}
namespace["main"]()
"""
        return subprocess.run(
            [sys.executable, optimization, "-c", code],
            capture_output=True,
            text=True,
            check=False,
        )

    def test_valid_and_corrupted_census_under_optimization(self):
        for optimization in ("-O", "-OO"):
            with self.subTest(optimization=optimization, corrupt=False):
                result = self.run_probe(optimization, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("G268 PASS:", result.stdout)
                self.assertIn("A5=132970510400 A6=-1324791182208", result.stdout)
            with self.subTest(optimization=optimization, corrupt=True):
                result = self.run_probe(optimization, corrupt=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("G268 antipodal certificate check failed", result.stderr)


if __name__ == "__main__":
    unittest.main()
