"""The exact G466 cumulant certificate must survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "probe_466_centered_cumulant_packet_no_go.py"


class CumulantOptimizationChecks(unittest.TestCase):
    def run_probe(self, optimization, corrupt):
        mutation = """
from fractions import Fraction
original = namespace["cumulants"]
def corrupted(values):
    result = original(values)
    result[4] = Fraction(1)
    return result
globals_dict["cumulants"] = corrupted
""" if corrupt else ""
        code = f"""
import runpy
namespace = runpy.run_path({str(PROBE)!r}, run_name="g466_probe")
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

    def test_exact_packet_rejects_corruption_under_optimization(self):
        for optimization in ("-O", "-OO"):
            with self.subTest(optimization=optimization, corrupt=False):
                result = self.run_probe(optimization, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("Kc_4 = -87878392/2825761 < 0", result.stdout)
            with self.subTest(optimization=optimization, corrupt=True):
                result = self.run_probe(optimization, corrupt=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("AssertionError: 1", result.stderr)


if __name__ == "__main__":
    unittest.main()
