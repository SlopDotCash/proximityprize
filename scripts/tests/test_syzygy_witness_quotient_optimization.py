"""Exact probe guards must remain live under Python optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "probe_syzygy_witness_quotient.py"


class OptimizedProbeChecks(unittest.TestCase):
    def run_probe(self, optimization, corrupt):
        mutation = """
original = globals_dict["guarded_pencil_capacity"]
globals_dict["guarded_pencil_capacity"] = lambda n, threshold: original(n, threshold) + 1
""" if corrupt else ""
        code = f"""
import runpy
namespace = runpy.run_path({str(PROBE)!r}, run_name="syzygy_probe")
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

    def test_exact_checks_survive_optimization_and_reject_corruption(self):
        for optimization in ("-O", "-OO"):
            with self.subTest(optimization=optimization, corrupt=False):
                result = self.run_probe(optimization, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("SYZYGY WITNESS-QUOTIENT PROBE: PASS", result.stdout)
            with self.subTest(optimization=optimization, corrupt=True):
                result = self.run_probe(optimization, corrupt=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("syzygy witness-quotient check failed", result.stderr)


if __name__ == "__main__":
    unittest.main()
