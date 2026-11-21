"""The SYZ3 production and finite-field checks must survive optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "probe_syz3_five_core_predecessor.py"


class RuntimeCertificateChecks(unittest.TestCase):
    def run_probe(self, optimization, corrupt):
        mutation = 'globals_dict["height"] = lambda _label: 0' if corrupt else ""
        operation = 'globals_dict["finite_check"]()' if corrupt else """
first = globals_dict["check_production_field"](globals_dict["P_FIRST"], globals_dict["BUDGET_FIRST"])
second = globals_dict["check_production_field"](globals_dict["P_SECOND"], globals_dict["BUDGET_SECOND"])
finite = globals_dict["finite_check"]()
print({"first": first, "second": second, "finite": finite})
"""
        code = f"""
import runpy
namespace = runpy.run_path({str(PROBE)!r}, run_name="syz3_probe")
globals_dict = namespace["check_production_field"].__globals__
{mutation}
{operation}
"""
        return subprocess.run(
            [sys.executable, optimization, "-c", code],
            capture_output=True,
            text=True,
            check=False,
        )

    def test_valid_and_corrupted_certificates_under_optimization(self):
        for optimization in ("-O", "-OO"):
            with self.subTest(optimization=optimization, corrupt=False):
                result = self.run_probe(optimization, corrupt=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("'distinct_scalars': 310", result.stdout)
            with self.subTest(optimization=optimization, corrupt=True):
                result = self.run_probe(optimization, corrupt=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("SYZ3 five-core certificate check failed", result.stderr)


if __name__ == "__main__":
    unittest.main()
