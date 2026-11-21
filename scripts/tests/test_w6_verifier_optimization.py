"""The W6 solver's independent signature verifier must survive optimization."""
from pathlib import Path
import subprocess
import sys
import unittest


PROBE = Path(__file__).resolve().parents[1] / "probes" / "probe_w6_kfour_sourcesix_cpsat.py"


class VerifierOptimizationChecks(unittest.TestCase):
    def run_verifier(self, optimization, case):
        signatures = {
            "valid": "[(set(range(3)), set(range(4))), (set(range(3, 6)), set(range(4, 8)))]",
            "pair_law": "[(set(range(3)), set(range(4)))] * 5",
            "witness_limit": "[(set(range(3)), set(e)) for e in ((0,1,2,3),(0,1,4,5),(0,1,6,7),(0,2,4,6),(0,2,5,7))]",
        }[case]
        code = f"""
import runpy, sys, types
for name in ("ortools", "ortools.sat", "ortools.sat.python"):
    sys.modules[name] = types.ModuleType(name)
cp_model = types.ModuleType("ortools.sat.python.cp_model")
sys.modules["ortools.sat.python.cp_model"] = cp_model
namespace = runpy.run_path({str(PROBE)!r}, run_name="w6_probe")
namespace["verify"]({signatures})
"""
        return subprocess.run(
            [sys.executable, optimization, "-c", code],
            capture_output=True,
            text=True,
            check=False,
        )

    def test_pair_law_and_witness_limit_stay_enforced(self):
        for optimization in ("-O", "-OO"):
            with self.subTest(optimization=optimization, case="valid"):
                result = self.run_verifier(optimization, "valid")
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("balanced=0 max_witnesses=0", result.stdout)
            for case, message in (
                ("pair_law", "pair law violated"),
                ("witness_limit", "balanced witness limit exceeded: 3"),
            ):
                with self.subTest(optimization=optimization, case=case):
                    result = self.run_verifier(optimization, case)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn(message, result.stderr)


if __name__ == "__main__":
    unittest.main()
