import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PROBE = ROOT / "scripts/probes/probe_ppc10_orbit_census.py"


class Ppc10OrbitCensusValidationTest(unittest.TestCase):
    def test_matched_anchor_runs_under_optimized_python(self):
        completed = subprocess.run(
            [sys.executable, "-O", str(PROBE), "--cell", "128:3"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn("energy=30725120 charZero=30725120", completed.stdout)
        self.assertIn("disjoint=0", completed.stdout)
        self.assertIn("check=True", completed.stdout)

    def test_center_decomposition_mismatch_fails_under_optimization(self):
        source = PROBE.read_text()
        original = "correction = total_centered - base_total"
        self.assertIn(original, source)
        corrupted = source.replace(original, "correction = total_centered - base_total + 1", 1)

        with tempfile.TemporaryDirectory() as temp_dir:
            mutated_probe = Path(temp_dir) / PROBE.name
            mutated_probe.write_text(corrupted)
            for optimization in ("-O", "-OO"):
                with self.subTest(optimization=optimization):
                    completed = subprocess.run(
                        [sys.executable, optimization, str(mutated_probe), "--cell", "16:3"],
                        cwd=ROOT,
                        capture_output=True,
                        text=True,
                        check=False,
                    )

                    self.assertNotEqual(completed.returncode, 0)
                    self.assertIn("support corrections do not sum to correction", completed.stderr)
                    self.assertNotIn("check=False", completed.stdout)


if __name__ == "__main__":
    unittest.main()
