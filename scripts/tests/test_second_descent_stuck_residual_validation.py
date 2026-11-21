import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PROBE = ROOT / "scripts/probes/probe_second_descent_stuck_residual.py"


class SecondDescentStuckResidualValidationTest(unittest.TestCase):
    def test_probe_reports_the_verified_refutation(self):
        completed = subprocess.run(
            [sys.executable, str(PROBE)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn('"status": "PASS"', completed.stdout)
        self.assertIn("SecondDescentStuckResidual", completed.stdout)

    def test_corrupted_identity_fails_under_optimization(self):
        source = PROBE.read_text()
        original = "squared_equation[1] -= scale**2"
        self.assertIn(original, source)
        corrupted = source.replace(original, "squared_equation[1] -= scale**2 - 1", 1)

        with tempfile.TemporaryDirectory() as temp_dir:
            mutated_probe = Path(temp_dir) / PROBE.name
            mutated_probe.write_text(corrupted)
            for optimization in ("-O", "-OO"):
                with self.subTest(optimization=optimization):
                    completed = subprocess.run(
                        [sys.executable, optimization, str(mutated_probe)],
                        cwd=ROOT,
                        capture_output=True,
                        text=True,
                        check=False,
                    )

                    self.assertNotEqual(completed.returncode, 0)
                    self.assertIn("integer witness factorization mismatch", completed.stderr)
                    self.assertNotIn('"status": "PASS"', completed.stdout)


if __name__ == "__main__":
    unittest.main()
