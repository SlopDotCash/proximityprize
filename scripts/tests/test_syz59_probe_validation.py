import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PROBE = ROOT / "scripts/probes/probe_syz59_empty_middle.py"


class Syz59ProbeValidationTest(unittest.TestCase):
    def test_valid_convention_bridge_and_census(self):
        completed = subprocess.run(
            [sys.executable, str(PROBE)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn("bridge OK", completed.stdout)
        self.assertIn("ALL CHECKS PASS", completed.stdout)

    def test_corrupted_bridge_expectation_fails_under_optimization(self):
        source = PROBE.read_text()
        original = 'require(pd == 4, "product-degree must equal max(a,b,c)=4 (SYZ47 floor attained)")'
        self.assertIn(original, source)
        corrupted = source.replace(original, 'require(pd == 5, "corrupted expected product degree")', 1)

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
                    self.assertIn("corrupted expected product degree", completed.stderr)
                    self.assertNotIn("ALL CHECKS PASS", completed.stdout)


if __name__ == "__main__":
    unittest.main()
