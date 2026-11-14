import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PROBE = ROOT / "scripts/probes/probe_sac_signed_puncture_support.py"


class Sac01SignedPunctureCertificateTest(unittest.TestCase):
    def test_probe_completes_with_kernel_checked_sac01_values(self):
        completed = subprocess.run(
            [sys.executable, str(PROBE)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn("C=-282820222144", completed.stdout)

    def test_decomposition_mismatch_fails_in_optimized_python(self):
        source = PROBE.read_text()
        original = "corr[s] = total[s] - base[s]"
        self.assertIn(original, source)
        corrupted = source.replace(original, "corr[s] = total[s] - base[s] + 1", 1)

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
                    self.assertIn("support decomposition failed", completed.stderr)
                    self.assertNotIn("check=False", completed.stdout)


if __name__ == "__main__":
    unittest.main()
