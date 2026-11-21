import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PROBE = ROOT / "scripts/probes/probe_n16_below_ceiling_max.py"


class N16BelowCeilingMaxValidationTest(unittest.TestCase):
    def test_small_exact_census_still_runs_under_optimization(self):
        completed = subprocess.run(
            [
                sys.executable,
                "-O",
                "-c",
                "import runpy,sys; m=runpy.run_path(sys.argv[1],run_name='probe'); "
                "x,c,maximum,winners,d=m['census'](8,17); "
                "print(len(c),maximum,winners,d)",
                str(PROBE),
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn("16 9", completed.stdout)

    def test_corrupted_count_fails_under_optimization(self):
        source = PROBE.read_text()
        assignment = "maximum = max(counts.values())"
        self.assertIn(assignment, source)
        corrupted = source.replace(assignment, "maximum = max(counts.values()) + 1", 1)
        corrupted = corrupted.replace(
            "for p in (17, 41, 257):", "for p in (17,):", 1
        )
        truncated_scan = "    # 2. Explicit n=16 spot checks (including the prize-scale prime)."
        self.assertIn(truncated_scan, corrupted)
        corrupted = corrupted.replace(truncated_scan, "    return\n\n" + truncated_scan, 1)

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
                    self.assertIn("AssertionError", completed.stderr)
                    self.assertNotIn("n=8 reproduction:", completed.stdout)


if __name__ == "__main__":
    unittest.main()
