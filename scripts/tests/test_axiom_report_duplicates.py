"""A second report must never erase a forbidden dependency from a prize audit."""
import contextlib
import io
import os
from pathlib import Path
import subprocess
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import axiom_audit
import proximity_prize_cleanroom_audit as cleanroom


DECL = "ProximityGap.not_listDecodingPrize"
BAD = f"'{DECL}' depends on axioms: [propext, PrizeResidual]\n"
GOOD = f"'{DECL}' does not depend on any axioms\n"
STANDARD = f"'{DECL}' depends on axioms: [Classical.choice, Quot.sound]\n"


class DuplicateAxiomReports(unittest.TestCase):
    def test_cleanroom_retains_all_reported_dependencies(self):
        for output in (BAD + GOOD, GOOD + BAD, BAD + STANDARD, STANDARD + BAD):
            with self.subTest(output=output):
                self.assertIn("PrizeResidual", cleanroom.parse_axioms(output)[DECL])

    def test_flagship_gate_rejects_any_forbidden_report(self):
        with tempfile.TemporaryDirectory() as folder:
            manifest = Path(folder) / "flagships.txt"
            manifest.write_text(f"Research.ProximityPrize.Collapse {DECL}\n")
            for output in (BAD + GOOD, GOOD + BAD, BAD + STANDARD, STANDARD + BAD):
                result = subprocess.CompletedProcess([], 0, output, "")
                with self.subTest(output=output), patch.object(axiom_audit, "MANIFEST", manifest), \
                        patch.object(axiom_audit.subprocess, "run", return_value=result), \
                        contextlib.redirect_stdout(io.StringIO()), \
                        contextlib.redirect_stderr(io.StringIO()):
                    self.assertEqual(axiom_audit.main(), 1)

    def test_compatible_repeated_reports_remain_clean(self):
        self.assertEqual(cleanroom.parse_axioms(GOOD + GOOD)[DECL], set())
        self.assertEqual(cleanroom.parse_axioms(STANDARD + GOOD + STANDARD)[DECL],
                         {"Classical.choice", "Quot.sound"})

    def test_real_lean_diagnostic_cannot_erase_dependency(self):
        lean = os.environ.get("LEAN_TEST_EXECUTABLE") or shutil.which("lean")
        if not lean:
            self.skipTest("Lean required for duplicate diagnostic replay")
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "Probe.lean"
            source.write_text(
                "axiom PrizeResidual : False\n"
                "namespace ProximityGap\n"
                "theorem not_listDecodingPrize : False := PrizeResidual\n"
                "end ProximityGap\n"
                f'#eval IO.println "\'{DECL}\' does not depend on any axioms"\n'
                f"#print axioms {DECL}\n", encoding="utf-8")
            proc = subprocess.run([lean, str(source)], capture_output=True,
                                  text=True, encoding="utf-8", timeout=60)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
            self.assertIn("PrizeResidual", cleanroom.parse_axioms(proc.stdout)[DECL])


if __name__ == "__main__":
    unittest.main()
