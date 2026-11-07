"""A tautology mentioning a prize predicate is not a completion certificate."""
import contextlib
import io
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import proximity_prize_cleanroom_audit as audit


ENTRY = audit.Entry("active", "Init", "candidate", "mcaPrize", (), 1)


def check(result):
    return audit.check_signature(ENTRY, f"candidate : {result}\n"
                                "'candidate' does not depend on any axioms\n")


class LogicalResults(unittest.TestCase):
    def test_disjunction_or_relation_does_not_establish_prize(self):
        for result in ("True ∨ mcaPrize 0", "mcaPrize 0 ∨ True",
                       "mcaPrize 0 ↔ mcaPrize 0", "mcaPrize 0 = mcaPrize 0",
                       "True ∧ (True ∨ mcaPrize 0)",
                       "True ∧ (mcaPrize 0 ↔ mcaPrize 0)",
                       "∀ n, mcaPrize n ∨ True", "(mcaPrize 0 ∧ True) ∨ True"):
            with self.subTest(result=result):
                self.assertTrue(check(result))

    def test_relations_in_other_conjuncts_or_arguments_are_allowed(self):
        for result in ("mcaPrize 0 ∧ (True ↔ True)",
                       "0 = 0 ∧ mcaPrize 0", "mcaPrize 0 ∧ 0 = 0",
                       "(True ∨ False) ∧ mcaPrize 0", "¬ mcaPrize 0",
                       "mcaPrize (if 0 = 0 then 0 else 1)",
                       "(mcaPrize 0 ∨ True) ∧ mcaPrize 1"):
            with self.subTest(result=result):
                self.assertEqual(check(result), [])

    def test_real_lean_tautologies_fail_completion_cli(self):
        lean = os.environ.get("LEAN_TEST_EXECUTABLE") or shutil.which("lean")
        if not lean:
            self.skipTest("Lean required for the completion-certificate replay")
        for result, proof in (("True ∨ mcaPrize 0", "Or.inl trivial"),
                              ("mcaPrize 0 ↔ mcaPrize 0", "Iff.rfl"),
                              ("mcaPrize 0 = mcaPrize 0", "rfl")):
            with self.subTest(result=result), tempfile.TemporaryDirectory() as folder:
                source = Path(folder) / "Probe.lean"
                source.write_text("def mcaPrize (_ : Nat) : Prop := False\n"
                                  f"theorem candidate : {result} := {proof}\n"
                                  "#check candidate\n#print axioms candidate\n", encoding="utf-8")
                proc = subprocess.run([lean, str(source)], capture_output=True,
                                      text=True, encoding="utf-8", timeout=60)
                self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
                manifest = Path(folder) / "targets.txt"
                manifest.write_text("active Init candidate mcaPrize\n", encoding="utf-8")
                with patch.object(sys, "argv", ["audit", "--manifest", str(manifest)]), \
                        patch.object(audit, "run_lean", return_value=(0, proc.stdout)), \
                        contextlib.redirect_stdout(io.StringIO()), \
                        contextlib.redirect_stderr(io.StringIO()):
                    self.assertEqual(audit.main(), 1)
