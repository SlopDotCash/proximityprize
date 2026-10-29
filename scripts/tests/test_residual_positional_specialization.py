"""A numeral-fixed instance is not a general residual-family discharge."""
from pathlib import Path
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import residual_census as census


class PositionalSpecialization(unittest.TestCase):
    def test_lean_proves_only_the_specialized_instance(self):
        lean = os.environ.get("LEAN_TEST_EXECUTABLE") or shutil.which("lean")
        if not lean:
            self.skipTest("Lean required for the specialized residual replay")
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "Probe.lean"
            source.write_text("def FooResidual (k : Nat) : Prop := k = 0\n"
                              "theorem provider : FooResidual 0 := rfl\n"
                              "theorem not_general : ¬ (∀ k, FooResidual k) := by\n"
                              "  intro h\n  exact Nat.noConfusion (h 1)\n"
                              "#print axioms provider\n#print axioms not_general\n",
                              encoding="utf-8")
            result = subprocess.run([lean, str(source)], capture_output=True,
                                    text=True, encoding="utf-8", timeout=60)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn("sorryAx", result.stdout)

    def test_fixed_instances_stay_open(self):
        for result in ("FooResidual 0", "FooResidual (0)", "FooResidual ((0))",
                       "FooResidual 0x0", "FooResidual (k := (0))"):
            with self.subTest(result=result), tempfile.TemporaryDirectory() as folder:
                root = Path(folder)
                source = root / "ArkLib/Probe.lean"
                source.parent.mkdir()
                source.write_text("def FooResidual (k : Nat) : Prop := k = 0\n"
                                  f"theorem provider : {result} := rfl\n", encoding="utf-8")
                declarations, residuals, _ = census.collect(root)
                census.find_providers(declarations, residuals)
                self.assertEqual(residuals[0]["status"], "open")
                self.assertTrue(residuals[0]["providers"][0]["specialised_arguments"])

    def test_general_result_and_unrelated_conjuncts_are_not_specialized(self):
        for result in ("FooResidual k", "FooResidual (k := k)",
                       "FooResidual k ∧ 0 = 0", "FooResidual k ∧ Bar 0",
                       "FooResidual (k := k) ∧ Bar (m := 0)"):
            with self.subTest(result=result):
                self.assertEqual(census.specialised_arguments(result, "FooResidual"), [])

    def test_positional_list_bound_and_implicit_numeral_forms(self):
        for result in ("SubJohnsonListResidual dom k m 0 A",
                       "SubJohnsonListResidual dom k m (0) A",
                       "SubJohnsonListResidual dom k m L (A := (0))"):
            with self.subTest(result=result):
                self.assertTrue(census.specialised_arguments(result, "SubJohnsonListResidual"))
