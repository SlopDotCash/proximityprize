"""Conditional prize-residual providers must not be counted as concrete proofs."""
from pathlib import Path
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import residual_census as census


def statuses(code):
    with tempfile.TemporaryDirectory() as folder:
        root = Path(folder)
        source = root / "ArkLib/Probe.lean"
        source.parent.mkdir()
        source.write_text(code, encoding="utf-8")
        declarations, residuals, _ = census.collect(root)
        census.find_providers(declarations, residuals)
        return residuals


class ProofPremises(unittest.TestCase):
    def test_false_and_anonymous_proof_parameters_are_conditional(self):
        for signature, proof in (("(proof : False) : FooResidual", "proof"),
                                 ("(_proof : False) : FooResidual", "_proof"),
                                 ("(_ : False) : FooResidual", "by assumption"),
                                 ("(_ : 0 = 1) : FooResidual", "by contradiction"),
                                 (": ∀ (proof : False), FooResidual", "fun p => p"),
                                 (": ∀ proof : False, FooResidual", "fun p => p"),
                                 (": ∀ (_ : FooResidual), FooResidual", "fun p => p")):
            with self.subTest(signature=signature):
                residual, = statuses("def FooResidual : Prop := False\n"
                                     f"theorem provider {signature} := {proof}\n")
                self.assertEqual(residual["status"], "open")

    def test_real_list_bound_stays_open_under_false_premise(self):
        source = (Path(__file__).resolve().parents[2] /
                  "ArkLib/Data/CodingTheory/ProximityGap/SubJohnsonListSupply.lean")
        code = source.read_text(encoding="utf-8") + """
namespace ProximityGap.Ownership
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} [NeZero n]
theorem conditional_provider (dom : Fin n ↪ F) (k m L A : ℕ) (proof : False) :
    SubJohnsonListResidual dom k m L A := False.elim proof
end ProximityGap.Ownership
"""
        residual, = [r for r in statuses(code) if r["name"] == "SubJohnsonListResidual"]
        self.assertEqual(residual["status"], "open")

    def test_forall_data_parameter_is_still_general(self):
        residual, = statuses("def FooResidual (n : Nat) : Prop := True\n"
                             "theorem provider : ∀ n : Nat, FooResidual n := fun _ => trivial\n")
        self.assertEqual(residual["status"], "discharged")

    def test_real_lean_conditional_false_certificate_compiles(self):
        lean = os.environ.get("LEAN_TEST_EXECUTABLE") or shutil.which("lean")
        if not lean:
            self.skipTest("Lean required for the conditional residual replay")
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "Probe.lean"
            source.write_text("def FooResidual : Prop := False\n"
                              "theorem provider : ∀ proof : False, FooResidual := fun p => p\n"
                              "#print axioms provider\n", encoding="utf-8")
            result = subprocess.run([lean, str(source)], capture_output=True,
                                    text=True, encoding="utf-8", timeout=60)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("does not depend on any axioms", result.stdout)
