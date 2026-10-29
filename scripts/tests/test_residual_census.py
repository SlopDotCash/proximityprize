"""Regression coverage for residual_census status classification."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

HEADER = "namespace T\n\n"
FOOTER = "\nend T\n"


class ResidualCensusTests(unittest.TestCase):
    def setUp(self):
        spec = importlib.util.spec_from_file_location(
            "residual_census", Path(__file__).resolve().parents[1] / "residual_census.py")
        self.census = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.census)
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def statuses(self, body):
        folder = self.root / "ArkLib" / "Data"
        folder.mkdir(parents=True, exist_ok=True)
        (folder / "A.lean").write_text(HEADER + body + FOOTER)
        decls, residuals, _ = self.census.collect(self.root)
        self.census.find_providers(decls, residuals)
        return {r["name"]: r["status"] for r in residuals}

    def test_provider_in_relocated_extension_preserves_discharge(self):
        canonical = self.root / "ArkLib" / "Data" / "A.lean"
        extension = self.root / "ProximityPrize" / "Extensions" / "Data" / "A.lean"
        canonical.parent.mkdir(parents=True)
        extension.parent.mkdir(parents=True)
        canonical.write_text(HEADER + "def FooResidual : Prop := True\n" + FOOTER)
        extension.write_text(HEADER +
            "theorem fooResidual_holds : FooResidual := trivial\n" + FOOTER)
        decls, residuals, _ = self.census.collect(self.root)
        self.census.find_providers(decls, residuals)
        self.assertEqual(len(residuals), 1)
        self.assertEqual(residuals[0]["status"], "discharged")
        self.assertEqual(residuals[0]["providers"][0]["file"],
                         "ProximityPrize/Extensions/Data/A.lean")

    def test_relocated_residual_stays_in_production_census(self):
        source = self.root / "ProximityPrize" / "Extensions" / "Data" / "A.lean"
        research = self.root / "Research" / "A.lean"
        source.parent.mkdir(parents=True)
        research.parent.mkdir()
        source.write_text(HEADER + "def FooResidual : Prop := True\n" + FOOTER)
        research.write_text(HEADER +
            "theorem fooResidual_holds : FooResidual := trivial\n" + FOOTER)
        decls, residuals, _ = self.census.collect(self.root)
        self.census.find_providers(decls, residuals)
        self.assertEqual(len(residuals), 1)
        self.assertEqual(residuals[0]["status"], "open")
        self.assertEqual(residuals[0]["file"], "ProximityPrize/Extensions/Data/A.lean")
        self.assertEqual(self.census.top_dir(residuals[0]["file"]), "Data")

    def test_general_provider_discharges(self):
        got = self.statuses(
            "def FooResidual {k : Nat} : Prop := True\n\n"
            "theorem fooResidual_holds {k : Nat} : FooResidual (k := k) := trivial\n")
        self.assertEqual(got["FooResidual"], "discharged")

    def test_equivalence_is_not_a_provider(self):
        got = self.statuses(
            "def FooResidual {k : Nat} : Prop := True\n"
            "def BarResidual {k : Nat} : Prop := True\n\n"
            "theorem fooResidual_iff_bar {k : Nat} :\n"
            "    FooResidual (k := k) ↔ BarResidual (k := k) := Iff.rfl\n")
        self.assertEqual(got["FooResidual"], "open")

    def test_top_level_connective_shape(self):
        conn = self.census.top_level_connective
        self.assertEqual(conn("FooResidual (k := k) → False"), "→")
        self.assertEqual(conn("∀ k, FooResidual (k := k) ∨ BarResidual"), "∨")
        self.assertEqual(conn("FooResidual = True"), "=")
        self.assertEqual(conn("FooResidual ∧ (A → B)"), "∧")
        self.assertIsNone(conn("FooResidual (f := fun x => x = x)"))
        self.assertIsNone(conn("FooResidual (k := k)"))

    def test_implication_from_residual_is_not_a_provider(self):
        got = self.statuses(
            "def FooResidual {k : Nat} : Prop := True\n\n"
            "theorem fooResidual_imp {k : Nat} : FooResidual (k := k) → True :=\n"
            "  fun _ => trivial\n")
        self.assertEqual(got["FooResidual"], "open")

    def test_disjunction_and_equation_are_not_providers(self):
        got = self.statuses(
            "def FooResidual {k : Nat} : Prop := True\n"
            "def BarResidual {k : Nat} : Prop := True\n\n"
            "theorem fooResidual_or {k : Nat} : FooResidual (k := k) ∨ True := Or.inr trivial\n"
            "theorem barResidual_eq {k : Nat} : BarResidual (k := k) = True := rfl\n")
        self.assertEqual(got["FooResidual"], "open")
        self.assertEqual(got["BarResidual"], "open")

    def test_left_conjunct_still_discharges(self):
        got = self.statuses(
            "def FooResidual {k : Nat} : Prop := True\n\n"
            "theorem fooResidual_and {k : Nat} : FooResidual (k := k) ∧ (True → True) :=\n"
            "  ⟨trivial, id⟩\n")
        self.assertEqual(got["FooResidual"], "discharged")

    def test_numeral_specialisation_is_not_a_provider(self):
        got = self.statuses(
            "def FooResidual {k : Nat} : Prop := 0 < k → False\n\n"
            "theorem fooResidual_zero : FooResidual (k := 0) := by\n"
            "  intro h; omega\n")
        self.assertEqual(got["FooResidual"], "open")

    def test_refutation_outranks_specialised_provider(self):
        got = self.statuses(
            "def FooResidual {k : Nat} : Prop := 0 < k → False\n\n"
            "theorem fooResidual_zero : FooResidual (k := 0) := by\n"
            "  intro h; omega\n\n"
            "theorem not_fooResidual : ¬ FooResidual (k := 1) := by\n"
            "  intro h; exact h (by omega)\n")
        self.assertEqual(got["FooResidual"], "refuted")

    def test_refutation_outranks_general_looking_provider(self):
        got = self.statuses(
            "def FooResidual {k : Nat} : Prop := True\n\n"
            "theorem fooResidual_holds {k : Nat} : FooResidual (k := k) := trivial\n\n"
            "theorem not_fooResidual : ¬ FooResidual (k := 1) := sorry\n")
        self.assertEqual(got["FooResidual"], "refuted")


if __name__ == "__main__":
    unittest.main()
