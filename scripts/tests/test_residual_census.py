"""Regression coverage for residual_census status classification."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

HEADER = "namespace T\n\n"
FOOTER = "\nend T\n"

# The prize-path residual of `ArkLib/Data/CodingTheory/ProximityGap/SubJohnsonListSupply.lean`
# (the open list-bound core of #389), with a true implication that proves nothing about it.
SUPPLY = """namespace ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

def SubJohnsonListBound (dom : Fin n ↪ F) (k m L A : ℕ) : Prop :=
  ∀ w : Fin n → F,
    (bigAgreeCodewords dom k m w).card ≤ L
      ∧ ∀ c ∈ bigAgreeCodewords dom k m w, (listAgreeSet c w).card ≤ A

def SubJohnsonListResidual (dom : Fin n ↪ F) (k m L A : ℕ) : Prop :=
  SubJohnsonListBound dom k m L A

theorem subJohnsonListResidual_and_false_imp (dom : Fin n ↪ F) (k m L A : ℕ) :
    SubJohnsonListResidual dom k m L A ∧ False → True := fun _ => trivial

end ProximityGap.Ownership
"""


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
        self.assertEqual(conn("FooResidual ∧ True → False"), "→")
        self.assertEqual(conn("FooResidual ∧ True ∨ False"), "∨")
        self.assertEqual(conn("FooResidual = True ∧ True"), "=")
        self.assertEqual(conn("FooResidual ∧ ∀ n : Nat, n = n → True"), "∧")
        self.assertEqual(conn("FooResidual ∧ ∃ n, n = n → True"), "∧")
        self.assertEqual(conn("FooResidual ∧ a = b"), "∧")
        self.assertIsNone(conn("FooResidual fun x => x → x"))
        self.assertEqual(conn("∃ n : Nat, ∀ k : Nat, FooResidual (k := k) → n = n"), "→")

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

    def test_conjunction_under_implication_or_disjunction_is_not_a_provider(self):
        got = self.statuses(
            "def FooResidual {k : Nat} : Prop := True\n"
            "def BarResidual {k : Nat} : Prop := True\n\n"
            "theorem fooResidual_and_imp {k : Nat} : FooResidual (k := k) ∧ False → True :=\n"
            "  fun _ => trivial\n"
            "theorem barResidual_and_or {k : Nat} : BarResidual (k := k) ∧ False ∨ True :=\n"
            "  Or.inr trivial\n")
        self.assertEqual(got["FooResidual"], "open")
        self.assertEqual(got["BarResidual"], "open")

    def test_existential_result_with_implication_is_not_a_provider(self):
        got = self.statuses(
            "def FooResidual {k : Nat} : Prop := True\n\n"
            "theorem fooResidual_holds :\n"
            "    ∃ n : Nat, ∀ k : Nat, FooResidual (k := k) → n = n :=\n"
            "  ⟨0, fun _ _ => rfl⟩\n")
        self.assertEqual(got["FooResidual"], "open")

    def test_left_conjunct_with_quantified_tail_still_discharges(self):
        got = self.statuses(
            "def FooResidual {k : Nat} : Prop := True\n\n"
            "theorem fooResidual_and_forall {k : Nat} :\n"
            "    FooResidual (k := k) ∧ ∀ n : Nat, n = n → True :=\n"
            "  ⟨trivial, fun _ _ => trivial⟩\n")
        self.assertEqual(got["FooResidual"], "discharged")

    def test_prize_list_bound_is_not_discharged_by_an_implication(self):
        folder = self.root / "ArkLib" / "Data" / "CodingTheory" / "ProximityGap"
        folder.mkdir(parents=True, exist_ok=True)
        (folder / "SubJohnsonListSupply.lean").write_text(SUPPLY)
        decls, residuals, _ = self.census.collect(self.root)
        self.census.find_providers(decls, residuals)
        got = {r["name"]: r["status"] for r in residuals}
        self.assertEqual(got["SubJohnsonListResidual"], "open")

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
