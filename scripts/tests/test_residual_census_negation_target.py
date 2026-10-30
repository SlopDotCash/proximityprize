"""A refutation must refute the residual outright, not a compound that mentions it."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]

# Provable statements about the true residual `FooResidual := True`.  Each puts the
# residual under `¬` without refuting it; `¬ (R → False)`, `¬ R → False`,
# `¬ (R ↔ False)`, `¬ R = False`, `¬ IsEmpty R`, `¬ ∀ h : R, False` and `¬ ¬ R`
# even prove it.
NOT_REFUTATIONS = [
    ("¬ (FooResidual ∧ False)", "fun h => h.2"),
    ("¬ (FooResidual → False)", "fun h => h trivial"),
    ("¬ FooResidual → False", "fun h => h trivial"),
    ("¬ FooResidual ∨ True", "Or.inr trivial"),
    ("¬ (FooResidual ↔ False)", "fun h => h.1 trivial"),
    ("¬ FooResidual = False", "fun h => cast h trivial"),
    ("¬ FooResidual ≠ True", "fun h => h rfl"),
    ("¬ IsEmpty FooResidual", "fun h => h.1 trivial"),
    ("¬ ∀ _h : FooResidual, False", "fun h => h trivial"),
    ("¬ ∃ _h : FooResidual, False", "fun ⟨_, h⟩ => h"),
    ("¬ ∃ _h : 1 = 0, FooResidual", "fun ⟨h, _⟩ => Nat.one_ne_zero h"),
    ("¬ ∃ _h : False, FooResidual", "fun ⟨h, _⟩ => h"),
    ("¬ ∃ _h : IsEmpty (Fin 3), FooResidual", "fun ⟨h, _⟩ => h.1 0"),
    ("¬ ∃ k ∈ ([] : List Nat), FooResidual", "fun ⟨_, hk, _⟩ => by simp at hk"),
    ("¬ ¬ FooResidual", "fun h => h trivial"),
    ("¬ FooResidual ∧ True → False", "fun h => h.1 trivial"),
    ("¬ (FooResidual ∨ True → False)", "fun h => h (Or.inr trivial)"),
]

# Genuine refutations of the false residual `FooResidual := False` still count.
REFUTATIONS = [
    ("¬ FooResidual", "id"),
    ("¬ (FooResidual)", "id"),
    ("¬ T.FooResidual", "id"),
    ("¬ FooResidual ∧ True", "⟨id, trivial⟩"),
    ("¬ (FooResidual) ∧ True", "⟨id, trivial⟩"),
    ("¬ FooResidual ∧ ∀ n : Nat, n = n → True", "⟨id, fun _ _ => trivial⟩"),
    ("¬ ∀ _k : Nat, FooResidual", "fun h => h 0"),
    ("¬ (∀ _k : Nat, FooResidual)", "fun h => h 0"),
    ("¬ ∀ k : Nat, 0 < k → FooResidual", "fun h => h 1 Nat.one_pos"),
    ("¬ ∀ _h : True, FooResidual", "fun h => h trivial"),
    ("¬ ∃ _k : Nat, FooResidual", "fun ⟨_, h⟩ => h"),
    ("¬ ∃ H : Nat, FooResidual", "fun ⟨_, h⟩ => h"),
    ("¬ (FooResidual ∨ False)", "fun h => h.elim id id"),
    ("¬ (False ∨ FooResidual)", "fun h => h.elim id id"),
    ("¬ (True → FooResidual)", "fun h => h trivial"),
    ("∀ _k : Nat, ¬ FooResidual", "fun _ => id"),
]

# The prize-path residual of `ArkLib/Data/CodingTheory/ProximityGap/SubJohnsonListSupply.lean`
# (the open list-bound core of #389), with a true theorem that refutes nothing.
SUPPLY = """namespace ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

def SubJohnsonListBound (dom : Fin n ↪ F) (k m L A : ℕ) : Prop :=
  ∀ w : Fin n → F,
    (bigAgreeCodewords dom k m w).card ≤ L
      ∧ ∀ c ∈ bigAgreeCodewords dom k m w, (listAgreeSet c w).card ≤ A

def SubJohnsonListResidual (dom : Fin n ↪ F) (k m L A : ℕ) : Prop :=
  SubJohnsonListBound dom k m L A

theorem subJohnsonListResidual_and_false (dom : Fin n ↪ F) (k m L A : ℕ) :
    ¬ (SubJohnsonListResidual dom k m L A ∧ False) := fun h => h.2

end ProximityGap.Ownership
"""


class NegationTargetTests(unittest.TestCase):
    def setUp(self):
        spec = importlib.util.spec_from_file_location(
            "residual_census", ROOT / "scripts" / "residual_census.py")
        self.census = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.census)
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def census_rows(self, relative, text):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        decls, residuals, _ = self.census.collect(self.root)
        self.census.find_providers(decls, residuals)
        return {r["name"]: r for r in residuals}

    def statuses(self, body):
        rows = self.census_rows("ArkLib/Data/A.lean", f"namespace T\n\n{body}\nend T\n")
        return {name: row["status"] for name, row in rows.items()}

    def theorem(self, value, statement, proof):
        return (f"def FooResidual : Prop := {value}\n\n"
                f"theorem t : {statement} := {proof}\n")

    def test_compound_negations_do_not_refute(self):
        for statement, proof in NOT_REFUTATIONS:
            with self.subTest(statement=statement):
                got = self.statuses(self.theorem("True", statement, proof))
                self.assertEqual(got["FooResidual"], "open")

    def test_negations_of_the_residual_still_refute(self):
        for statement, proof in REFUTATIONS:
            with self.subTest(statement=statement):
                got = self.statuses(self.theorem("False", statement, proof))
                self.assertEqual(got["FooResidual"], "refuted")

    def test_disjunction_and_conjunction_refute_both_residuals(self):
        for statement, proof in [
            ("¬ (BarResidual ∨ FooResidual)", "fun h => h.elim id id"),
            ("¬ BarResidual ∧ ¬ FooResidual", "⟨id, id⟩"),
        ]:
            with self.subTest(statement=statement):
                got = self.statuses(
                    "def FooResidual : Prop := False\n"
                    "def BarResidual : Prop := False\n\n"
                    f"theorem t : {statement} := {proof}\n")
                self.assertEqual(got, {"FooResidual": "refuted", "BarResidual": "refuted"})

    def test_relation_and_binder_shapes(self):
        for negated, want in [
            ("(R == Q)", []),
            ("R ≤ False", []),
            ("R ∈ S", []),
            ("∃! k, R k", []),
            ("∃ ε > (0 : ℝ), R ε", []),
            ("∃ h : Nat.Prime (2 + 2), R", []),
            ("∃ _ : IsEmpty (Fin 3), R", []),
            ("∃ (k : ℕ) (hk : 0 < k), R k", []),
            ("∃ H : Polynomial (ZMod 7), R H", ["R"]),
            ("R fun x => x = x", ["R"]),
            ("R (f := fun x => x = x)", ["R"]),
        ]:
            with self.subTest(negated=negated):
                self.assertEqual(self.census.negation_targets(negated, ["R"]), want)

    def test_prize_list_bound_stays_open(self):
        row = self.census_rows(
            "ArkLib/Data/CodingTheory/ProximityGap/SubJohnsonListSupply.lean", SUPPLY)[
            "SubJohnsonListResidual"]
        self.assertEqual(row["status"], "open")
        self.assertEqual(row["refutations"], [])


if __name__ == "__main__":
    unittest.main()
