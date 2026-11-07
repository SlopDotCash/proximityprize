"""Lean's ASCII connectives must classify exactly like their Unicode spellings."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]

# (ASCII result, Unicode result, proof, expected status) for `FooResidual := True`.
SHAPES = [
    ("FooResidual -> True", "FooResidual → True", "fun _ => trivial", "open"),
    ("FooResidual \\/ True", "FooResidual ∨ True", "Or.inr trivial", "open"),
    ("FooResidual <-> True", "FooResidual ↔ True", "Iff.rfl", "open"),
    ("FooResidual /\\ (True -> True)", "FooResidual ∧ (True → True)", "⟨trivial, id⟩", "discharged"),
]

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

theorem subJohnsonListResidual_imp_true (dom : Fin n ↪ F) (k m L A : ℕ) :
    SubJohnsonListResidual dom k m L A -> True := fun _ => trivial

end ProximityGap.Ownership
"""


class AsciiConnectiveTests(unittest.TestCase):
    def setUp(self):
        spec = importlib.util.spec_from_file_location(
            "residual_census", ROOT / "scripts" / "residual_census.py")
        self.census = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.census)
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def statuses(self, relative, text):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        decls, residuals, _ = self.census.collect(self.root)
        self.census.find_providers(decls, residuals)
        return {r["name"]: r["status"] for r in residuals}

    def foo_status(self, result, proof, binders=""):
        body = (f"namespace T\n\ndef FooResidual : Prop := True\n\n"
                f"theorem fooResidual_x{binders} : {result} := {proof}\n\nend T\n")
        return self.statuses("ArkLib/Data/A.lean", body)["FooResidual"]

    def test_ascii_and_unicode_spellings_agree(self):
        for ascii_form, unicode_form, proof, want in SHAPES:
            with self.subTest(result=ascii_form):
                self.assertEqual(self.foo_status(ascii_form, proof), want)
                self.assertEqual(self.foo_status(unicode_form, proof), want)

    def test_ascii_proposition_binder_is_an_extra_assumption(self):
        got = self.foo_status("FooResidual", "c.2.elim", binders=" (c : True /\\ False)")
        self.assertEqual(got, "open")

    def test_prize_list_bound_is_not_discharged_by_an_ascii_implication(self):
        got = self.statuses(
            "ArkLib/Data/CodingTheory/ProximityGap/SubJohnsonListSupply.lean", SUPPLY)
        self.assertEqual(got["SubJohnsonListResidual"], "open")

    def test_unicode_connectives(self):
        self.assertEqual(self.census.unicode_connectives("A <-> B -> C /\\ D \\/ E"),
                         "A ↔ B → C ∧ D ∨ E")
        self.assertEqual(self.census.unicode_connectives("f (x := y) → z"), "f (x := y) → z")
        self.assertEqual(self.census.unicode_connectives('R "a->b \\" /\\\\" «c\\/d» -> S'),
                         'R "a->b \\" /\\\\" «c\\/d» → S')


if __name__ == "__main__":
    unittest.main()
