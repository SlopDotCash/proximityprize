"""sorry_census must count admitting `exact?` / `apply?` configurations as holes.

On Lean v4.30.0-rc2, `Lean.Elab.LibrarySearch.exact?` calls `admitGoal` whenever
the search returns suggestions, including when `LibrarySearchConfig.all` made it
keep a complete proof. `lake env lean` still exits 0 (only a `sorry` warning).

Checked in separate files, each ending in `#print axioms t`:

* `exact? +all`, `apply? +all`, `exact?+all`, `(all := true)`,
  `(config := { all := true })`, `+grind +all`, `(all := false) +all`,
  `(config := { grind := true }) +all`, a comment or newline before `+all`,
  and `{ cfg with all := true }` — exit 0, `'t' depends on axioms: [sorryAx]`.
* Bare `exact?` on a goal it can close, plus `exact? +all -all`, `(all := .false)`,
  `(config := { grind := true })`, `+all (config := { grind := true })`,
  and `(config := { all := true }) -all` — exit 0, axioms `[propext]`.
* Bare `apply?` and `apply? -all` against the partial `NeedsFalse.intro`
  suggestion below elaborate with `sorryAx`, even though collection is off.
* `exact? + all` (space before the name) — exit 1, not a silent proof.
"""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import sorry_census


HOLES = """\
theorem exact_plus : (1 : Nat) = 1 := by
  exact? +all

theorem apply_plus : (1 : Nat) = 1 := by
  apply? +all

theorem exact_tight : (1 : Nat) = 1 := by
  exact?+all

theorem exact_field : (1 : Nat) = 1 := by
  exact? (all := true)

theorem apply_field : (1 : Nat) = 1 := by
  apply? (all := true)

theorem exact_config : (1 : Nat) = 1 := by
  exact? (config := { all := true })

theorem exact_config_order : (1 : Nat) = 1 := by
  exact? (config := { grind := true, all := true })

theorem exact_parens : (1 : Nat) = 1 := by
  exact? (config := ({ all := true }))

theorem exact_grind_all : (1 : Nat) = 1 := by
  exact? +grind +all

theorem exact_reenable : (1 : Nat) = 1 := by
  exact? (all := false) +all

theorem exact_after_config : (1 : Nat) = 1 := by
  exact? (config := { grind := true }) +all

theorem exact_comment : (1 : Nat) = 1 := by
  exact? /- keep -/ +all

theorem exact_line : (1 : Nat) = 1 := by
  exact?
    +all

theorem exact_using (h : (1 : Nat) = 1) : (1 : Nat) = 1 := by
  exact? +all using h

theorem exact_goals : (1 : Nat) = 1 := by
  all_goals exact? +all

theorem exact_bullet : (1 : Nat) = 1 ∧ True := by
  constructor
  · exact? +all
  · trivial

theorem exact_with : (1 : Nat) = 1 := by
  exact? (config := { cfg with all := true })

theorem exact_multiline : (1 : Nat) = 1 := by
  exact? (
    all := true)

theorem exact_cmt_true : (1 : Nat) = 1 := by
  exact? (config := { all := /- x -/ true })

theorem splice : String := s!"{exact? +all}"
"""

# Proofs Lean accepts without `sorryAx`, plus text that only looks like the
# admitting form. None of these is a hole.
CLEAN = """\
theorem exact_plain : (1 : Nat) = 1 := by
  exact?

theorem exact_cancel : (1 : Nat) = 1 := by
  exact? +all -all

theorem exact_field_false : (1 : Nat) = 1 := by
  exact? (all := .false)

theorem exact_grind : (1 : Nat) = 1 := by
  exact? +grind

theorem exact_struct_grind : (1 : Nat) = 1 := by
  exact? (config := { grind := true })

theorem exact_struct_false : (1 : Nat) = 1 := by
  exact? (config := { all := .false })

theorem exact_reset : (1 : Nat) = 1 := by
  exact? +all (config := { grind := true })

theorem exact_override : (1 : Nat) = 1 := by
  exact? (config := { all := true }) -all

theorem exact_both_fields : (1 : Nat) = 1 := by
  exact? (all := true) (all := .false)

theorem exact_star : (1 : Nat) = 1 := by
  exact? -star

theorem spaced_plus : (1 : Nat) = 1 := by
  exact? + all

def apply? : Nat := 0
def exact? : Nat := 1
example : Nat := apply?
example : Nat := exact?
example : Nat :=
  apply?
example : Nat := by exact apply?
example : Nat := by
  exact
    apply?
example : Nat := by
  exact (let x := (); apply?)
example : Nat := by
  exact (fun _ : Unit => apply?) ()
def apply?? : Nat := 2
def qualifiedApply : Nat := Foo.apply?
def quotedApply : Nat := «apply?»
def nameApply := `apply?

def «exact? +all» : Nat := 2
def «apply? (all := true)» : Nat := 3

theorem named_config : (1 : Nat) = 1 := by
  exact? (config := cfg) -all

theorem with_other : (1 : Nat) = 1 := by
  exact? (config := { cfg with grind := true }) -all

theorem term_percent : Nat := exact?% 0
theorem qualified : Nat := Foo.exact? +all

-- exact? +all
/- apply? (all := true)
-/
/-- exact? (config := { all := true }) -/

def msg := "exact? +all"
def msgApply := "by apply? -all"
def raw := r#"apply? (all := true)"#
def rawApply := r#"{by apply?}"#

theorem bare_then_other : (1 : Nat) = 1 := by
  exact?
theorem not_this : True := by
  skip
"""


class LibrarySearchAdmit(unittest.TestCase):
    def census(self, text: str) -> list[dict]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Research").mkdir()
            (root / "ArkLib").mkdir()
            (root / "Research" / "Probe.lean").write_text(text, encoding="utf-8")
            return [r for r in sorry_census.census(root) if r["kind"] == "hole"]

    def test_admitting_library_search_is_a_hole(self) -> None:
        holes = self.census(HOLES)
        self.assertEqual(
            [(r["decl"], r["token"]) for r in holes],
            [
                ("theorem exact_plus", "exact?"),
                ("theorem apply_plus", "apply?"),
                ("theorem exact_tight", "exact?"),
                ("theorem exact_field", "exact?"),
                ("theorem apply_field", "apply?"),
                ("theorem exact_config", "exact?"),
                ("theorem exact_config_order", "exact?"),
                ("theorem exact_parens", "exact?"),
                ("theorem exact_grind_all", "exact?"),
                ("theorem exact_reenable", "exact?"),
                ("theorem exact_after_config", "exact?"),
                ("theorem exact_comment", "exact?"),
                ("theorem exact_line", "exact?"),
                ("theorem exact_using", "exact?"),
                ("theorem exact_goals", "exact?"),
                ("theorem exact_bullet", "exact?"),
                ("theorem exact_with", "exact?"),
                ("theorem exact_multiline", "exact?"),
                ("theorem exact_cmt_true", "exact?"),
                ("theorem splice", "exact?"),
            ],
        )

    def test_closing_search_and_lookalikes_are_not_holes(self) -> None:
        self.assertEqual(self.census(CLEAN), [])

    def test_apply_can_admit_incomplete_suggestions_with_collection_off(self) -> None:
        # Elaborates independently with `sorryAx` on pinned Lean 4.30.0-rc2.
        for options in ("", " -all"):
            with self.subTest(options=options):
                source = f"""\
import Lean.Elab.Tactic.LibrarySearch

inductive NeedsFalse : Prop where
  | intro : False → NeedsFalse

theorem incomplete : NeedsFalse := by
  apply?{options}

#print axioms incomplete
"""
                self.assertEqual(
                    [(row["decl"], row["token"]) for row in self.census(source)],
                    [("theorem incomplete", "apply?")],
                )

    def test_apply_in_tactic_quotation_is_a_hole(self) -> None:
        # On Lean 4.35, this macro elaborates incomplete with sorryAx.
        for quote in ("`(tactic| apply?)", "`(tactic|\n    apply?)"):
            with self.subTest(quote=quote):
                source = f"""\
import Lean

macro "searchProof" : tactic => {quote}

inductive NeedsFalse : Prop where
  | intro : False → NeedsFalse

theorem incomplete : NeedsFalse := by
  searchProof
"""
                self.assertEqual([row["token"] for row in self.census(source)], ["apply?"])

    def test_apply_in_tactic_sequences_is_rejected(self) -> None:
        for body in (
            "by apply?",
            "by /- comment -/ apply? -all",
            "by { apply? -all }",
            "by {\n  apply? -all\n}",
            "by all_goals apply? -all",
            "by\n  all_goals\n    apply?",
            "by set_option maxHeartbeats 200000 in apply? -all",
            "by set_option maxHeartbeats 200000 in all_goals apply? -all",
            "by\n  set_option maxHeartbeats 200000 in\n    apply?",
            "by let _ := (); apply? -all",
            "by match true with | true => apply?",
            "by\n  match true with\n  | true => apply?",
            "by\n  match true with\n    | true => apply?",
            "by\n  match true with\n  | true =>\n    apply?",
            "by\n  constructor <;> apply?",
            "by\n  constructor; apply?",
            "by\n  first | apply? -all | trivial",
            "by\n  first\n  | apply? -all\n  | trivial",
            "by\n  case next => apply?",
            "by\n  case next =>\n    apply?",
            "by\n  · apply?",
        ):
            with self.subTest(body=body):
                source = f"theorem test : True := {body}\n"
                self.assertEqual([row["token"] for row in self.census(source)], ["apply?"])

    def test_search_config_does_not_assume_opaque_or_shadowable_values(self) -> None:
        for config in (
            "(all := Bool.true)",
            "(«all» := _root_.Bool.true)",
            "+«all»",
            "(«config» := named)",
            "(config := named)",
            "(config := { named with grind := true })",
            "(config := { «all» := Bool.true })",
            "(config := {\n    grind := false\n    all := Bool.true\n  })",
            "(all := Bool.not false)",
            "(all := false)",
            "(all := Bool.false)",
            "(config := { all := false })",
            '(all := _root_.Bool.false "argument")',
        ):
            for tactic in ("exact?", "apply?"):
                with self.subTest(tactic=tactic, config=config):
                    source = f"theorem test : True := by\n  {tactic} {config}\n"
                    self.assertEqual([row["token"] for row in self.census(source)], [tactic])

    def test_safe_overrides_clear_potentially_admitting_options(self) -> None:
        for config in (
            "(config := named) -all",
            "(config := named) (all := .false)",
            "(all := Bool.not false) -«all»",
            "+all (all := ((/- reason -/ _root_.Bool.false)))",
            "+all (config := { grind := true, all := .false })",
        ):
            with self.subTest(config=config):
                self.assertEqual(self.census(f"theorem test : True := by\n  exact? {config}\n"), [])


if __name__ == "__main__":
    unittest.main()
