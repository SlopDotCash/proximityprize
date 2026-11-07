"""sorry_census must count admitting `exact?` / `apply?` configurations as holes.

On Lean v4.30.0-rc2, `Lean.Elab.LibrarySearch.exact?` calls `admitGoal` whenever
the search returns suggestions, including when `LibrarySearchConfig.all` made it
keep a complete proof. `lake env lean` still exits 0 (only a `sorry` warning).

Checked in separate files, each ending in `#print axioms t`:

* `exact? +all`, `apply? +all`, `exact?+all`, `(all := true)`,
  `(config := { all := true })`, `+grind +all`, `(all := false) +all`,
  `(config := { grind := true }) +all`, a comment or newline before `+all`,
  and `{ cfg with all := true }` — exit 0, `'t' depends on axioms: [sorryAx]`.
* bare `exact?` / `apply?`, `+all -all`, `(all := false)`,
  `(config := { grind := true })`, `+all (config := { grind := true })`,
  and `(config := { all := true }) -all` — exit 0, axioms `[propext]`.
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

theorem apply_plain : (1 : Nat) = 1 := by
  apply?

theorem exact_cancel : (1 : Nat) = 1 := by
  exact? +all -all

theorem exact_field_false : (1 : Nat) = 1 := by
  exact? (all := false)

theorem exact_grind : (1 : Nat) = 1 := by
  exact? +grind

theorem exact_struct_grind : (1 : Nat) = 1 := by
  exact? (config := { grind := true })

theorem exact_struct_false : (1 : Nat) = 1 := by
  exact? (config := { all := false })

theorem exact_reset : (1 : Nat) = 1 := by
  exact? +all (config := { grind := true })

theorem exact_override : (1 : Nat) = 1 := by
  exact? (config := { all := true }) -all

theorem exact_both_fields : (1 : Nat) = 1 := by
  exact? (all := true) (all := false)

theorem exact_star : (1 : Nat) = 1 := by
  exact? -star

theorem spaced_plus : (1 : Nat) = 1 := by
  exact? + all

def apply? : Nat := 0
def exact? : Nat := 1
example : Nat := apply?
example : Nat := exact?

def «exact? +all» : Nat := 2
def «apply? (all := true)» : Nat := 3

theorem named_config : (1 : Nat) = 1 := by
  exact? (config := cfg)

theorem with_other : (1 : Nat) = 1 := by
  exact? (config := { cfg with grind := true })

theorem term_percent : Nat := exact?% 0
theorem qualified : Nat := Foo.exact? +all

-- exact? +all
/- apply? (all := true)
-/
/-- exact? (config := { all := true }) -/

def msg := "exact? +all"
def raw := r#"apply? (all := true)"#

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


if __name__ == "__main__":
    unittest.main()
