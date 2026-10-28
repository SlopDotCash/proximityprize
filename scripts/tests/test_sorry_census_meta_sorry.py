"""sorry_census must count metaprograms that build `sorryAx` as live holes."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import sorry_census

# Compiles on Lean v4.30.0-rc2 with only a "declaration uses `sorry`" warning;
# `#print axioms toy` reports [sorryAx].
HOLES = """\
import Lean
open Lean Elab Tactic Meta in
elab "close_it" : tactic => do
  let g ← getMainGoal
  g.assign (← mkSorry (← g.getType) (synthetic := false))
  replaceMainGoal []
theorem toy : (1 : Nat) = 2 := by close_it
def labeled (e : Expr) : MetaM Expr := mkLabeledSorry e false true
def raw : False := sorryAx False false
"""

# Prose about the same names is not a hole.
PROSE = """\
/-- Axioms: `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `mkSorry`). -/
theorem t : 2 = 2 := rfl
-- admitGoal and elabSorry are not used here
"""


class MetaSorry(unittest.TestCase):
    def census(self, text: str) -> list[dict]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Research").mkdir()
            (root / "ArkLib").mkdir()
            (root / "Research" / "Probe.lean").write_text(text, encoding="utf-8")
            return [r for r in sorry_census.census(root) if r["kind"] == "hole"]

    def test_sorry_api_is_a_hole(self) -> None:
        holes = self.census(HOLES)
        self.assertEqual([(r["line"], r["token"]) for r in holes],
                         [(5, "mkSorry"), (8, "mkLabeledSorry"), (9, "sorryAx")])

    def test_prose_is_not_a_hole(self) -> None:
        self.assertEqual(self.census(PROSE), [])


if __name__ == "__main__":
    unittest.main()
