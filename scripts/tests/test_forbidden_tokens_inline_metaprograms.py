"""forbidden_tokens must reject inline proof metaprograms (`run_tac`, `by_elab`)."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "forbidden_tokens.py"

# Both compile on Lean v4.30.0-rc2 and `#print axioms` reports [sorryAx], yet the
# source has no `sorry` / `sorryAx` token, so sorry_census also reports 0 holes.
INLINE = {
    "run_tac": """\
import Lean
open Lean Elab Tactic Meta
theorem bad : 1 = 2 := by
  run_tac do
    let g ← getMainGoal
    g.assign (mkApp2 (mkConst (Name.mkSimple ("sor" ++ "ryAx")) [Level.zero])
      (← g.getType) (toExpr false))
""",
    "by_elab": """\
import Lean
open Lean Elab Term Meta
theorem bad2 : 1 = 2 := by_elab do
  return mkApp2 (mkConst (Name.mkSimple ("sor" ++ "ryAx")) [Level.zero])
    (← mkEq (toExpr 1) (toExpr 2)) (toExpr false)
""",
}

# Prose and longer identifiers are not uses.
CLEAN = """\
/-- Proved without `run_tac` or `by_elab`. -/
theorem t : 2 = 2 := rfl
-- by_elab and run_tac are rejected in live code
def my_run_tac_note : Nat := 1
"""


def run(text: str) -> subprocess.CompletedProcess:
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "Probe.lean"
        path.write_text(text, encoding="utf-8")
        return subprocess.run(
            [sys.executable, str(SCRIPT), str(path)],
            capture_output=True,
            text=True,
            check=False,
        )


class InlineMetaprograms(unittest.TestCase):
    def test_inline_metaprograms_are_rejected(self) -> None:
        for label, text in INLINE.items():
            with self.subTest(label=label):
                result = run(text)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("forbidden metaprogram declaration", result.stderr)

    def test_prose_and_longer_names_stay_clean(self) -> None:
        result = run(CLEAN)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
