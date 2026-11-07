"""forbidden_tokens must reject an `axiom` whose name is spliced in by a quotation."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "forbidden_tokens.py"

# Both forms compile on Lean v4.30.0-rc2 with only `import Lean`, and
# `#print axioms toyGap_holds` lists `toyResidualWitness`; before this check the
# precheck reported both files clean.
MACRO_ARGUMENT = """\
import Lean
macro "residual_witness " n:ident : command => `(axiom $n : False)
residual_witness toyResidualWitness
def ToyGapResidual : Prop := 1 = 2
theorem toyGap_holds : ToyGapResidual := toyResidualWitness.elim
"""
MACRO_RULES = """\
import Lean
syntax "residual_witness" : command
macro_rules
  | `(residual_witness) => `(axiom $(Lean.mkIdent `toyResidualWitness) : False)
residual_witness
"""
LAUNDERED = {
    "macro_argument": MACRO_ARGUMENT,
    "macro_rules_mk_ident": MACRO_RULES,
    "typed_antiquotation": "macro \"w \" n:ident : command => `(axiom $n:ident : False)\n",
    "modifiers_and_comment": (
        "macro \"w \" n:ident : command =>\n"
        "  `(private noncomputable axiom /- name -/ $n : False)\n"
    ),
    "next_line": "macro \"w \" n:ident : command => `(axiom\n    $n : False)\n",
}

# Prose, literals and quoted identifiers mention `axiom $` without declaring one.
CLEAN = """\
/-- A macro must never expand to `axiom $n : False`. -/
-- macro "w " n:ident : command => `(axiom $n : False)
def note : String := "axiom $n"
def «axiom $n» : Nat := 1
macro "five" : term => `(5)
theorem t : five = 5 := rfl
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


class AntiquotedAxioms(unittest.TestCase):
    def test_antiquoted_axiom_names_are_rejected(self) -> None:
        for label, text in LAUNDERED.items():
            with self.subTest(label=label):
                result = run(text)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("axiom declaration with an antiquoted name", result.stderr)

    def test_prose_literals_and_other_macros_stay_clean(self) -> None:
        result = run(CLEAN)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
