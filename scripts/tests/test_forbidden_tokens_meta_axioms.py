"""forbidden_tokens must reject metaprograms that add kernel declarations."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "forbidden_tokens.py"

# The `run_cmd` case compiles on Lean v4.30.0-rc2, and `#print axioms` lists the
# hidden `toyResidualWitness : False` for the residual "proof".
HIDDEN_AXIOM = """\
import Lean
open Lean Elab Command in
run_cmd liftCoreM <| addDecl (.axiomDecl
  { name := `toyResidualWitness, levelParams := [], type := mkConst ``False, isUnsafe := false })
def ToyGapResidual : Prop := 1 = 2
theorem toyGapResidual_holds : ToyGapResidual := (toyResidualWitness).elim
"""

META = {
    "run_cmd": HIDDEN_AXIOM,
    "run_elab": "run_elab pure ()\n",
    "run_meta": "run_meta pure ()\n",
    "eval_add_and_compile": "#eval show Lean.CoreM Unit from Lean.addAndCompile d\n",
    "elab_add_decl": 'elab "mk_witness" : command => Lean.Elab.Command.liftCoreM (Lean.addDecl d)\n',
    "axiom_decl_value": "def d : Lean.Declaration := .axiomDecl v\n",
}

# Ordinary evaluation and prose: none of these adds a declaration.
CLEAN = """\
#eval (List.range 3).length
/-- Residuals are never added with `run_cmd` or `addDecl`. -/
theorem t : 2 = 2 := rfl
-- run_cmd addDecl (.axiomDecl v) would be rejected in live code
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


class MetaDeclarations(unittest.TestCase):
    def test_metaprogram_declarations_are_rejected(self) -> None:
        for label, text in META.items():
            with self.subTest(label=label):
                result = run(text)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("forbidden metaprogram declaration", result.stderr)

    def test_eval_and_prose_stay_clean(self) -> None:
        result = run(CLEAN)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
