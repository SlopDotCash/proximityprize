"""forbidden_tokens must reject `#exit`, which hides the rest of a file from Lean."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "forbidden_tokens.py"

# Lean stops at `#exit`, so the "proof" of the open prize residual below is never
# elaborated, yet the text-based residual census counts it as a discharge.
PHANTOM = """\
namespace ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

def SubJohnsonListResidual (dom : Fin n ↪ F) (k m L A : ℕ) : Prop :=
  SubJohnsonListBound dom k m L A

#exit

theorem subJohnsonListResidual_holds (dom : Fin n ↪ F) (k m L A : ℕ) :
    SubJohnsonListResidual dom k m L A := by simp

end ProximityGap.Ownership
"""

EXITS = {
    "phantom_provider": PHANTOM,
    "bare": "#exit\n",
    "indented": "section\n  #exit\nend\n",
    "after_command": "theorem t : 2 = 2 := rfl #exit\n",
    # `#` is not an identifier character and Lean takes the longest token, so
    # these are still a real `#exit` followed by ignored text.
    "glued_after_term": "theorem t : 2 = 2 := rfl#exit\n",
    "glued_suffix": "#exit_foo\n",
}

# Lean reads this literal as plain (so `#exit` is live); the lexer must not guess
# the interpolated reading and miss it.
AMBIGUOUS = 'def x : Nat := panic! "{" #exit "}"\n'

# Prose, strings and names that merely contain the text stay clean.
CLEAN = """\
/-- Never end a library file with `#exit`. -/
theorem t : 2 = 2 := rfl
-- #exit would be rejected in live code
def s : String := "#exit"
def exit_count : Nat := 0
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


class ExitCommand(unittest.TestCase):
    def test_exit_is_rejected(self) -> None:
        for label, text in EXITS.items():
            with self.subTest(label=label):
                result = run(text)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("forbidden `#exit`", result.stderr)

    def test_exit_hidden_by_an_ambiguous_literal_is_rejected(self) -> None:
        result = run(AMBIGUOUS)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("reads differently as a plain and as an interpolated string", result.stderr)

    def test_comments_strings_and_names_stay_clean(self) -> None:
        result = run(CLEAN)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
