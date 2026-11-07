"""forbidden_tokens must reject direct use of the compiler-trust axioms."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "forbidden_tokens.py"

# Each term compiles on Lean v4.30.0-rc2 (with a deprecation warning) and
# `#print axioms` reports [Lean.ofReduceBool, Lean.trustCompiler]: the result is
# native evaluation that the kernel never checks.
DIRECT = {
    "ofReduceBool": (
        "def f : Bool := 2 ^ 10 == 1024\n"
        "theorem a : f = true := Lean.ofReduceBool f true (Eq.refl true)\n"
    ),
    "ofReduceNat": (
        "def g : Nat := 2 ^ 10\n"
        "theorem b : g = 1024 := Lean.ofReduceNat g 1024 (Eq.refl 1024)\n"
    ),
    "open_namespace": (
        "def h : Bool := 3 * 7 == 21\n"
        "open Lean in\n"
        "theorem c : h = true := ofReduceBool h true (Eq.refl true)\n"
    ),
    "trustCompiler": "theorem d : True := (fun _ => trivial) Lean.trustCompiler\n",
}

# Comments, docstrings and longer identifiers are not uses.
CLEAN = """\
/-- Kernel-checked: no `native_decide` / `Lean.ofReduceBool`. -/
theorem k1 : 3 * 7 = 21 := by decide
-- avoids Lean.ofReduceNat and Lean.trustCompiler
theorem k2 : 2 = 2 := rfl
def myofReduceBoolLemma : Nat := 1
def ofReduceNat_note : Nat := 2
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


class ReduceAxioms(unittest.TestCase):
    def test_direct_uses_are_rejected(self) -> None:
        for label, text in DIRECT.items():
            with self.subTest(label=label):
                result = run(text)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("forbidden token", result.stderr)

    def test_comments_and_longer_names_stay_clean(self) -> None:
        result = run(CLEAN)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
