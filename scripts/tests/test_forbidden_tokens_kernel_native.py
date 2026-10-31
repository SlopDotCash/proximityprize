"""forbidden_tokens must reject direct calls to the kernel's native-reduction primitives.

`native_decide` is banned by name, but a proof term can call the primitive under it,
`Lean.ofReduceBool`, without the tactic. Each `NATIVE` case compiles on Lean v4.30.0-rc2
(only a deprecation warning), and `#print axioms` reports `Lean.ofReduceBool` or
`Lean.ofReduceNat` together with `Lean.trustCompiler`: the kernel trusts compiled code.
"""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "forbidden_tokens.py"

AUX = "def aux : Bool := decide (2 ^ 10 = 1024)\ndef auxN : Nat := 2 ^ 10\n"

NATIVE = {
    "ofReduceBool": AUX + "theorem a : 2 ^ 10 = 1024 :=\n"
    "  of_decide_eq_true (Lean.ofReduceBool aux true rfl)\n",
    "ofReduceNat": AUX + "theorem b : auxN = 1024 := Lean.ofReduceNat auxN 1024 rfl\n",
    "open_namespace": AUX + "open Lean in\ntheorem c : auxN = 1024 := ofReduceNat auxN 1024 rfl\n",
    "guillemets": AUX + "theorem d : 2 ^ 10 = 1024 :=\n"
    "  of_decide_eq_true (Lean.«ofReduceBool» aux true rfl)\n",
    "reduceBool": AUX + "theorem e : Lean.reduceBool aux = true := rfl\n",
    "reduceNat": AUX + "theorem f : Lean.reduceNat auxN = 1024 := rfl\n",
}

# Comments and docstrings that only mention the primitives, and longer identifiers that
# contain them, stay clean. (String literals are scanned like code by `TOKEN_RE`, the
# same as for `native_decide`.)
CLEAN = """\
/-- Kernel-checked: no `native_decide` / `Lean.ofReduceBool`. -/
theorem k1 : 2 ^ 10 = 1024 := by decide
-- no Lean.ofReduceNat or Lean.reduceBool here
def myofReduceBoolCount : Nat := 0
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


class KernelNativeReduction(unittest.TestCase):
    def test_native_reduction_primitives_are_rejected(self) -> None:
        for label, text in NATIVE.items():
            with self.subTest(label=label):
                result = run(text)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("forbidden token", result.stdout + result.stderr)

    def test_comments_and_longer_names_stay_clean(self) -> None:
        result = run(CLEAN)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
