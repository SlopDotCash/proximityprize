"""forbidden_tokens must reject every native-evaluation form, not only `native_decide`."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "forbidden_tokens.py"

# Each `decide` form compiles on Lean v4.30.0-rc2 and `#print axioms` reports an
# auxiliary `<name>._native.decide.ax_1_1` axiom (native evaluation, no kernel check).
NATIVE = {
    "plus": "theorem a : 2 ^ 10 = 1024 := by decide +native\n",
    "config": "theorem b : 3 * 7 = 21 := by decide (config := { native := true })\n",
    "named": "theorem c : 3 * 7 = 21 := by decide (native := true)\n",
    "split": "theorem d : 3 * 7 = 21 := by\n  decide\n    +native\n",
    "comment_between": "theorem e : 3 * 7 = 21 := by decide /- kernel? -/ +native\n",
    "bv_check": 'theorem f (x : BitVec 8) : x + 0 = x := by bv_check "f.lrat"\n',
}

# Kernel-checked forms and prose: none of these is a native evaluation.
CLEAN = """\
theorem k1 : 3 * 7 = 21 := by decide
theorem k2 : 3 * 7 = 21 := by decide +kernel
theorem k3 : 3 * 7 = 21 := by decide (kernel := true)
theorem k4 : 3 * 7 = 21 := by decide (native := false)
/-- Proved by kernel `decide`, not `decide +native` or `bv_check`. -/
theorem k5 : 2 = 2 := rfl
-- no decide (native := true) here
def s : String := "decide +native"
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


class NativeForms(unittest.TestCase):
    def test_native_forms_are_rejected(self) -> None:
        for label, text in NATIVE.items():
            with self.subTest(label=label):
                result = run(text)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("forbidden native evaluation", result.stderr)

    def test_kernel_forms_and_prose_stay_clean(self) -> None:
        result = run(CLEAN)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
