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

# `elabConfig` evaluates the term (`Lean.Elab.Tactic.Config` on v4.30.0-rc2),
# so these are the same `native := true` the flat scan missed. A nested `)`
# also used to truncate the scan and drop a following `+native`.
NESTED = {
    "paren_true": "theorem t : 3 * 7 = 21 := by decide (native := (true))\n",
    "double_paren": "theorem t : 3 * 7 = 21 := by decide (native := ((true)))\n",
    "spaced_paren": "theorem t : 3 * 7 = 21 := by decide ( native := ( true ) )\n",
    "comment_in_paren": "theorem t : 3 * 7 = 21 := by decide (native := (/- keep -/ true))\n",
    "config_value_paren": "theorem t : 3 * 7 = 21 := by decide (config := { native := (true) })\n",
    "config_wrapped": "theorem t : 3 * 7 = 21 := by decide (config := ({ native := (true) }))\n",
    "false_then_plus": "theorem t : 3 * 7 = 21 := by decide (native := (false)) +native\n",
    "bool_true": "theorem t : 3 * 7 = 21 := by decide (native := Bool.true)\n",
    "flag": "theorem t : 3 * 7 = 21 := by decide (native := flag)\n",
    "cfg_name": "theorem t : 3 * 7 = 21 := by decide (config := cfg)\n",
    "with_inherit": "theorem t : 3 * 7 = 21 := by decide (config := { cfg with kernel := true })\n",
    "spread": "theorem t : 3 * 7 = 21 := by decide (config := { ..cfg })\n",
    "quoted_true": "theorem t : 3 * 7 = 21 := by decide (native := «true»)\n",
}

# Kernel-checked forms and prose: none of these is a native evaluation.
CLEAN = """\
theorem k1 : 3 * 7 = 21 := by decide
theorem k2 : 3 * 7 = 21 := by decide +kernel
theorem k3 : 3 * 7 = 21 := by decide (kernel := true)
theorem k4 : 3 * 7 = 21 := by decide (native := false)
theorem k6 : 3 * 7 = 21 := by decide (native := (false))
theorem k7 : 3 * 7 = 21 := by decide (native := ((false)))
theorem k8 : 3 * 7 = 21 := by decide (config := { kernel := true })
theorem k9 : 3 * 7 = 21 := by decide (config := { native := (false) })
theorem k10 : 3 * 7 = 21 := by decide (config := ({ native := (false), kernel := true }))
theorem k11 : 3 * 7 = 21 := by decide +native (native := (false))
theorem k12 : 3 * 7 = 21 := by decide (native := (true)) (native := false)
theorem k13 : 3 * 7 = 21 := by decide +native (config := { kernel := true })
theorem k14 : 3 * 7 = 21 := by decide (config := { cfg with native := (false) })
theorem k15 : 3 * 7 = 21 := by decide (config := { native := (false), ..cfg })
/-- Proved by kernel `decide`, not `decide +native` or `bv_check`. -/
theorem k5 : 2 = 2 := rfl
-- no decide (native := (true)) here
def s : String := "decide (native := (true))"
def msg := "decide +native"
theorem propDecide : Bool := decide (1 = 1)
def αdecide (native : Bool) : Bool := native
theorem notTactic : Bool := αdecide (true)
def «decide (native := (true))» : Nat := 0
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

    def test_nested_and_computed_native_forms_are_rejected(self) -> None:
        for label, text in NESTED.items():
            with self.subTest(label=label):
                result = run(text)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("forbidden native evaluation", result.stderr)

    def test_kernel_forms_and_prose_stay_clean(self) -> None:
        result = run(CLEAN)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
