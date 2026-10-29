"""forbidden_tokens must reject the Lean debug options that defeat the proof gates.

On Lean v4.30.0-rc2 every `REJECTED` snippet below elaborates with exit code 0.
`set_option debug.skipKernelTC true` makes `#print axioms` report that the false
theorem "does not depend on any axioms"; the three `…AsSorry` options report
`[sorryAx]` with only a "declaration uses `sorry`" warning. None of them contains
a `sorry`, `admit` or `axiom` token, so `sorry_census.py --fail-on-holes` passes,
and the flagship audit (`#print axioms`) is blind to the kernel skip. The
`lakefile.toml` form was confirmed with a one-file package: `lake build` reports
no axioms for the same false theorem.
"""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import forbidden_tokens

SCRIPT = Path(__file__).resolve().parents[1] / "forbidden_tokens.py"

CHEAT = """\
import Lean
open Lean Meta Elab Tactic in
elab "my_tac" : tactic =>
  liftMetaTactic1 fun mvarId => do
    mvarId.assign (mkConst ``True.intro)
    return none
"""

REJECTED = {
    "skip_kernel_in": CHEAT
    + "set_option debug.skipKernelTC true in\n"
    + "theorem bad : (1 : Nat) = 2 := by my_tac\n",
    "skip_kernel_file_level": CHEAT
    + "set_option debug.skipKernelTC true\n"
    + "theorem bad : (1 : Nat) = 2 := by my_tac\n",
    "skip_kernel_quoted": CHEAT
    + "set_option «debug».«skipKernelTC» true in\n"
    + "theorem bad : (1 : Nat) = 2 := by my_tac\n",
    "skip_kernel_name_literal": CHEAT
    + "elab \"cheat_decl\" : command => do\n"
    + "  let stx ← `(theorem $(mkIdent `bad) : (1 : Nat) = 2 := by my_tac)\n"
    + "  Command.withScope (fun s => { s with opts := s.opts.setBool `debug.skipKernelTC true })\n"
    + "    (Command.elabCommand stx)\n",
    "skip_kernel_string_component": CHEAT
    + "elab \"cheat_decl\" : command => do\n"
    + "  let stx ← `(theorem $(mkIdent `bad) : (1 : Nat) = 2 := by my_tac)\n"
    + "  let opt := Name.mkStr (Name.mkStr Name.anonymous \"debug\") \"skipKernelTC\"\n"
    + "  Command.withScope (fun s => { s with opts := s.opts.setBool opt true })\n"
    + "    (Command.elabCommand stx)\n",
    "by_as_sorry": "set_option debug.byAsSorry true in\n"
    "theorem bad : (1 : Nat) = 2 := by rfl\n",
    "by_as_sorry_term_level": "theorem bad : (1 : Nat) = 2 := "
    "set_option debug.byAsSorry true in by rfl\n",
    "proof_as_sorry": "set_option debug.proofAsSorry true in\n"
    "theorem bad : (1 : Nat) = 2 := by rfl\n",
    "terminal_tactics_as_sorry": "set_option debug.terminalTacticsAsSorry true in\n"
    "theorem bad : (1 : Nat) = 2 := by omega\n",
}

# Prose, ordinary options and identifiers that merely contain a name are clean.
CLEAN = """\
/-- Axiom-clean: no `debug.skipKernelTC`, no `debug.byAsSorry` anywhere. -/
theorem fine : 2 = 2 := rfl
-- set_option debug.proofAsSorry true would be a hole; not used
/- set_option debug.terminalTacticsAsSorry true in … -/
set_option maxHeartbeats 400000 in
theorem fine2 : 3 = 3 := rfl
set_option linter.style.nativeDecide false
set_option debug.moduleNameAtTimeout false
def skipKernelTC_free : Nat := 1
theorem byAsSorry_is_rejected : 1 = 1 := rfl
"""

LAKEFILE_REJECTED = {
    "lean_options": "[leanOptions]\ndebug.skipKernelTC = true\n",
    "quoted_key": "[leanOptions]\n\"debug.proofAsSorry\" = true\n",
    "weak_prefix": "[moreServerOptions]\nweak.debug.byAsSorry = true\n",
    "after_hash_in_string": "[leanOptions]\nx = \"#\"\ndebug.terminalTacticsAsSorry = true\n",
}

LAKEFILE_CLEAN = """\
name = "Arklib"
# debug.skipKernelTC = true  (commented out: documentation only)
[leanOptions]
autoImplicit = false
weak.linter.style.longFile = 1500
"""


def run(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args], capture_output=True, text=True, check=False
    )


def run_lean(text: str) -> subprocess.CompletedProcess:
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "Probe.lean"
        path.write_text(text, encoding="utf-8")
        return run(str(path))


def run_tree(lakefile: str) -> subprocess.CompletedProcess:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        (root / "ArkLib").mkdir()
        (root / "Research").mkdir()
        (root / "ArkLib" / "Fine.lean").write_text(
            "theorem fine : 1 = 1 := rfl\n", encoding="utf-8"
        )
        (root / "lakefile.toml").write_text(lakefile, encoding="utf-8")
        return run(str(root))


class DebugOptions(unittest.TestCase):
    def test_debug_options_are_rejected(self) -> None:
        for label, text in REJECTED.items():
            with self.subTest(label=label):
                result = run_lean(text)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("forbidden Lean debug option `debug.", result.stderr)

    def test_prose_and_ordinary_options_stay_clean(self) -> None:
        result = run_lean(CLEAN)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_lakefile_debug_options_are_rejected(self) -> None:
        for label, text in LAKEFILE_REJECTED.items():
            with self.subTest(label=label):
                result = run_tree(text)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("in the Lake configuration", result.stderr)

    def test_lakefile_without_debug_options_is_clean(self) -> None:
        result = run_tree(LAKEFILE_CLEAN)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_explicit_lakefile_argument_is_scanned(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "lakefile.toml"
            path.write_text(LAKEFILE_REJECTED["lean_options"], encoding="utf-8")
            result = run(str(path))
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("in the Lake configuration", result.stderr)
            self.assertNotIn("expected a .lean file", result.stderr)

    def test_lakefile_hit_lines(self) -> None:
        self.assertEqual(
            forbidden_tokens.lakefile_debug_option_hits(LAKEFILE_REJECTED["after_hash_in_string"]),
            [(3, "terminalTacticsAsSorry")],
        )
        self.assertEqual(forbidden_tokens.lakefile_debug_option_hits(LAKEFILE_CLEAN), [])


if __name__ == "__main__":
    unittest.main()
