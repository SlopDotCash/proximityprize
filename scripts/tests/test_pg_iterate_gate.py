"""pg-iterate.sh must not print ✅ for a file the required gate rejects.

`requiredTests` names this script as the narrow check for prize work, and the
prize ledgers quote its ✅ OK as the axiom-cleanliness evidence. `lake env lean`
prints nothing for `axiom`, `native_decide`, `bv_decide`, `unsafe`,
`@[implemented_by]` or a metaprogram `addDecl`, and `native_decide` reports a
generated axiom name rather than `sorryAx`, so a type-check plus a `sorryAx`
grep certifies files that `./scripts/validate.sh` fails.
"""
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "pg-iterate.sh"
RESIDUAL_ALLOWLIST = Path(__file__).resolve().parents[1] / "residual_axioms.txt"
# Resolve once: on Windows an unresolved "bash" reaches the WSL stub in
# System32 before PATH is searched.
BASH = shutil.which("bash")

# Stands in for `lake env lean <file>`: the probes below never reach the Lean
# toolchain, so CI gate 1 is the only judge of the source and FAKE_LAKE_STDOUT
# is the only source of `#print axioms` output.
FAKE_LAKE = '''#!/usr/bin/env python3
import os
import sys
sys.stdout.write(os.environ.get("FAKE_LAKE_STDOUT", ""))
sys.exit(int(os.environ.get("FAKE_LAKE_RC", "0")))
'''

CLEAN = "theorem ok : 1 + 1 = 2 := rfl\n"
AXIOM_BRICK = "axiom cheat : False\ntheorem brick : False := cheat\n"
NATIVE_BRICK = "theorem fast : 2 ^ 10 = 1024 := by native_decide\n"
UNSAFE_BRICK = "unsafe def escape : Nat := 0\n"


def documented_residual() -> str:
    for raw in RESIDUAL_ALLOWLIST.read_text(encoding="utf-8").splitlines():
        line = raw.split("#", 1)[0].strip()
        if line:
            return line.split()[0]
    return ""


@unittest.skipIf(BASH is None, "bash is required")
class PgIterateGateParity(unittest.TestCase):
    def run_iterate(self, source: str, *, elapsed: str = "", quiet: bool = False,
                    lake_rc: int = 0):
        with tempfile.TemporaryDirectory(prefix="pg-iterate-test-") as tmp:
            root = Path(tmp)
            probe = root / "Probe.lean"
            probe.write_text(source, encoding="utf-8")
            binaries = root / "bin"
            binaries.mkdir()
            fake_lake = binaries / "lake"
            fake_lake.write_text(FAKE_LAKE, encoding="utf-8")
            fake_lake.chmod(0o755)
            env = {
                **os.environ,
                "PATH": str(binaries) + os.pathsep + os.environ["PATH"],
                "FAKE_LAKE_STDOUT": elapsed,
                "FAKE_LAKE_RC": str(lake_rc),
            }
            args = [BASH, str(SCRIPT)]
            if quiet:
                args.append("-q")
            args.append(str(probe))
            return subprocess.run(args, capture_output=True, encoding="utf-8",
                                  errors="replace", env=env)

    def assert_rejected(self, source: str, code: int, needle: str, **kwargs):
        result = self.run_iterate(source, **kwargs)
        self.assertEqual(result.returncode, code, result.stdout + result.stderr)
        self.assertIn(needle, result.stdout + result.stderr)

    def assert_accepted(self, source: str, **kwargs):
        result = self.run_iterate(source, **kwargs)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("OK", result.stdout)

    # -- CI gate 1 parity ---------------------------------------------------
    def test_clean_file_still_passes(self):
        self.assert_accepted(CLEAN)

    def test_declared_axiom_is_rejected(self):
        self.assert_rejected(AXIOM_BRICK, 1, "forbidden custom axiom")

    def test_native_decide_is_rejected(self):
        self.assert_rejected(NATIVE_BRICK, 1, "forbidden token native_decide")

    def test_unsafe_declaration_is_rejected(self):
        self.assert_rejected(UNSAFE_BRICK, 1, "forbidden unsafe declaration")

    def test_typecheck_failure_keeps_its_own_exit_code(self):
        self.assert_rejected(CLEAN, 3, "error: bad", lake_rc=3,
                             elapsed="Probe.lean:1:0: error: bad\n")

    # -- axiom report -------------------------------------------------------
    def test_standard_axioms_pass(self):
        self.assert_accepted(
            CLEAN,
            elapsed="'brick' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
        )

    def test_axiom_free_declaration_passes(self):
        self.assert_accepted(CLEAN, elapsed="'brick' does not depend on any axioms\n")

    def test_custom_axiom_in_report_is_rejected(self):
        self.assert_rejected(CLEAN, 2, "cheat",
                             elapsed="'brick' depends on axioms: [cheat]\n")

    def test_sorry_ax_in_report_is_rejected(self):
        self.assert_rejected(CLEAN, 2, "sorryAx",
                             elapsed="'brick' depends on axioms: [sorryAx]\n")

    def test_native_decide_axiom_in_report_is_rejected(self):
        self.assert_rejected(
            CLEAN, 2, "native_decide",
            elapsed="'brick' depends on axioms: [brick._native.native_decide.ax_1_1]\n",
        )

    # Lean wraps a long `#print axioms` list across lines; a one-line capture would read
    # nothing and still print ✅. These pin the across-line scan.
    def test_wrapped_axiom_report_is_rejected(self):
        self.assert_rejected(
            CLEAN, 2, "cheat",
            elapsed="'brick' depends on axioms: [propext, Classical.choice,\n"
                    "  Quot.sound, cheat]\n",
        )

    def test_wrapped_standard_axiom_report_passes(self):
        self.assert_accepted(
            CLEAN,
            elapsed="'brick' depends on axioms: [propext, Classical.choice,\n"
                    "  Quot.sound]\n",
        )

    def test_unterminated_axiom_report_fails_closed(self):
        self.assert_rejected(
            CLEAN, 2, "never closes",
            elapsed="'brick' depends on axioms: [propext, cheat\n",
        )

    def test_documented_residual_stays_allowed(self):
        residual = documented_residual()
        if not residual:
            self.skipTest("scripts/residual_axioms.txt documents no residual")
        self.assert_accepted(
            CLEAN, elapsed=f"'brick' depends on axioms: [{residual}]\n")

    def test_namespaced_residual_matches_its_entry(self):
        residual = documented_residual()
        if not residual:
            self.skipTest("scripts/residual_axioms.txt documents no residual")
        self.assert_accepted(
            CLEAN,
            elapsed=f"'brick' depends on axioms: [ArkLib.ProximityGap.{residual}]\n",
        )

    def test_quiet_mode_does_not_hide_a_failed_audit(self):
        self.assert_rejected(CLEAN, 2, "cheat", quiet=True,
                             elapsed="'brick' depends on axioms: [cheat]\n")


if __name__ == "__main__":
    unittest.main()
