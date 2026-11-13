"""Post-build axiom inventory from Lean metadata (repository audit 2026-10-28, T02/T03).

`scripts/axiom_audit.py` lists every axiom constant declared in an imported
`ArkLib` module (including research and extensions) from Lean's environment. It sees
every name form and axioms added without the `axiom` keyword and requires each to be a
residual pinned in `scripts/residual_axioms.txt` with the same fully qualified
name and module. The Lean-gated test runs the generated command on the pinned
toolchain (set LEAN_TEST_EXECUTABLE).
"""

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
import axiom_audit  # noqa: E402
import forbidden_tokens  # noqa: E402

LEAN = os.environ.get("LEAN_TEST_EXECUTABLE")
DIGEST = "sha256:" + "0" * 64


def pins(*entries: tuple[str, str]) -> dict:
    return {fqn: forbidden_tokens.Pin(fqn, path, DIGEST, "#2", 1) for fqn, path in entries}


def lean_output(*rows: tuple[str, str]) -> str:
    return "noise\n" + "".join(f"AXIOM-INVENTORY\t{n}\t{m}\n" for n, m in rows)


class Inventory(unittest.TestCase):
    def test_pinned_axiom_in_its_module_passes(self):
        out = lean_output(("Ns.residual", "ArkLib.A.B"))
        self.assertEqual(axiom_audit.check_inventory(out, pins(("Ns.residual", "ArkLib/A/B.lean"))),
                         ([], []))

    def test_unpinned_axiom_fails(self):
        failures, _ = axiom_audit.check_inventory(lean_output(("Sneaky.x", "Research.P")), {})
        self.assertEqual(len(failures), 1)
        self.assertIn("Sneaky.x: axiom declared in Research.P is not a residual pinned", failures[0])

    def test_pinned_name_in_another_module_fails(self):
        failures, _ = axiom_audit.check_inventory(
            lean_output(("Ns.residual", "ArkLib.Other")), pins(("Ns.residual", "ArkLib/A/B.lean")))
        self.assertEqual(failures, ["Ns.residual: axiom declared in ArkLib.Other, but its pin "
                                    "names ArkLib/A/B.lean"])

    def test_names_are_compared_canonically(self):
        out = lean_output(("«Ns».«a b»", "ArkLib.A"))
        self.assertEqual(axiom_audit.check_inventory(out, pins(("Ns.«a b»", "ArkLib/A.lean"))),
                         ([], []))

    def test_missing_pinned_axiom_is_a_warning(self):
        failures, warnings = axiom_audit.check_inventory(
            lean_output(), pins(("Ns.gone", "ArkLib/A.lean")))
        self.assertEqual(failures, [])
        self.assertIn("Ns.gone: pinned residual is not an axiom of ArkLib.A", warnings[0])

    def test_audited_modules_include_every_pinned_module(self):
        listed = subprocess.run([sys.executable, str(SCRIPTS / "axiom_audit.py"),
                                 "--print-modules"], capture_output=True, text=True,
                                check=True).stdout.split()
        live, errors = forbidden_tokens.load_manifest(axiom_audit.RESIDUALS)
        self.assertEqual(errors, [])
        for pin in live.values():
            self.assertIn(axiom_audit.module_of(pin.file), listed)

    def test_command_filters_the_audited_roots(self):
        command = axiom_audit.inventory_command()
        for root in ("ArkLib",):
            self.assertIn(f"mod.getRoot == `{root}", command)
        self.assertNotIn("mod.getRoot == `ArkLib.Research", command)
        self.assertIn(".axiomInfo", command)


@unittest.skipUnless(LEAN, "set LEAN_TEST_EXECUTABLE to the pinned Lean binary")
class LeanMetadata(unittest.TestCase):
    def test_command_lists_core_axioms_with_their_modules(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Inventory.lean"
            path.write_text("import Lean\n" + axiom_audit.inventory_command(("Init",)),
                            encoding="utf-8")
            proc = subprocess.run([LEAN, str(path)], capture_output=True, text=True,
                                  timeout=300)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("AXIOM-INVENTORY\tpropext\tInit.Core", proc.stdout)
        self.assertIn("AXIOM-INVENTORY\tClassical.choice\tInit.Prelude", proc.stdout)
        self.assertIn("AXIOM-INVENTORY\tsorryAx\tInit.Prelude", proc.stdout)

    def test_default_inventory_detects_unused_extension_axiom(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            extension = root / "ArkLib/Extensions/InventoryFixture.lean"
            extension.parent.mkdir(parents=True)
            audit = root / "Inventory.lean"
            audit.write_text(
                "import Lean\nimport ArkLib.Extensions.InventoryFixture\n"
                "#print axioms fixtureClean\n" + axiom_audit.inventory_command(),
                encoding="utf-8",
            )
            env = dict(os.environ, LEAN_PATH=directory)
            for unexpected_axiom in (False, True):
                with self.subTest(unexpected_axiom=unexpected_axiom):
                    source = "theorem fixtureClean : True := trivial\n"
                    if unexpected_axiom:
                        source += "axiom fixtureUnused : False\n"
                    extension.write_text(source, encoding="utf-8")
                    build = subprocess.run(
                        [LEAN, "-o", str(extension.with_suffix(".olean")), str(extension)],
                        cwd=root, env=env, capture_output=True, text=True, timeout=30,
                    )
                    self.assertEqual(build.returncode, 0, build.stdout + build.stderr)
                    run = subprocess.run(
                        [LEAN, str(audit)], cwd=root, env=env,
                        capture_output=True, text=True, timeout=30,
                    )
                    self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
                    self.assertIn("'fixtureClean' does not depend on any axioms", run.stdout)
                    failures, warnings = axiom_audit.check_inventory(run.stdout, {})
                    self.assertEqual(warnings, [])
                    if unexpected_axiom:
                        self.assertEqual(len(failures), 1)
                        self.assertIn(
                            "fixtureUnused: axiom declared in ArkLib.Extensions.InventoryFixture",
                            failures[0],
                        )
                    else:
                        self.assertEqual(failures, [])


if __name__ == "__main__":
    unittest.main()
