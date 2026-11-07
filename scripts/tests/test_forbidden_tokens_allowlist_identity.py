"""One residual_axioms.txt entry pins exactly one reviewed `axiom` declaration.

Repository audit 2026-10-28, T03: the allowlist used to store simple names, so
an entry also authorized an `axiom` with that simple name in any namespace, in
any file and with any statement (the audit's fixture was
`namespace Arbitrary … axiom no_selfReciprocal_factor : False … end Arbitrary`,
accepted as a documented assumption). An entry now pins the fully qualified
name, the defining file and a digest of the reviewed signature together with
its in-scope `variable`/`universe`/`open`/`export`/`include`/`omit` context. A
copy, a relocation, and a statement or context change are all rejected until
the manifest is updated in a reviewed change. A pin records a documented
assumption; it proves nothing.
"""

import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "forbidden_tokens.py"
ALLOWLIST = SCRIPT.parent / "residual_axioms.txt"
sys.path.insert(0, str(SCRIPT.parent))
import forbidden_tokens  # noqa: E402

LEGIT = (
    "namespace Lattice.Hachi\n"
    "variable {q : Nat}\n"
    "/-- The documented residual. -/\n"
    "axiom no_selfReciprocal_factor (h : q % 8 = 5) : q ≠ 0\n"
    "end Lattice.Hachi\n"
)
PINNED = "Lattice.Hachi.no_selfReciprocal_factor"
# tooling-counterexamples.json, case `allowlist_namespace`.
AUDIT_COPY = "namespace Arbitrary\naxiom no_selfReciprocal_factor : False\nend Arbitrary\n"


def run(root: Path, *args: str) -> "subprocess.CompletedProcess[str]":
    """The precheck with `root/manifest.txt` as manifest and `root` as path base."""
    return subprocess.run(
        [sys.executable, str(SCRIPT), "--root", str(root),
         "--allowlist", str(root / "manifest.txt"), *args],
        capture_output=True, text=True, encoding="utf-8", cwd=str(root),
        env={**os.environ, "PYTHONIOENCODING": "utf-8"},
    )


class PinnedTree:
    """A scratch tree whose manifest pins the declarations it starts with."""

    def __init__(self, files: dict[str, str]):
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)
        for name, text in files.items():
            self.write(name, text)
        printed = run(self.root, "--print-residual-manifest", "Src")
        assert printed.returncode == 0, printed.stdout + printed.stderr
        (self.root / "manifest.txt").write_text(printed.stdout, encoding="utf-8")

    def write(self, name: str, text: str) -> None:
        path = self.root / "Src" / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def scan(self, *paths: str) -> "subprocess.CompletedProcess[str]":
        return run(self.root, *(paths or ("Src",)))

    def __enter__(self) -> "PinnedTree":
        return self

    def __exit__(self, *exc) -> None:
        self._tmp.cleanup()


class ExactPins(unittest.TestCase):
    def test_reviewed_declaration_passes(self):
        with PinnedTree({"Legit.lean": LEGIT}) as tree:
            manifest = (tree.root / "manifest.txt").read_text(encoding="utf-8")
            self.assertTrue(manifest.startswith(f"{PINNED}  Src/Legit.lean  sha256:"), manifest)
            proc = tree.scan()
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
            self.assertIn(f"allowed documented residual axiom {PINNED}", proc.stdout)
            self.assertIn("1 allowlisted residual axiom(s)", proc.stdout)

    def test_comment_and_layout_changes_keep_the_pin(self):
        with PinnedTree({"Legit.lean": LEGIT}) as tree:
            tree.write("Legit.lean", LEGIT.replace(
                "axiom no_selfReciprocal_factor (h : q % 8 = 5) : q ≠ 0",
                "axiom no_selfReciprocal_factor -- tracked in #2\n"
                "    (h : q % 8 = 5) :\n    /- conclusion -/ q ≠ 0"))
            proc = tree.scan()
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)

    def test_root_and_quoted_names_are_fully_qualified(self):
        source = ("namespace Outer\naxiom _root_.rootLevel : 1 = 1\n"
                  "axiom «quoted name».«b.c» : 2 = 2\nend Outer\n")
        with PinnedTree({"Names.lean": source}) as tree:
            manifest = (tree.root / "manifest.txt").read_text(encoding="utf-8")
            self.assertIn("rootLevel  Src/Names.lean", manifest)
            self.assertIn("Outer.«quoted name».«b.c»  Src/Names.lean", manifest)
            proc = tree.scan()
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)

    def test_print_manifest_keeps_the_reviewed_note(self):
        with PinnedTree({"Legit.lean": LEGIT}) as tree:
            manifest = tree.root / "manifest.txt"
            line = manifest.read_text(encoding="utf-8").split("  # ")[0]
            manifest.write_text(f"{line}  # https://example.invalid/issues/2 note\n",
                                encoding="utf-8")
            printed = run(tree.root, "--print-residual-manifest", "Src")
            self.assertEqual(printed.stdout, f"{line}  # https://example.invalid/issues/2 note\n")


class RejectedChanges(unittest.TestCase):
    def assert_rejected(self, proc: "subprocess.CompletedProcess[str]", needle: str) -> None:
        self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
        self.assertIn(needle, proc.stderr)

    def test_audit_copy_under_another_namespace_is_rejected(self):
        with PinnedTree({"Legit.lean": LEGIT}) as tree:
            tree.write("Arbitrary.lean", AUDIT_COPY)
            expected = f"Arbitrary.no_selfReciprocal_factor is not the pinned residual {PINNED}"
            # Alongside the reviewed declaration, and in a file-scoped run.
            self.assert_rejected(tree.scan(), expected)
            self.assert_rejected(tree.scan("Src/Arbitrary.lean"), expected)

    def test_root_copy_in_the_same_file_is_rejected(self):
        with PinnedTree({"Legit.lean": LEGIT}) as tree:
            tree.write("Legit.lean", LEGIT + "axiom no_selfReciprocal_factor : False\n")
            self.assert_rejected(tree.scan(), "no_selfReciprocal_factor is not the pinned residual")

    def test_relocation_to_another_file_is_rejected(self):
        with PinnedTree({"Legit.lean": LEGIT}) as tree:
            (tree.root / "Src" / "Legit.lean").unlink()
            tree.write("Moved.lean", LEGIT)
            self.assert_rejected(tree.scan(), f"residual axiom {PINNED} does not match its "
                                              f"reviewed pin")

    def test_statement_change_is_rejected(self):
        with PinnedTree({"Legit.lean": LEGIT}) as tree:
            tree.write("Legit.lean", LEGIT.replace(": q ≠ 0", ": False"))
            self.assert_rejected(tree.scan(), "does not match its reviewed pin")

    def test_context_changes_are_rejected(self):
        for old, new in (("variable {q : Nat}", "variable {q : Int}"),
                         ("variable {q : Nat}\n", "variable {q : Nat}\nopen Nat\n"),
                         ("namespace Lattice.Hachi\n", "namespace Lattice.Hachi\nuniverse u\n")):
            with self.subTest(new=new), PinnedTree({"Legit.lean": LEGIT}) as tree:
                tree.write("Legit.lean", LEGIT.replace(old, new))
                self.assert_rejected(tree.scan(), "does not match its reviewed pin")

    def test_unknown_namespace_fails_closed(self):
        with PinnedTree({"Legit.lean": LEGIT}) as tree:
            tree.write("Legit.lean", "end Other\n" + LEGIT)
            self.assert_rejected(tree.scan(), "fully qualified name cannot be determined")

    def test_old_simple_name_entries_are_rejected(self):
        with PinnedTree({"Legit.lean": LEGIT}) as tree:
            (tree.root / "manifest.txt").write_text(
                "no_selfReciprocal_factor  # old format\n", encoding="utf-8")
            self.assert_rejected(tree.scan(), "malformed residual-axiom entry")


class LiveManifest(unittest.TestCase):
    """The checked-in manifest parses and names files that exist."""

    def test_entries_are_well_formed(self):
        pins, errors = forbidden_tokens.load_manifest(ALLOWLIST)
        self.assertEqual(errors, [])
        for pin in pins.values():
            with self.subTest(fqn=pin.fqn):
                self.assertTrue((SCRIPT.parent.parent / pin.file).is_file(), pin.file)
                self.assertTrue(pin.note, "each entry needs its tracking issue")

    def test_discharged_names_no_longer_authorize_an_axiom(self):
        # Entries removed when their axiom was proved or turned into a hypothesis.
        pins, _ = forbidden_tokens.load_manifest(ALLOWLIST)
        live = {forbidden_tokens.simple_name(fqn) for fqn in pins}
        for name in ("no_selfReciprocal_factor", "foldKnowledgeStateFunction_toFun_full",
                     "foldOracleVerifier_rbrKnowledgeSoundness"):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as tmp:
                self.assertNotIn(name, live)
                (Path(tmp) / "Revived.lean").write_text(f"axiom {name} : False\n",
                                                        encoding="utf-8")
                proc = subprocess.run([sys.executable, str(SCRIPT), tmp], capture_output=True,
                                      text=True, cwd=str(SCRIPT.parent.parent))
                self.assertNotEqual(proc.returncode, 0, proc.stdout)


if __name__ == "__main__":
    unittest.main()
