"""Selection logic of the changed-module audit."""
import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
spec = importlib.util.spec_from_file_location("audit", SCRIPTS / "audit-changed-modules.py")
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)

A = "ArkLib/Research/ProximityGap/A.lean"
B = "ArkLib/Research/ProximityGap/B.lean"
C = "ArkLib/Research/ProximityGap/C.lean"
D = "ArkLib/Research/ProximityGap/D.lean"
LIB = "ArkLib/Data/Lib.lean"


class ParseImports(unittest.TestCase):
    def test_keeps_arklib_imports_in_every_form(self):
        text = (
            "/- header -/\n"
            "import Mathlib.Tactic\n"
            "import ArkLib.Research.ProximityGap.A\n"
            "public import ArkLib.Data.Lib\n"
            "import ArkLib.Research.ProximityGap.Frontier._Under\n"
            "import ArkLib.Research.ProximityGap.«3Fold»\n"
            "/- outer /- nested -/\nimport ArkLib.Commented.Out\n-/\n"
            "  public meta import all ArkLib.Research.ProximityGap.C ArkLib.Research.ProximityGap.D\n"
            "-- import ArkLib.Commented.Out\n"
            "theorem t : True := trivial\n")
        self.assertEqual(audit.parse_imports(text), [
            A, LIB, "ArkLib/Research/ProximityGap/Frontier/_Under.lean",
            "ArkLib/Research/ProximityGap/3Fold.lean", C, D])


class CacheIsolation(unittest.TestCase):
    def test_target_sidecars_stay_private(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            library, mirror = root / "lib", root / "mirror"
            for suffix in (".olean", ".olean.private", ".olean.server", ".ir"):
                path = library / (A[:-5] + suffix)
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(b"shared")
            (library / (B[:-5] + ".olean")).write_bytes(b"dependency")
            audit.mirror_cache(library, mirror, {A})
            self.assertEqual(list((mirror / A).parent.glob("A.*")), [])
            self.assertTrue((mirror / (B[:-5] + ".olean")).is_symlink())

    def test_timeout_records_partial_output(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            expired = subprocess.TimeoutExpired("lean", 1, output=b"stdout", stderr=b"stderr")
            with patch.object(audit.subprocess, "run", side_effect=expired):
                _, code, _, errors = audit.compile_module(root, A, root/"mirror", root, {}, 1)
            self.assertEqual(code, 124)
            self.assertEqual(errors, ["audit: timed out"])
            self.assertIn("stdoutstderr", next(root.glob("*.log")).read_text())


class Select(unittest.TestCase):
    def setUp(self):
        # D imports C imports B imports A; everything imports the library module
        self.imports = {A: [LIB], B: [A, LIB], C: [B], D: [C]}

    def test_changed_module_pulls_in_every_importer(self):
        chosen = audit.select(self.imports, {B}, compiled={A, B, C, D})
        self.assertEqual(chosen, {B, C, D})

    def test_uncompiled_dependency_is_built_first(self):
        self.assertEqual(audit.select(self.imports, {C}, compiled={B, C, D}), {C, D})
        self.assertEqual(audit.select(self.imports, {B}, compiled={C, D}), {A, B, C, D})

    def test_dependency_outside_the_trees_is_never_selected(self):
        chosen = audit.select(self.imports, {A}, compiled=set())
        self.assertNotIn(LIB, chosen)
        self.assertEqual(chosen, {A, B, C, D})

    def test_unknown_changed_path_is_ignored(self):
        self.assertEqual(audit.select(self.imports, {"docs/notes.lean"}, compiled=set()), set())


if __name__ == "__main__":
    unittest.main()
