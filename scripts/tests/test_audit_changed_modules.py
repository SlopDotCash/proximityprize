"""Selection logic of the changed-module audit."""
import importlib.util
from pathlib import Path
import unittest

SCRIPTS = Path(__file__).resolve().parents[1]
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
            "-- import ArkLib.Commented.Out\n"
            "theorem t : True := trivial\n")
        self.assertEqual(audit.parse_imports(text), [
            A, LIB, "ArkLib/Research/ProximityGap/Frontier/_Under.lean",
            "ArkLib/Research/ProximityGap/3Fold.lean"])


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
