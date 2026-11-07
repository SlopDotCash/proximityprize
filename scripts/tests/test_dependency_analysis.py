"""Tests for ArkLib dependency analysis scripts."""
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parents[1]
DEP_DIR = SCRIPTS_DIR / "dependency_analysis"
sys.path.insert(0, str(DEP_DIR))

import generate_dependency_graph as gdg
import generate_top_level_graph as gtlg


class DependencyAnalysisTests(unittest.TestCase):
    def test_module_name_preserves_a_symlink_alias(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            package = root / "ArkLib"
            package.mkdir()
            (package / "Real.lean").write_text("import ArkLib.Core\n", encoding="utf-8")
            alias = package / "Alias.lean"
            try:
                alias.symlink_to("Real.lean")
            except OSError:
                self.skipTest("Creating a symlink requires platform support")
            self.assertEqual(gdg.normalize_module_name(alias, root), "ArkLib.Alias")
            self.assertEqual(
                gdg.build_dependency_graph([str(alias)], str(root)),
                {"ArkLib.Core": ["ArkLib.Alias"]},
            )

    def test_normalize_module_name_cross_platform(self):
        root = SCRIPTS_DIR.parent
        # Native and forward slash
        full_forward = str(root / "ArkLib" / "Data" / "Basic.lean")
        self.assertEqual(
            gdg.normalize_module_name(full_forward, str(root)),
            "ArkLib.Data.Basic",
        )
        # Windows-style backslashes or mixed separators
        full_backward = str(root).replace("/", "\\") + "\\ArkLib\\Data\\Basic.lean"
        self.assertEqual(
            gdg.normalize_module_name(full_backward, str(root)),
            "ArkLib.Data.Basic",
        )
        # Sibling directory sharing prefix must not be truncated into a false module name
        sibling_file = str(root) + "Lib/Data/Basic.lean"
        sibling_norm = gdg.normalize_module_name(sibling_file, str(root))
        self.assertNotEqual(sibling_norm, "Data.Basic")
        self.assertTrue(sibling_norm.startswith(".."))

    def test_parse_imports(self):
        with tempfile.TemporaryDirectory() as td:
            lean_file = Path(td) / "Test.lean"
            lean_file.write_text(
                "import ArkLib.Data.Basic\n"
                "import Mathlib.Data.Real.Basic\n"
                "-- import Commented.Out\n",
                encoding="utf-8",
            )
            imports = gdg.parse_imports(str(lean_file))
            self.assertEqual(
                imports,
                ["ArkLib.Data.Basic", "Mathlib.Data.Real.Basic"],
            )

    def test_json_and_top_level_graph_generation(self):
        with tempfile.TemporaryDirectory() as td:
            graph = {
                "ArkLib.Data.Basic": ["ArkLib.Algebra.Group", "Mathlib.Data.Nat"],
                "ArkLib.Algebra.Group": [],
            }
            json_file = Path(td) / "deps.json"
            gdg.generate_json_graph(graph, str(json_file))

            with open(json_file, "r", encoding="utf-8") as f:
                data = json.load(f)

            node_map = {n["id"]: n["type"] for n in data["nodes"]}
            self.assertEqual(node_map["ArkLib.Data.Basic"], "internal")
            self.assertEqual(node_map["ArkLib.Algebra.Group"], "internal")
            self.assertEqual(node_map["Mathlib.Data.Nat"], "external")

            dot_file = Path(td) / "top_level.dot"
            gtlg.generate_top_level_graph(str(json_file), str(dot_file))
            self.assertTrue(dot_file.exists())
            dot_content = dot_file.read_text(encoding="utf-8")
            self.assertIn('"Data" -> "Algebra";', dot_content)


if __name__ == "__main__":
    unittest.main()
