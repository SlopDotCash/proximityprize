"""Regression coverage for the source/documentation boundary."""
import importlib.util
from pathlib import Path
import tempfile
import unittest


class DocumentationBoundaryTests(unittest.TestCase):
    def setUp(self):
        spec = importlib.util.spec_from_file_location(
            "docs_integrity", Path(__file__).resolve().parents[1] / "check-docs-integrity.py")
        self.checker = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.checker)
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.checker.REPO_ROOT = self.root

    def test_lean_source_is_allowed(self):
        folder = self.root / "ArkLib" / "Data"
        folder.mkdir(parents=True)
        (folder / "Basic.lean").write_text("namespace Example\nend Example\n")
        self.assertEqual(self.checker.check_lean_tree_markdown(), [])

    def test_nested_markdown_is_rejected(self):
        folder = self.root / "ArkLib" / "Data"
        folder.mkdir(parents=True)
        (folder / "README.md").write_text("A misplaced document.\n")
        self.assertEqual(self.checker.check_lean_tree_markdown(),
                         ["Markdown belongs outside ArkLib: ArkLib/Data/README.md"])

    def test_research_documents_are_checked(self):
        folder = self.root / "Research" / "ProximityPrize"
        folder.mkdir(parents=True)
        doc = folder / "AGENTS.md"
        doc.write_text("Research guide.\n")
        self.assertIn(doc, self.checker.tracked_markdown_files())


if __name__ == "__main__":
    unittest.main()
