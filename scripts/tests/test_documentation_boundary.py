"""Regression coverage for the source/documentation boundary."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import tomllib
import unittest
from unittest.mock import patch


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
        self.checker.AGENTS_PATH = self.root / "AGENTS.md"
        self.checker.CLAUDE_PATH = self.root / "CLAUDE.md"

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
                         [f"Markdown belongs outside ArkLib: {Path('ArkLib/Data/README.md')}"])

    def test_links_in_comments_and_fenced_examples_are_ignored(self):
        docs = self.root / "docs"
        docs.mkdir()
        (self.root / "AGENTS.md").write_text("")
        scripts = self.root / "scripts"
        scripts.mkdir()
        (scripts / "README.md").write_text("")
        (docs / "example.md").write_text(
            "<!-- [commented link](missing-comment.md) -->\n"
            "~~~markdown\n[example](missing-tilde.md)\n~~~\n"
            "```markdown\n[example](missing-backtick.md)\n```\n"
            "[real link](missing-real.md)\n"
        )
        self.assertEqual(self.checker.check_markdown_links(),
                         [f"Broken link in {Path('docs/example.md')}: missing-real.md"])

    def test_research_documents_are_checked(self):
        folder = self.root / "Research" / "ProximityPrize"
        folder.mkdir(parents=True)
        doc = folder / "AGENTS.md"
        doc.write_text("Research guide.\n")
        self.assertIn(doc, self.checker.tracked_markdown_files())

    def test_markdown_visibility_boundaries(self):
        cases = {
            "multiline comment": "<!--\n[hidden](missing.md)\n-->\n",
            "comment with fence": "<!--\n~~~\n-->\n",
            "longer closing fence": "~~~md\n[hidden](missing.md)\n~~~~\n",
            "short fence does not close": "~~~~\n~~~\n[hidden](missing.md)\n~~~~\n",
            "mixed markers do not close": "~~~\n```\n[hidden](missing.md)\n~~~\n",
            "closing fence with text": "~~~\n~~~text\n[hidden](missing.md)\n~~~\n",
            "indented fence": "   ~~~md\n[hidden](missing.md)\n   ~~~\n",
            "comment opener inside fence": "~~~html\n<!--\n~~~\n",
            "comment closer inside fence": "~~~html\n-->\n~~~\n",
            "backticks inside tilde fence": "~~~\n```\n[hidden](missing.md)\n~~~\n",
            "inline code": "`[hidden](missing.md)`\n",
            "inline comment example": "`<!--`\n",
            "double backtick inline code": "``[hidden](missing.md) ` <!--``\n",
            "four backtick fence": "````md\n```\n[hidden](missing.md)\n````\n",
        }
        doc = self.root / "example.md"
        for name, example in cases.items():
            with self.subTest(name=name):
                doc.write_text(example + "[real](missing-real.md)\n", encoding="utf-8")
                with patch.object(self.checker, "tracked_markdown_files", return_value=[doc]):
                    self.assertEqual(self.checker.check_markdown_links(),
                                     ["Broken link in example.md: missing-real.md"])

    def test_unclosed_blocks_hide_links_to_end_of_file(self):
        doc = self.root / "example.md"
        for opener in ("<!--", "~~~markdown", "```markdown"):
            with self.subTest(opener=opener):
                doc.write_text(opener + "\n[hidden](missing.md)\n", encoding="utf-8")
                with patch.object(self.checker, "tracked_markdown_files", return_value=[doc]):
                    self.assertEqual(self.checker.check_markdown_links(), [])

    def test_existing_links_and_links_next_to_comments(self):
        doc = self.root / "example.md"
        (self.root / "exists.md").write_text("", encoding="utf-8")
        doc.write_text("[valid](exists.md)\n<!-- hidden -->[real](missing.md)\n"
                       "[split]<!-- hidden -->(missing-split.md)\n", encoding="utf-8")
        with patch.object(self.checker, "tracked_markdown_files", return_value=[doc]):
            self.assertEqual(self.checker.check_markdown_links(),
                             ["Broken link in example.md: missing.md"])


class WebsiteDocumentationTargets(unittest.TestCase):
    def test_local_site_build_selects_all_default_library_docs_and_blueprint(self):
        """Exercise the actual shell flow with fake tools, without invoking Lake or TeX."""
        repo = Path(__file__).resolve().parents[2]
        config = tomllib.loads((repo / "lakefile.toml").read_text())
        libraries = {lib["name"] for lib in config["lean_lib"]}
        expected = {target + ":docs" for target in config["defaultTargets"]
                    if target in libraries} | {"ArkLibBlueprint:docs"}
        with tempfile.TemporaryDirectory(prefix="site-docs-test-") as tmp:
            root = Path(tmp)
            scripts = root / "scripts"
            scripts.mkdir()
            (scripts / "build-web.sh").write_text((repo / "scripts/build-web.sh").read_text())
            calls = root / "calls.jsonl"
            lake = scripts / "lake-locked.sh"
            lake.write_text("#!/usr/bin/env python3\n"
                            "import json, os, pathlib, sys\n"
                            "with open(os.environ['DOCS_TEST_CALLS'], 'a') as f:\n"
                            " f.write(json.dumps(sys.argv[1:]) + '\\n')\n"
                            "if any(arg.endswith(':docs') for arg in sys.argv[1:]):\n"
                            " p = pathlib.Path('.lake/build/doc')\n"
                            " p.mkdir(parents=True, exist_ok=True)\n"
                            " (p / 'index.html').write_text('API fixture')\n")
            lake.chmod(0o755)
            binary = root / "bin"
            binary.mkdir()
            blueprint = binary / "leanblueprint"
            blueprint.write_text("#!/usr/bin/env python3\n"
                                 "import pathlib, sys\n"
                                 "p = pathlib.Path('print/print.pdf' if sys.argv[1] == 'pdf' "
                                 "else 'web/index.html')\n"
                                 "p.parent.mkdir(parents=True, exist_ok=True)\n"
                                 "p.write_text('blueprint fixture')\n")
            blueprint.chmod(0o755)
            (root / "blueprint").mkdir()
            env = dict(os.environ, DOCS_TEST_CALLS=str(calls),
                       PATH=str(binary) + os.pathsep + os.environ["PATH"])
            subprocess.run(["bash", "scripts/build-web.sh"], cwd=root, env=env,
                           check=True, capture_output=True, text=True)
            commands = [json.loads(line) for line in calls.read_text().splitlines()]
            docs = [target for command in commands if command[0] == "build"
                    for target in command[1:] if target.endswith(":docs")]
            self.assertCountEqual(docs, expected)
            self.assertIn(["build", "ArkLibBlueprint"], commands)
            self.assertIn(["exe", "checkdecls", "blueprint/lean_decls"], commands)
            self.assertTrue((root / "home_page/docs/index.html").is_file())
            self.assertTrue((root / "home_page/blueprint/index.html").is_file())


if __name__ == "__main__":
    unittest.main()
