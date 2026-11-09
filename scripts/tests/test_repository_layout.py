# Copyright (c) 2026 nubs
# SPDX-License-Identifier: MIT OR Apache-2.0
# Authors: nubs (with Codex assistance)
"""Keep removed scratch roots from returning through later contributions."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("repository_layout", Path(__file__).parents[1] / "check-layout.py")
layout = importlib.util.module_from_spec(spec)
spec.loader.exec_module(layout)


class RepositoryLayoutTests(unittest.TestCase):
    def test_authored_html_is_visible_and_generated_output_stays_ignored(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / ".gitignore").write_bytes((layout.ROOT / ".gitignore").read_bytes())
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            for path, expected in [("website/library/new-source.html", 1),
                                   ("website/library/nested/new-source.html", 1),
                                   ("build/site/index.html", 0),
                                   ("downloaded-paper.html", 0)]:
                with self.subTest(path=path):
                    result = subprocess.run(
                        ["git", "-c", "core.excludesFile=/dev/null", "check-ignore",
                         "--no-index", "-q", path], cwd=root)
                    self.assertEqual(result.returncode, expected)

    def test_conventional_roots_and_nested_research_are_allowed(self):
        self.assertEqual([], layout.violations([
            "README.md", ".github/workflows/ci.yml", "ArkLib.lean",
            "ArkLib/Research/ProximityGap/All.lean", "ArkLib/Tests/Data/Basic.lean",
            "docs/research/proximity-gap/DOSSIER.md", "website/library/index.html",
            "website/blueprint/src/web.tex", "scripts/probes/lean/Witness.lean",
            "external/zk-payments-confetti",
        ]))

    def test_legacy_and_unclassified_root_files_are_rejected(self):
        paths = ["scratchpad/probe.py", "_nubs_research/witness.lean", "Research/Foo.lean",
                 "ProximityPrize/Extensions.lean", "ArkLibTest/Test.lean", "home_page/index.html",
                 "blueprint/src/web.tex", "mine/MISSION.md", "notes.txt"]
        self.assertEqual(sorted(paths), layout.violations(paths))


if __name__ == "__main__":
    unittest.main()
