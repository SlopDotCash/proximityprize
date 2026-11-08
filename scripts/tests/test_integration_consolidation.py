"""Source preservation and import-boundary regressions for upstream integration."""

import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch


SCRIPT_DIR = Path(__file__).resolve().parents[1] / "integration"
sys.path.insert(0, str(SCRIPT_DIR))
spec = importlib.util.spec_from_file_location(
    "integration_consolidation", SCRIPT_DIR / "check_consolidation.py")
consolidation = importlib.util.module_from_spec(spec)
spec.loader.exec_module(consolidation)


class ConsolidationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.content = "module\n\n@[expose] public section\ndef base : Nat := 1\n"
        self.write("ArkLib/Base.lean", self.content)
        self.write("ArkLib.lean", "module\npublic import ArkLib.Base\n")
        self.write("Research/Client.lean", "import ArkLib.Base\n")
        self.write("scripts/arklib-upstream.json", json.dumps({
            "revision": "a" * 40, "files": ["ArkLib/Base.lean"]}))
        data = self.content.encode()
        self.blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()

    def write(self, path, text):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def run_check(self):
        with patch.object(consolidation, "ROOT", self.root), patch.object(
            consolidation, "pinned_blobs", return_value={"ArkLib/Base.lean": self.blob}
        ):
            return consolidation.check()

    def test_downstream_can_import_pinned_canonical_module(self):
        errors, counts = self.run_check()
        self.assertEqual(errors, [])
        self.assertEqual(counts["canonical_modules"], 1)

    def test_modified_canonical_implementation_is_rejected(self):
        self.write("ArkLib/Base.lean", self.content.replace(":= 1", ":= 2"))
        errors, _ = self.run_check()
        self.assertTrue(any("Canonical source differs" in error for error in errors))

    def test_reviewed_downstream_proof_preserves_upstream_provenance(self):
        changed = self.content.replace(":= 1", ":= 2")
        self.write("ArkLib/Base.lean", changed)
        manifest_path = self.root / "scripts/arklib-upstream.json"
        manifest = json.loads(manifest_path.read_text())
        manifest["downstream_adaptations"] = [{
            "path": "ArkLib/Base.lean", "upstream_blob": self.blob,
            "sha256": hashlib.sha256(changed.encode()).hexdigest(),
            "declarations": ["base"], "source_revision": "b" * 40,
            "reason": "Audited downstream contribution with preserved upstream interface.",
        }]
        manifest_path.write_text(json.dumps(manifest))
        errors, _ = self.run_check()
        self.assertEqual(errors, [])
        self.write("ArkLib/Base.lean", changed.replace(":= 2", ":= 3"))
        errors, _ = self.run_check()
        self.assertTrue(any("reviewed source hash" in error for error in errors))

    def test_reviewed_proof_cannot_change_its_upstream_base(self):
        manifest_path = self.root / "scripts/arklib-upstream.json"
        manifest = json.loads(manifest_path.read_text())
        manifest["downstream_adaptations"] = [{
            "path": "ArkLib/Base.lean", "upstream_blob": "wrong",
            "sha256": hashlib.sha256(self.content.encode()).hexdigest(),
            "declarations": ["base"], "source_revision": "b" * 40,
            "reason": "Reviewed proof.",
        }]
        manifest_path.write_text(json.dumps(manifest))
        errors, _ = self.run_check()
        self.assertTrue(any("different upstream base" in error for error in errors))

    def test_canonical_import_of_downstream_source_is_rejected(self):
        self.write("ArkLib/Base.lean", "module\npublic import Research.Client\n")
        errors, _ = self.run_check()
        self.assertTrue(any("imports downstream/test source" in error for error in errors))

    def test_missing_renamed_module_is_reported(self):
        self.write("Research/Client.lean", "import ArkLib.Retired\n")
        errors, _ = self.run_check()
        self.assertTrue(any("Missing local import" in error for error in errors))

    def test_cycle_in_downstream_extensions_is_reported(self):
        self.write("Research/Client.lean", "import Research.Other\n")
        self.write("Research/Other.lean", "import Research.Client\n")
        errors, _ = self.run_check()
        self.assertTrue(any("Import cycle:" in error for error in errors))

    def test_umbrella_cannot_silently_omit_source(self):
        self.write("ArkLib.lean", "module\n")
        errors, _ = self.run_check()
        self.assertTrue(any("re-export every canonical module" in error for error in errors))

    def test_comments_and_strings_do_not_create_import_edges(self):
        source = ("/- import Research.Fake\n/- nested -/ -/\n"
                  'def text := "import Research.Fake"\n'
                  "module\npublic import\n  ArkLib.Base\nimport all ArkLib.Other\n")
        self.assertEqual(consolidation.imports(source), ["ArkLib.Base", "ArkLib.Other"])


if __name__ == "__main__":
    unittest.main()
