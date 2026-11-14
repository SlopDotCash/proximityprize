"""Source preservation and import-boundary regressions for upstream integration."""

import contextlib
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import tomllib
import unittest
from unittest.mock import patch


SCRIPT_DIR = Path(__file__).resolve().parents[1] / "integration"
sys.path.insert(0, str(SCRIPT_DIR))
spec = importlib.util.spec_from_file_location(
    "integration_consolidation", SCRIPT_DIR / "check_consolidation.py")
consolidation = importlib.util.module_from_spec(spec)
spec.loader.exec_module(consolidation)
surface_spec = importlib.util.spec_from_file_location(
    "library_surfaces", SCRIPT_DIR.parent / "update-library-surfaces.py")
surfaces = importlib.util.module_from_spec(surface_spec)
surface_spec.loader.exec_module(surfaces)


class ConsolidationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.content = "module\n\n@[expose] public section\ndef base : Nat := 1\n"
        self.write("ArkLib/Base.lean", self.content)
        self.write("ArkLib.lean", "module\npublic import ArkLib.Base\n")
        self.write("ArkLib/Research/ProximityGap/Client.lean", "import ArkLib.Base\n")
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
        self.write("ArkLib/Base.lean",
                   "module\npublic import ArkLib.Research.ProximityGap.Client\n")
        errors, _ = self.run_check()
        self.assertTrue(any("imports downstream/test source" in error for error in errors))

    def test_missing_renamed_module_is_reported(self):
        self.write("ArkLib/Research/ProximityGap/Client.lean", "import ArkLib.Retired\n")
        errors, _ = self.run_check()
        self.assertTrue(any("Missing local import" in error for error in errors))

    def test_obsolete_local_roots_are_missing_imports_not_external_dependencies(self):
        for module in ("Research.Client", "ProximityPrize.Extensions.Proof", "ArkLibTest.Client"):
            with self.subTest(module=module):
                self.write("ArkLib/Research/ProximityGap/Client.lean", f"import {module}\n")
                errors, _ = self.run_check()
                self.assertIn(
                    "Missing local import: ArkLib/Research/ProximityGap/Client.lean -> " + module,
                    errors)

    def test_cycle_in_downstream_extensions_is_reported(self):
        self.write("ArkLib/Research/ProximityGap/Client.lean",
                   "import ArkLib.Research.ProximityGap.Other\n")
        self.write("ArkLib/Research/ProximityGap/Other.lean",
                   "import ArkLib.Research.ProximityGap.Client\n")
        errors, _ = self.run_check()
        self.assertTrue(any("Import cycle:" in error for error in errors))

    def test_umbrella_cannot_silently_omit_source(self):
        self.write("ArkLib.lean", "module\n")
        errors, _ = self.run_check()
        self.assertTrue(any("re-export every canonical module" in error for error in errors))

    def test_comments_and_strings_do_not_create_import_edges(self):
        source = ("/- import ArkLib.Research.ProximityGap.Fake\n/- nested -/ -/\n"
                  'def text := "import ArkLib.Research.ProximityGap.Fake"\n'
                  "module\npublic import\n  ArkLib.Base\nimport all ArkLib.Other\n")
        self.assertEqual(consolidation.imports(source), ["ArkLib.Base", "ArkLib.Other"])


class LibrarySurfaceGenerationTests(unittest.TestCase):
    @staticmethod
    def glob_matches(glob, module):
        if glob.endswith(".*"):
            prefix = glob[:-2]
            return module == prefix or module.startswith(prefix + ".")
        if glob.endswith(".+"):
            return module.startswith(glob[:-2] + ".")
        return module == glob

    def test_specialized_sources_keep_distinct_owners_and_complete_umbrellas(self):
        with tempfile.TemporaryDirectory(prefix="library-surfaces-") as directory:
            root = Path(directory)
            sources = {
                "ArkLib/Base.lean": "module\n@[expose] public section\ndef base : Nat := 1\n",
                "ArkLib/Data/Ordinary.lean": "def ordinary : Nat := 1\n",
                "ArkLib/ToMathlib/Fast.lean": "def fast : Nat := 1\n",
                "ArkLib/ToMathlib/GHSZ02LargeNProof.lean": "def expensive : Nat := 1\n",
                "ArkLib/Extensions.lean": "-- generated extension umbrella\n",
                "ArkLib/Extensions/Data/Proof.lean": "theorem extensionProof : True := trivial\n",
                "ArkLib/Extensions/Deep/Nested.lean": "theorem nestedProof : True := trivial\n",
                "ArkLib/Compatibility/Proof.lean": "theorem compatibilityProof : True := trivial\n",
                "ArkLib/Compatibility/Deep/Nested.lean": "theorem nestedCompat : True := trivial\n",
                "ArkLib/Downstream.lean": "-- generated downstream umbrella\n",
                "ArkLib/Research/ProximityGap.lean": "import ArkLib.Base\n",
                "ArkLib/Research/ProximityGap/Client.lean": "import ArkLib.Base\n",
                "ArkLib/Tests/Client.lean": "import ArkLib.Base\n",
            }
            for name, text in sources.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")
            scripts = root / "scripts"
            scripts.mkdir()
            (scripts / "arklib-upstream.json").write_text(json.dumps({
                "revision": "a" * 40, "files": ["ArkLib/Base.lean"]}), encoding="utf-8")
            (root / "ArkLib.lean").write_text("-- generated canonical umbrella\n", encoding="utf-8")
            (root / "lakefile.toml").write_text(
                'name = "SurfaceFixture"\n'
                '[[lean_lib]]\nname = "ArkLib"\nrequiresModuleSystem = true\n\n'
                '[[lean_lib]]\nname = "ArkLibTest"\nroots = []\n'
                'globs = ["ArkLib.Tests.+"]\nallowNonModules = true\n\n'
                + surfaces.BEGIN + "\n" + surfaces.END + "\n", encoding="utf-8")
            subprocess.run(["git", "init", "-q", str(root)], check=True, capture_output=True)
            subprocess.run(["git", "-C", str(root), "add", "--", "ArkLib", "ArkLib.lean",
                            "scripts/arklib-upstream.json", "lakefile.toml"],
                           check=True, capture_output=True)
            with patch.object(surfaces, "ROOT", root), contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(surfaces.main(), 0)

            config = tomllib.loads((root / "lakefile.toml").read_text(encoding="utf-8"))
            libraries = {library["name"]: library for library in config["lean_lib"]}
            generic = libraries["ArkLibExtensions"]["globs"]
            for module in ("ArkLib.Data.Ordinary", "ArkLib.ToMathlib.Fast"):
                with self.subTest(generic_extension=module):
                    self.assertTrue(any(self.glob_matches(glob, module) for glob in generic))
            excluded = {
                "ArkLib.Base", "ArkLib.ToMathlib.GHSZ02LargeNProof", "ArkLib.Extensions",
                "ArkLib.Extensions.Data.Proof", "ArkLib.Extensions.Deep.Nested",
                "ArkLib.Compatibility.Proof", "ArkLib.Compatibility.Deep.Nested",
                "ArkLib.Downstream", "ArkLib.Research.ProximityGap",
                "ArkLib.Research.ProximityGap.Client", "ArkLib.Tests.Client",
            }
            for module in excluded:
                with self.subTest(specialized_or_excluded=module):
                    self.assertFalse(any(self.glob_matches(glob, module) for glob in generic))
            self.assertTrue(libraries["ArkLib"]["requiresModuleSystem"])
            self.assertEqual(libraries["ArkLibTest"]["globs"], ["ArkLib.Tests.+"])
            self.assertEqual(libraries["ResearchProximityPrize"]["roots"],
                             ["ArkLib.Research.ProximityGap"])
            downstream = libraries["ProximityPrizeExtensions"]
            self.assertEqual(downstream["roots"], [])
            self.assertEqual(downstream["globs"],
                             ["ArkLib.Downstream", "ArkLib.Extensions.*", "ArkLib.Compatibility.+"])
            for name in ("ArkLibTest", "ArkLibExtensions", "ResearchProximityPrize",
                         "ProximityPrizeExtensions"):
                self.assertTrue(libraries[name]["allowNonModules"])
            self.assertEqual((root / "ArkLib.lean").read_text(),
                             "module\n\npublic import ArkLib.Base\n")
            self.assertEqual((root / "ArkLib/Extensions.lean").read_text(),
                             "import ArkLib.Extensions.Data.Proof\n"
                             "import ArkLib.Extensions.Deep.Nested\n")
            self.assertEqual((root / "ArkLib/Downstream.lean").read_text(),
                             "import ArkLib.Extensions\n"
                             "import ArkLib.Compatibility.Deep.Nested\n"
                             "import ArkLib.Compatibility.Proof\n")


if __name__ == "__main__":
    unittest.main()
