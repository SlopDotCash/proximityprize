"""Selection logic and cache checks of the changed-module audit."""
import importlib.util
import json
from pathlib import Path
import tempfile
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

    def test_importers_of_a_rebuilt_dependency_are_rebuilt(self):
        # B changed and needs A, which has no compiled module; C also imports A, so its
        # compiled module predates the A that is about to be built
        imports = {A: [], B: [A], C: [A]}
        self.assertEqual(audit.select(imports, {B}, compiled={B, C}), {A, B, C})
        self.assertEqual(audit.select(imports, {B}, compiled={A, B, C}), {B})

    def test_dependency_outside_the_trees_is_never_selected(self):
        chosen = audit.select(self.imports, {A}, compiled=set())
        self.assertNotIn(LIB, chosen)
        self.assertEqual(chosen, {A, B, C, D})

    def test_unknown_changed_path_is_ignored(self):
        self.assertEqual(audit.select(self.imports, {"docs/notes.lean"}, compiled=set()), set())


class Outdated(unittest.TestCase):
    def setUp(self):
        self.imports = {A: [LIB], B: [A], C: [B], D: [A]}

    def test_a_finished_run_leaves_nothing_outdated(self):
        self.assertEqual(audit.outdated(self.imports, {}), set())
        self.assertEqual(audit.outdated(self.imports, {A: 1.0, B: 2.0, C: 3.0, D: 2.0}), set())

    def test_importer_older_than_a_module_compiled_here_is_outdated(self):
        # A was compiled again after B; C imports only B and is not affected directly
        self.assertEqual(audit.outdated(self.imports, {A: 5.0, B: 2.0, C: 3.0, D: 6.0}), {B})

    def test_importer_never_compiled_here_is_outdated(self):
        self.assertEqual(audit.outdated(self.imports, {A: 1.0}), {B, D})
        self.assertEqual(audit.outdated(self.imports, {B: 1.0}), {C})


class Audited(unittest.TestCase):
    def test_keeps_an_excluded_source_only_when_a_covered_source_imports_it(self):
        root = "ArkLib/Research/ProximityGap.lean"
        bench = "ArkLib/Research/ProximityGap/Bench.lean"
        umbrella = "ArkLib/Research/ProximityGap/All.lean"
        scratch = "ArkLib/Research/ProximityGap/Scratch.lean"
        dead = "ArkLib/Research/ProximityGap/Dead.lean"
        imports = {root: [bench, LIB], bench: [umbrella, A], umbrella: [A], A: [],
                   scratch: [dead, A], dead: []}
        excluded = {bench, umbrella, scratch, dead}
        self.assertEqual(audit.audited(imports, excluded), {root, bench, umbrella, A})
        self.assertEqual(audit.audited(imports, set()), set(imports))


class LakeTextHash(unittest.TestCase):
    def test_matches_values_computed_by_lean(self):
        # `#eval (mixHash 1723 (hash s)).toNat` in Lean 4.35.0
        cases = {
            "": 2433114807351286261,
            "abc": 5685835570530936180,
            "import Mathlib\n\ntheorem t : True := trivial\n": 15918801189741214880,
            "αβγ→∀ 12345678": 10199208443016428576,
        }
        for text, value in cases.items():
            self.assertEqual(audit.lake_text_hash(text.encode("utf-8")), f"{value:016x}")

    def test_ignores_carriage_returns_before_line_feeds(self):
        self.assertEqual(audit.lake_text_hash(b"a\r\nb\r\n"), audit.lake_text_hash(b"a\nb\n"))
        self.assertNotEqual(audit.lake_text_hash(b"a\nb\n"), audit.lake_text_hash(b"a\nb"))


def write_trace(path: Path, source: str, value: str) -> None:
    """A trace file with the nesting Lake uses for a module's inputs."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({
        "schemaVersion": "2025-09-10",
        "depHash": "0000000000000001",
        "inputs": [
            ["deps", [["imports", [["ArkLib.Other:importAllArts", "aaaaaaaaaaaaaaaa"]]]]],
            ["Lean 4.35.0", "bbbbbbbbbbbbbbbb"],
            ["/some/other/checkout/" + source, value],
            ["options", [["-DautoImplicit=false", "cccccccccccccccc"]]],
        ]}), encoding="utf-8")


class CacheOrigin(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.library = Path(self.directory.name) / "library"
        self.mirror = Path(self.directory.name) / "mirror"
        for base in (self.library, self.mirror):
            (base / "ArkLib/Research/ProximityGap").mkdir(parents=True)

    def tearDown(self):
        self.directory.cleanup()

    def test_reads_the_hash_of_the_module_source_only(self):
        trace = self.library / (A[:-5] + ".trace")
        write_trace(trace, A, "1234567890abcdef")
        self.assertEqual(audit.recorded_source_hash(trace, A), "1234567890abcdef")
        self.assertIsNone(audit.recorded_source_hash(trace, B))

    def test_unreadable_trace_has_no_hash(self):
        trace = self.library / (A[:-5] + ".trace")
        self.assertIsNone(audit.recorded_source_hash(trace, A))
        trace.write_text("legacy 12345", encoding="utf-8")
        self.assertIsNone(audit.recorded_source_hash(trace, A))
        trace.write_text("[1, 2]", encoding="utf-8")
        self.assertIsNone(audit.recorded_source_hash(trace, A))

    def test_linked_module_is_described_by_its_trace(self):
        write_trace(self.library / (A[:-5] + ".trace"), A, "1111111111111111")
        self.assertIsNone(audit.cached_source_hash(self.library, self.mirror, A))
        shared = self.library / (A[:-5] + ".olean")
        shared.write_bytes(b"olean")
        (self.mirror / (A[:-5] + ".olean")).symlink_to(shared)
        self.assertEqual(audit.cached_source_hash(self.library, self.mirror, A),
                         "1111111111111111")

    def test_module_compiled_by_an_earlier_run_is_described_by_its_sidecar(self):
        write_trace(self.library / (A[:-5] + ".trace"), A, "1111111111111111")
        (self.library / (A[:-5] + ".olean")).write_bytes(b"shared")
        (self.mirror / (A[:-5] + ".olean")).write_bytes(b"private")
        self.assertIsNone(audit.cached_source_hash(self.library, self.mirror, A))
        (self.mirror / (A[:-5] + audit.SIDECAR)).write_text("2222222222222222\n",
                                                             encoding="utf-8")
        self.assertEqual(audit.cached_source_hash(self.library, self.mirror, A),
                         "2222222222222222")

    def test_reports_modules_outside_the_audit_built_from_another_text(self):
        root = Path(self.directory.name) / "root"
        (root / "ArkLib/Data").mkdir(parents=True)
        (root / "ArkLib/Research/ProximityGap").mkdir(parents=True)
        (self.library / "ArkLib/Data").mkdir(parents=True)
        for source, text, recorded in (
                (LIB, b"-- current\n", audit.lake_text_hash(b"-- other\n")),
                ("ArkLib/Data/Same.lean", b"-- same\n", audit.lake_text_hash(b"-- same\n")),
                (A, b"-- audited\n", "0000000000000000")):
            (root / source).write_bytes(text)
            (self.library / (source[:-5] + ".olean")).write_bytes(b"olean")
            write_trace(self.library / (source[:-5] + ".trace"), source, recorded)
        (self.library / "ArkLib/Data/Orphan.olean").write_bytes(b"olean")
        self.assertEqual(audit.outside_mismatches(root, self.library, {A}), [LIB])


if __name__ == "__main__":
    unittest.main()
