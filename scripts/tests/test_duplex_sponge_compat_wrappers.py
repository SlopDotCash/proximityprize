"""Regression guard: each duplicated DuplexSponge module pair has one implementation owner.

Issue #353 renamed the paper-numbered `DuplexSponge/Security/Lemma5*.lean` files to semantic
names, but the old files were re-added right afterwards and both copies were then edited in
parallel: sixteen pairs of independently compiled implementations, identical apart from their
imports (repository audit 2026-10-28, finding L06). The upstream-ArkLib integration
consolidated them from the live dependency graph; the chosen owner and compatibility path for
every pair are recorded in `scripts/integration/duplex-clone-consolidation.json` (for every
pair the paper-numbered `Lemma5*` module owns the implementation and the semantic name is
the wrapper). This test fails if a compatibility path regains declarations, stops
re-exporting exactly its recorded owner, or if an owner degenerates into a wrapper.
"""
import json
import re
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
SECURITY = REPO / "ArkLib" / "OracleReduction" / "FiatShamir" / "DuplexSponge" / "Security"
MANIFEST = REPO / "scripts" / "integration" / "duplex-clone-consolidation.json"
IMPORT_RE = re.compile(r"import\s+(\S+)")


def strip_lean_comments(text):
    """Drop Lean line comments and (nested) block comments, including docstrings."""
    out = []
    i = 0
    n = len(text)
    while i < n:
        if text.startswith("/-", i):
            depth = 1
            i += 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("unterminated block comment")
            out.append(" ")
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = n if end < 0 else end
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def wrapper_imports(text):
    """Return the imported modules if `text` is import-only Lean source, else None."""
    imports = []
    for line in strip_lean_comments(text).splitlines():
        line = line.strip()
        if not line:
            continue
        match = IMPORT_RE.fullmatch(line)
        if match is None:
            return None
        imports.append(match.group(1))
    return imports


class StripLeanCommentsTests(unittest.TestCase):
    def test_import_only_source_with_header_and_docstring(self):
        source = ("/-\nCopyright header\n-/\n\nimport A.B.C\n\n/-!\n# Doc /- nested -/\n-/\n"
                  "-- trailing note\n")
        self.assertEqual(wrapper_imports(source), ["A.B.C"])

    def test_declarations_are_rejected(self):
        source = "import A.B.C\n\n/-- doc -/\ntheorem t : True := trivial\n"
        self.assertIsNone(wrapper_imports(source))

    def test_unterminated_comment_is_an_error(self):
        with self.assertRaises(ValueError):
            strip_lean_comments("import A\n/- open")


def module_name(repo_path):
    """`ArkLib/.../Security/Foo.lean` -> `ArkLib.....Security.Foo`."""
    return repo_path[: -len(".lean")].replace("/", ".")


class DuplexSpongeCompatWrapperTests(unittest.TestCase):
    def setUp(self):
        self.pairs = json.loads(MANIFEST.read_text(encoding="utf-8"))["pairs"]

    def test_manifest_covers_sixteen_distinct_pairs(self):
        self.assertEqual(len(self.pairs), 16)
        paths = [p["compatibility_module"] for p in self.pairs]
        paths += [p["implementation_owner"] for p in self.pairs]
        self.assertEqual(len(paths), len(set(paths)), "a module appears in two pairs")

    def test_compatibility_paths_are_import_only_wrappers_of_their_owner(self):
        for pair in self.pairs:
            compat = REPO / pair["compatibility_module"]
            with self.subTest(wrapper=compat.name):
                self.assertTrue(compat.is_file(), compat)
                imports = wrapper_imports(compat.read_text(encoding="utf-8"))
                self.assertIsNotNone(
                    imports, f"{compat.name} declares content; keep it an import-only wrapper "
                    "and put the implementation in its recorded owner module")
                self.assertEqual(imports, [module_name(pair["implementation_owner"])],
                                 f"{compat.name} must re-export exactly its recorded owner")

    def test_owners_hold_the_implementation(self):
        for pair in self.pairs:
            owner = REPO / pair["implementation_owner"]
            with self.subTest(owner=owner.name):
                self.assertTrue(owner.is_file(), owner)
                self.assertTrue(owner.parent == SECURITY, owner)
                self.assertIsNone(wrapper_imports(owner.read_text(encoding="utf-8")),
                                  f"{owner.name} is import-only; the pair has no implementation")


if __name__ == "__main__":
    unittest.main()
