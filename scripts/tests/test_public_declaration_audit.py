"""Public ownership must respect Lean's module visibility, not just spelling."""

from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch


sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "integration"))
from audit_public_declarations import audit, public_declarations


class PublicDeclarationAuditTests(unittest.TestCase):
    def names(self, source):
        return [record["name"] for record in public_declarations(source)]

    def test_classic_public_private_and_anonymous(self):
        self.assertEqual(self.names("namespace N\ndef visible := 1\n"
                                    "private def hidden := 2\ninstance : Inhabited Nat := ⟨0⟩\nend N\n"),
                         ["N.visible"])

    def test_module_defaults_private_until_public_section(self):
        self.assertEqual(self.names("module\ndef hidden := 1\n"
                                    "public def visible := 2\ndef stillHidden := 3\n"
                                    "@[expose] public section\ndef exposed := 4\n"
                                    "namespace N\ntheorem fact : True := True.intro\nend N\n"),
                         ["visible", "exposed", "N.fact"])

    def test_public_section_ends_without_leaking_visibility(self):
        self.assertEqual(self.names("module\npublic section Named\nnamespace Outer.Inner\n"
                                    "def δ := 1\nend Inner\nend Named\ndef hidden := 2\n"),
                         ["Outer.Inner.δ"])

    def test_comments_strings_and_same_short_name_do_not_make_collisions(self):
        self.assertEqual(self.names('/- public def fake := 1 -/\nnamespace A\n'
                                    'def x := "theorem fake : True := True.intro"\nend A\n'
                                    'namespace B\ndef x := 2\nend B\n'), ["A.x", "B.x"])

    def test_report_detects_distinct_bodies_and_bounds_details(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "ArkLib").mkdir()
            paths = ["ArkLib/A.lean", "ArkLib/B.lean"]
            for index, path in enumerate(paths):
                (root / path).write_text(f"def first := {index}\ndef second := {index}\n")
            with patch("audit_public_declarations.subprocess.check_output",
                       return_value=("\0".join(paths) + "\0").encode()):
                report = audit(root, limit=1)
            self.assertEqual(report["source_files"], 2)
            self.assertEqual(report["public_named_records"], 4)
            self.assertEqual(report["duplicate_names"], 2)
            self.assertEqual(list(report["duplicates"]), ["first"])
            self.assertTrue(report["duplicates_truncated"])
            self.assertNotEqual(report["duplicates"]["first"][0]["command_sha256"],
                                report["duplicates"]["first"][1]["command_sha256"])


if __name__ == "__main__":
    unittest.main()
