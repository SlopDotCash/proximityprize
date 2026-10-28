"""Regression coverage for string literals in the residual census scanner.

A ``"/-"`` or ``"--"`` inside a double-quoted Lean string literal is
string content, not a comment marker. The previous scanner treated it as
a comment opener, so every declaration after such a string was blanked
out of the census: a real provider for a named prize residual would be
missed and the residual would be reported open even though it is
discharged in live code. The same scanner must still honour real
line/block comments and nested block comments.
"""

import importlib.util
from pathlib import Path
import tempfile
import unittest


def _load_census():
    spec = importlib.util.spec_from_file_location(
        "residual_census",
        Path(__file__).resolve().parents[1] / "residual_census.py",
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


rc = _load_census()


class ResidualCensusStringLiteralTests(unittest.TestCase):
    def test_string_block_marker_does_not_hide_provider(self):
        text = (
            "def FooResidual : Prop := True\n"
            'def s : String := "/-"\n'
            "theorem foo_provider : FooResidual := by trivial\n"
        )
        stripped = rc.strip_comments(text)
        self.assertIn("foo_provider", stripped)

    def test_string_line_marker_does_not_mask_rest_of_line(self):
        text = 'def s : String := "--" ++ "x"\n'
        stripped = rc.strip_comments(text)
        self.assertIn('++ "x"', stripped)

    def test_escaped_quote_inside_string(self):
        text = (
            'def s : String := "a \\"/- b"\n'
            "theorem after_provider : FooResidual := by trivial\n"
        )
        self.assertIn("after_provider", rc.strip_comments(text))

    def test_real_block_comment_still_hides(self):
        text = (
            "/- comment\n"
            "theorem hidden_provider : FooResidual := by trivial\n"
            "-/\n"
            "theorem visible_provider : FooResidual := by trivial\n"
        )
        stripped = rc.strip_comments(text)
        self.assertNotIn("hidden_provider", stripped)
        self.assertIn("visible_provider", stripped)

    def test_real_line_comment_still_hides(self):
        text = (
            "-- theorem hidden_provider : FooResidual := by trivial\n"
            "theorem visible_provider : FooResidual := by trivial\n"
        )
        stripped = rc.strip_comments(text)
        self.assertNotIn("hidden_provider", stripped)
        self.assertIn("visible_provider", stripped)

    def test_nested_block_comment_still_hides(self):
        text = (
            "/- outer /- inner -/ theorem hidden_provider : FooResidual := by trivial -/\n"
            "theorem visible_provider : FooResidual := by trivial\n"
        )
        stripped = rc.strip_comments(text)
        self.assertNotIn("hidden_provider", stripped)
        self.assertIn("visible_provider", stripped)

    def test_char_literal_quote_does_not_start_string(self):
        text = (
            "def c : Char := '\"'\n"
            "/- comment\n"
            "theorem hidden_provider : FooResidual := by trivial\n"
            "-/\n"
            "theorem visible_provider : FooResidual := by trivial\n"
        )
        stripped = rc.strip_comments(text)
        self.assertNotIn("hidden_provider", stripped)
        self.assertIn("visible_provider", stripped)

    def test_parse_file_counts_provider_after_string_marker(self):
        # Named prize residual: a provider after a "/-" string literal
        # must be visible to the census, otherwise a discharged residual
        # is reported open.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "ArkLib").mkdir()
            source = root / "ArkLib" / "Test.lean"
            source.write_text(
                "def CurveCommonAgreementResidual : Prop := True\n"
                'def s : String := "/-"\n'
                "theorem curve_provider : CurveCommonAgreementResidual := by trivial\n"
            )
            decls = rc.parse_file(source, root)
        names = [d["name"] for d in decls]
        self.assertIn("CurveCommonAgreementResidual", names)
        self.assertIn("curve_provider", names)


if __name__ == "__main__":
    unittest.main()
