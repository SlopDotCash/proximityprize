"""Literal example declarations must not discharge the real list-bound debt."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import residual_census as census


class LiteralDeclarations(unittest.TestCase):
    def test_real_list_residual_stays_open_after_literal_example(self):
        original = (Path(__file__).resolve().parents[2] /
                    "ArkLib/Data/CodingTheory/ProximityGap/SubJohnsonListSupply.lean")
        fake = ("\nnamespace ProximityGap.Ownership\n"
                "theorem literal_provider : SubJohnsonListResidual dom k m L A := by trivial\n"
                "end ProximityGap.Ownership\n")
        for literal in ('"' + fake + '"', 'r#"' + fake + '"#',
                        'r##"a quote: "\n' + fake + '"##'):
            with self.subTest(literal=literal), tempfile.TemporaryDirectory() as folder:
                root = Path(folder)
                source = root / "ArkLib/Probe.lean"
                source.parent.mkdir()
                source.write_text(original.read_text(encoding="utf-8") +
                                  "\ndef exampleText : String := " + literal + "\n",
                                  encoding="utf-8")
                declarations, residuals, _ = census.collect(root)
                census.find_providers(declarations, residuals)
                residual, = [r for r in residuals if r["name"] == "SubJohnsonListResidual"]
                self.assertEqual(residual["status"], "open")
                self.assertNotIn("literal_provider", [d["name"] for d in declarations])

    def test_raw_comment_markers_do_not_hide_live_provider(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            source = root / "ArkLib/Probe.lean"
            source.parent.mkdir()
            source.write_text('def FooResidual : Prop := True\n'
                              'def text : String := r##"a quote: " /- --"##\n'
                              'theorem real_provider : FooResidual := trivial\n',
                              encoding="utf-8")
            declarations, residuals, _ = census.collect(root)
            census.find_providers(declarations, residuals)
            self.assertEqual(residuals[0]["status"], "discharged")
