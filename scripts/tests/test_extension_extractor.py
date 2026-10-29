"""Keep the migration aid's fail-closed preservation checks in the normal suite."""

from pathlib import Path
import sys
import unittest


sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "integration"))
import extract_downstream_extensions as extractor


class ExtensionExtractorTests(unittest.TestCase):
    def test_source_preservation_and_ambiguous_command_regressions(self):
        extractor.self_test()

    def promotion(self, downstream, upstream):
        old = next(c for c in extractor.parse_commands(downstream) if c.name == "interpolate")
        new = next(c for c in extractor.parse_commands(upstream) if c.name == "interpolate")
        return extractor.promoted_private_duplicate(
            downstream, old, {new.full_name: ("ArkLib/Canonical.lean", new)},
            {"ArkLib/Canonical.lean": upstream})

    def test_private_helper_promoted_to_identical_public_owner_is_reused(self):
        downstream = ("namespace ReedSolomon\nvariable (n : Nat)\n"
                      "private noncomputable def interpolate : Nat := n\nend ReedSolomon\n")
        upstream = ("module\n@[expose] public section\nnamespace ReedSolomon\n"
                    "variable (n : Nat)\nnoncomputable def interpolate : Nat := n\nend ReedSolomon\n")
        self.assertEqual(self.promotion(downstream, upstream)[0], "ArkLib/Canonical.lean")
        # Different signatures, bodies, namespaces, attributes, or context are
        # genuine review cases, even when a simple declaration name matches.
        for changed in (downstream.replace(":= n", ":= n + 1"),
                        downstream.replace(": Nat :=", ": Int :="),
                        downstream.replace("(n : Nat)", "(n : Nat) (extra : Nat)"),
                        downstream.replace("namespace ReedSolomon", "namespace Other")
                                  .replace("end ReedSolomon", "end Other"),
                        downstream.replace("private noncomputable", "@[simp] private noncomputable")):
            with self.subTest(source=changed):
                self.assertIsNone(self.promotion(changed, upstream))

    def test_local_named_declarations_are_not_private_promotions(self):
        downstream = "namespace N\nlocal def interpolate : Nat := 1\nend N\n"
        upstream = "namespace N\ndef interpolate : Nat := 1\nend N\n"
        self.assertIsNone(self.promotion(downstream, upstream))

    def test_removed_sealed_command_takes_its_entire_prefix_chain(self):
        source = ("namespace N\n"
                  "set_option maxHeartbeats 1000000 in\n"
                  "seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in\n"
                  "theorem moved : True := by trivial\n"
                  "section FoldStepLogic\n"
                  "theorem retained : True := by trivial\n"
                  "end FoldStepLogic\nend N\n")
        moved = next(c for c in extractor.parse_commands(source) if c.name == "moved")
        command = source[moved.start:moved.end]
        self.assertIn("set_option maxHeartbeats", command)
        self.assertIn("seal sDomain", command)
        retained = source[:moved.start] + source[moved.end:]
        self.assertNotIn("maxHeartbeats", retained)
        self.assertNotIn("seal ", retained)
        self.assertEqual(extractor.declaration_names(retained), {"N.retained"})
        self.assertIn("section FoldStepLogic", retained)

    def test_removed_name_brings_its_moved_canonical_owner_into_scope(self):
        modules = extractor.canonical_owner_modules("ArkLib/ReedSolomon.lean", [
            {"name": "ReedSolomon.weightConstraint",
             "upstream_owner": "ArkLib/ReedSolomon/Constrained.lean"},
            {"name": "ReedSolomon.otherMovedLemma",
             "upstream_owner": "ArkLib/ReedSolomon/Constrained.lean"}])
        self.assertEqual(modules, {"ArkLib.ReedSolomon", "ArkLib.ReedSolomon.Constrained"})


if __name__ == "__main__":
    unittest.main()
