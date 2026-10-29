# Copyright (c) 2026 cerapmen7.
# Released under MIT and Apache-2.0; see LICENSE-MIT and LICENSE.
"""A prize audit must check the configured predicate, not a namesake constant."""

import contextlib
from dataclasses import replace
import io
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import proximity_prize_cleanroom_audit as audit


CANONICAL = {
    "ProximityGap.GrandChallenges.grandMCAChallenge_of_resolution":
        "ProximityGap.grandMCAChallenge",
    "ProximityGap.GrandChallenges.grandListDecodingChallenge_of_resolution":
        "ProximityGap.grandListDecodingChallenge",
    "ProximityGap.prizeResolution_mca_M521": "ProximityGap.GrandChallenges.mcaPrize",
    "ProximityGap.prizeResolution_ld": "ProximityGap.GrandChallenges.listDecodingPrize",
}


class PredicateIdentity(unittest.TestCase):
    def test_active_manifest_pins_full_predicate_names(self):
        entries = audit.parse_manifest(audit.DEFAULT_MANIFEST)
        actual = {entry.decl: entry.conclusion for entry in entries if entry.status == "active"}
        self.assertEqual(actual, CANONICAL)

    def test_full_name_printing_is_enabled(self):
        self.assertIn("set_option pp.fullNames true", audit.build_probe([]))

    def test_qualified_predicate_cannot_match_another_name_segment(self):
        predicate = "ProximityGap.GrandChallenges.mcaPrize"
        entry = audit.Entry("active", "Init", "candidate", predicate, (), 1)
        for other in ("Counterfeit." + predicate, predicate + ".Trivial"):
            with self.subTest(other=other):
                printed = (f"candidate : {other} 0\n"
                           "'candidate' does not depend on any axioms\n")
                self.assertTrue(audit.check_signature(entry, printed))
        printed = (f"candidate : {predicate} 0\n"
                   "'candidate' does not depend on any axioms\n")
        self.assertEqual(audit.check_signature(entry, printed), [])

    def test_global_predicate_does_not_match_a_namespaced_namesake(self):
        entry = audit.Entry("active", "Init", "candidate", "mcaPrize", (), 1)
        printed = ("candidate : Counterfeit.mcaPrize 0\n"
                   "'candidate' does not depend on any axioms\n")
        self.assertTrue(audit.check_signature(entry, printed))


class LeanPredicateIdentity(unittest.TestCase):
    def replay(self, entry, fixture):
        lean = os.environ.get("LEAN_TEST_EXECUTABLE") or shutil.which("lean")
        if not lean:
            self.skipTest("Pinned Lean required for predicate-identity replay")
        # Insert declarations after imports and before the generated options/checks.
        probe = audit.build_probe([entry]).replace("import Init\n", "import Init\n" + fixture, 1)
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "PredicateIdentity.lean"
            source.write_text(probe, encoding="utf-8")
            result = subprocess.run([lean, str(source)], capture_output=True,
                                    text=True, encoding="utf-8", timeout=60)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(audit.parse_axioms(result.stdout)[entry.decl], set())
            manifest = Path(directory) / "targets.txt"
            manifest.write_text(
                f"active Init {entry.decl} {entry.conclusion}\n", encoding="utf-8",
            )
            with patch.object(sys, "argv", ["audit", "--manifest", str(manifest)]), \
                    patch.object(audit, "run_lean", return_value=(0, result.stdout)), \
                    contextlib.redirect_stdout(io.StringIO()), \
                    contextlib.redirect_stderr(io.StringIO()):
                return audit.main(), result.stdout

    def test_each_default_target_rejects_a_proof_of_a_different_predicate(self):
        for target in audit.parse_manifest(audit.DEFAULT_MANIFEST):
            if target.status != "active":
                continue
            predicate = CANONICAL[target.decl]
            short = predicate.rsplit(".", 1)[-1]
            # The genuine configured predicate is false; its namesake is true.
            # Lean checks the supplied proof without axioms, but that proof says
            # nothing about the configured prize/challenge predicate.
            fixture = (f"def {predicate} (_ : Nat) : Prop := False\n"
                       f"def Counterfeit.{short} (_ : Nat) : Prop := True\n"
                       f"theorem {target.decl} : Counterfeit.{short} 0 := True.intro\n")
            with self.subTest(target=target.decl):
                result, _ = self.replay(replace(target, module="Init"), fixture)
                self.assertEqual(result, 1)

    def test_open_namespace_does_not_hide_a_genuine_prize_conclusion(self):
        predicate = "ProximityGap.GrandChallenges.mcaPrize"
        entry = audit.Entry("active", "Init", "candidate", predicate, (), 1)
        fixture = (f"def {predicate} (_ : Nat) : Prop := True\n"
                   "open ProximityGap.GrandChallenges\n"
                   "theorem candidate : mcaPrize 0 := True.intro\n")
        result, printed = self.replay(entry, fixture)
        self.assertIn(predicate, printed)
        self.assertEqual(result, 0)


if __name__ == "__main__":
    unittest.main()
