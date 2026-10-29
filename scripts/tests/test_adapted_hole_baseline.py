"""Reviewed proof improvements cannot hide changed, copied, or additional holes."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from forbidden_tokens import InheritedSourcePolicy
from integration.extract_downstream_extensions import parse_commands
from sorry_census import census


class AdaptedHoleBaseline(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.path = self.root / "ArkLib/Protocol.lean"
        self.path.parent.mkdir()
        (self.root / "scripts").mkdir()
        self.upstream = ("namespace N\n"
                         "def held : Nat := by\n  exact sorry\n\n"
                         "def improved : Nat := sorry\nend N\n")
        self.current = self.upstream.replace("def improved : Nat := sorry", "def improved : Nat := 7")
        self.path.write_text(self.upstream)
        git = ["git", "-C", str(self.root)]
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        subprocess.run([*git, "add", "ArkLib"], check=True)
        subprocess.run([*git, "-c", "user.name=test", "-c", "user.email=test@example.invalid",
                        "commit", "-qm", "upstream"], check=True)
        self.revision = subprocess.check_output([*git, "rev-parse", "HEAD"], text=True).strip()
        upstream_bytes = self.upstream.encode()
        blob = hashlib.sha1(b"blob " + str(len(upstream_bytes)).encode() + b"\0"
                            + upstream_bytes).hexdigest()
        self.repository = "https://github.com/Verified-zkEVM/ArkLib"
        self.manifest = {"repository": self.repository, "revision": self.revision,
                         "files": ["ArkLib/Protocol.lean"], "downstream_adaptations": [{
                             "path": "ArkLib/Protocol.lean", "upstream_blob": blob,
                             "source_revision": self.revision,
                             "declarations": ["N.improved"], "reason": "Reviewed completion"}]}
        command = next(c for c in parse_commands(self.upstream) if c.full_name == "N.held")
        self.entry = {"file": "ArkLib/Protocol.lean", "decl": "def held",
                      "declaration": "N.held", "sha256": hashlib.sha256(upstream_bytes).hexdigest(),
                      "command_sha256": self.command_hash(self.upstream, command)}
        self.write_current(self.current)

    @staticmethod
    def command_hash(text, command):
        return hashlib.sha256(text[command.start:command.end].strip().encode()).hexdigest()

    def write_manifest(self):
        (self.root / "scripts/arklib-upstream.json").write_text(json.dumps(self.manifest))

    def write_current(self, text):
        self.path.write_text(text)
        self.manifest["downstream_adaptations"][0]["sha256"] = hashlib.sha256(text.encode()).hexdigest()
        self.write_manifest()

    def results(self):
        policy = InheritedSourcePolicy(self.root)
        rows = [row for row in census(self.root) if row["kind"] == "hole"]
        return [(row, policy.matches_adapted_upstream_hole(
            self.root / row["file"], row, self.entry, self.revision, self.repository)) for row in rows]

    def test_unchanged_admitted_command_survives_reviewed_completion(self):
        self.assertEqual([allowed for _, allowed in self.results()], [True])

    def test_extra_token_in_later_command_cannot_reuse_preceding_label(self):
        self.write_current(self.current.replace("\ndef improved", "\n#check sorryAx\n\ndef improved"))
        results = self.results()
        self.assertEqual([row["decl"] for row, _ in results], ["def held", "def held"])
        self.assertEqual([allowed for _, allowed in results], [True, False])

    def test_census_cli_keeps_the_token_boundary_gate(self):
        baseline = self.root / "scripts/sorry_baseline.json"
        baseline.write_text(json.dumps({"repository": self.repository,
            "revision": self.revision, "holes": [self.entry]}))
        command = [sys.executable, str(Path(__file__).resolve().parents[1] / "sorry_census.py"),
                   "--root", str(self.root), "--baseline", str(baseline), "--fail-on-holes"]
        result = subprocess.run(command, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.write_current(self.current.replace("\ndef improved", "\n#check sorryAx\n\ndef improved"))
        result = subprocess.run(command, capture_output=True, text=True)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("1 NEW live hole", result.stderr)

    def test_changed_admitted_body_and_forged_command_hash_are_rejected(self):
        changed = self.current.replace("exact sorry", "exact (sorry)")
        self.write_current(changed)
        self.assertEqual([allowed for _, allowed in self.results()], [False])
        command = next(c for c in parse_commands(changed) if c.full_name == "N.held")
        self.entry["command_sha256"] = self.command_hash(changed, command)
        self.assertEqual([allowed for _, allowed in self.results()], [False])

    def test_new_hole_in_same_body_is_not_inherited(self):
        self.write_current(self.current.replace("exact sorry", "have extra : Nat := sorry\n  exact sorry"))
        self.assertEqual([allowed for _, allowed in self.results()], [False, False])

    def test_copied_name_in_new_namespace_is_not_inherited(self):
        self.write_current(self.current + "namespace Copied\ndef held : Nat := sorry\nend Copied\n")
        self.assertEqual([allowed for _, allowed in self.results()], [True, False])

    def test_duplicate_full_name_is_ambiguous_and_rejected(self):
        self.write_current(self.current.replace("def improved", "def held : Nat := sorry\ndef improved"))
        self.assertEqual([allowed for _, allowed in self.results()], [False, False])

    def test_reviewed_current_hash_and_upstream_base_are_required(self):
        for field, value in (("sha256", "0" * 64), ("upstream_blob", "0" * 40), ("reason", "")):
            with self.subTest(field=field):
                self.write_current(self.current)
                self.manifest["downstream_adaptations"][0][field] = value
                self.write_manifest()
                self.assertEqual([allowed for _, allowed in self.results()], [False])
                # Restore all provenance for the next independent mutation.
                self.restore_base()

    def restore_base(self):
        content = self.upstream.encode()
        self.manifest["downstream_adaptations"][0]["upstream_blob"] = hashlib.sha1(
            b"blob " + str(len(content)).encode() + b"\0" + content).hexdigest()
        self.manifest["downstream_adaptations"][0]["reason"] = "Reviewed completion"

    def test_unreviewed_file_and_changed_upstream_file_digest_are_rejected(self):
        self.entry["sha256"] = "0" * 64
        self.assertEqual([allowed for _, allowed in self.results()], [False])
        self.manifest["downstream_adaptations"] = []
        self.write_manifest()
        self.assertEqual([allowed for _, allowed in self.results()], [False])

    def test_pin_revision_and_repository_cannot_be_replaced(self):
        row = self.results()[0][0]
        policy = InheritedSourcePolicy(self.root)
        self.assertFalse(policy.matches_adapted_upstream_hole(
            self.path, row, self.entry, "0" * 40, self.repository))
        self.assertFalse(policy.matches_adapted_upstream_hole(
            self.path, row, self.entry, self.revision, "https://github.com/Other/Repo"))


if __name__ == "__main__":
    unittest.main()
