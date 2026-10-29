"""Inherited source-policy debt must never excuse a new or changed declaration."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from forbidden_tokens import InheritedSourcePolicy


class UpstreamSourcePolicy(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.path = self.root / "ArkLib/Tuple.lean"
        self.path.parent.mkdir()
        (self.root / "scripts").mkdir()
        self.path.write_text("theorem old_stub : True := trivial\n")
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        subprocess.run(["git", "-C", str(self.root), "add", "ArkLib"], check=True)
        subprocess.run(["git", "-C", str(self.root), "-c", "user.name=test",
                        "-c", "user.email=test@example.invalid", "commit", "-qm", "upstream"],
                       check=True)
        revision = subprocess.check_output(["git", "-C", str(self.root), "rev-parse", "HEAD"],
                                           text=True).strip()
        provenance = {"repository": "https://github.com/Verified-zkEVM/ArkLib",
                      "revision": revision}
        self.entry = {"file": "ArkLib/Tuple.lean", "declaration": "old_stub",
                      "kind": "vacuous_true_theorem",
                      "sha256": hashlib.sha256(self.path.read_bytes()).hexdigest()}
        self.baseline = dict(provenance, exceptions=[self.entry])
        (self.root / "scripts/arklib-upstream.json").write_text(
            json.dumps(dict(provenance, files=["ArkLib/Tuple.lean"])))
        self.write_baseline()

    def write_baseline(self):
        (self.root / "scripts/upstream-source-policy.json").write_text(json.dumps(self.baseline))

    def test_exact_inherited_site_only(self):
        policy = InheritedSourcePolicy(self.root)
        self.assertTrue(policy.allows(self.path, "old_stub", "vacuous_true_theorem"))
        self.assertFalse(policy.allows(self.path, "new_stub", "vacuous_true_theorem"))
        self.assertFalse(policy.allows(self.path, "old_stub", "native_decide"))
        self.assertFalse(policy.allows(self.path, "old_stub", "custom_axiom"))
        copy = self.root / "ArkLib/Copy.lean"
        copy.write_bytes(self.path.read_bytes())
        self.assertFalse(policy.allows(copy, "old_stub", "vacuous_true_theorem"))

    def test_changed_file_and_forged_digest_are_rejected(self):
        self.path.write_text(self.path.read_text() + "theorem new_stub : True := trivial\n")
        self.assertFalse(InheritedSourcePolicy(self.root).allows(
            self.path, "old_stub", "vacuous_true_theorem"))
        self.entry["sha256"] = hashlib.sha256(self.path.read_bytes()).hexdigest()
        self.write_baseline()
        self.assertFalse(InheritedSourcePolicy(self.root).allows(
            self.path, "old_stub", "vacuous_true_theorem"))

    def test_revision_change_invalidates_exceptions(self):
        self.baseline["revision"] = "0" * 40
        self.write_baseline()
        self.assertFalse(InheritedSourcePolicy(self.root).allows(
            self.path, "old_stub", "vacuous_true_theorem"))

    def test_reviewed_adaptation_does_not_relax_true_stub_file_hash(self):
        original = self.path.read_bytes()
        self.path.write_text(self.path.read_text() + "def improved : Nat := 7\n")
        inventory_path = self.root / "scripts/arklib-upstream.json"
        inventory = json.loads(inventory_path.read_text())
        inventory["downstream_adaptations"] = [{"path": "ArkLib/Tuple.lean",
            "sha256": hashlib.sha256(self.path.read_bytes()).hexdigest(),
            "upstream_blob": hashlib.sha1(b"blob " + str(len(original)).encode()
                                         + b"\0" + original).hexdigest(),
            "source_revision": inventory["revision"],
            "declarations": ["improved"], "reason": "Reviewed completion"}]
        inventory_path.write_text(json.dumps(inventory))
        # Even a valid declaration fingerprint must not weaken this separate gate.
        self.entry["command_sha256"] = hashlib.sha256(original.strip()).hexdigest()
        self.write_baseline()
        self.assertFalse(InheritedSourcePolicy(self.root).allows(
            self.path, "old_stub", "vacuous_true_theorem"))


if __name__ == "__main__":
    unittest.main()
