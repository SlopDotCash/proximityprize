"""Pin and destination guards must fail before any network or checkout mutation."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location(
    "arklib_reference", Path(__file__).resolve().parents[1] / "arklib-reference.py")
REFERENCE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(REFERENCE)


class ReferenceGuards(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.manifest = self.root / "manifest.json"
        self.head = "a" * 40
        self.manifest.write_text(json.dumps({"pull_requests": [
            {"number": 7, "head": self.head, "disposition": "reviewed"}]}))
        self.addCleanup(patch.stopall)
        patch.object(REFERENCE, "ROOT", self.root).start()
        patch.object(REFERENCE, "MANIFEST", self.manifest).start()
        patch.object(REFERENCE, "REFERENCE", self.root).start()
        (self.root / ".git").mkdir()
        self.git = patch.object(REFERENCE, "git").start()

    def run_main(self, *args):
        with patch("sys.argv", ["arklib-reference.py", *args]), \
                contextlib.redirect_stderr(io.StringIO()), \
                contextlib.redirect_stdout(io.StringIO()):
            REFERENCE.main()

    def test_unknown_pr_does_not_fetch(self):
        with self.assertRaises(SystemExit):
            self.run_main("fetch", "--pr", "8")
        self.git.assert_not_called()

    def test_native_destination_does_not_fetch(self):
        with self.assertRaises(SystemExit):
            self.run_main("worktree", "--pr", "7", "--path", str(self.root / "nested"))
        self.git.assert_not_called()

    def test_mismatched_head_prevents_worktree(self):
        self.git.side_effect = ["", "b" * 40]
        with self.assertRaises(RuntimeError):
            self.run_main("worktree", "--pr", "7", "--path", str(self.root.parent / (self.root.name + "-pr")))
        self.assertFalse(any(call.args[0] == "worktree" for call in self.git.call_args_list))
        self.assertEqual(self.git.call_args_list[0].args[-1],
                         f"{self.head}:refs/remotes/pr-audit/pr-7")
        self.assertEqual(self.git.call_args_list[0].args[-2], REFERENCE.SOURCE)


if __name__ == "__main__":
    unittest.main()
