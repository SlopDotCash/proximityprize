"""The iterator must distinguish diagnostics from theorem names in lint output."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "pg-iterate.sh"


class IteratorDiagnostics(unittest.TestCase):
    def run_iterator(self, output, status=0):
        with tempfile.TemporaryDirectory() as directory:
            lake = Path(directory) / "lake"
            lake.write_text('#!/usr/bin/env python3\nimport os\nprint(os.environ["MOCK_OUTPUT"])\nraise SystemExit(int(os.environ["MOCK_STATUS"]))\n')
            lake.chmod(0o755)
            env = dict(os.environ, PATH=directory + os.pathsep + os.environ["PATH"],
                       MOCK_OUTPUT=output, MOCK_STATUS=str(status))
            return subprocess.run(["bash", str(SCRIPT), "Example.lean"], env=env,
                                  capture_output=True, text=True)

    def test_lint_theorem_name_is_not_error(self):
        result = self.run_iterator("Example.lean:1:1: warning: unused simp argument\n  [apply] simp only [errorBound]")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_failed_lean_exit_preserved(self):
        self.assertEqual(self.run_iterator("resource failure", 7).returncode, 7)

    def test_sorry_warning_fails(self):
        self.assertNotEqual(self.run_iterator("Example.lean:1:1: warning: declaration uses 'sorry'").returncode, 0)

    def test_sorry_axiom_fails(self):
        self.assertEqual(self.run_iterator("'x' depends on axioms: [propext, sorryAx]").returncode, 2)

    def test_explicit_error_fails(self):
        self.assertNotEqual(self.run_iterator("Example.lean:1:1: error: unknown identifier").returncode, 0)

    def test_standard_axioms_pass(self):
        self.assertEqual(self.run_iterator("'x' depends on axioms: [propext, Classical.choice, Quot.sound]").returncode, 0)
