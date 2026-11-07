"""The real CI scope step must retain removed gate inputs and fail closed."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from test_ci_pr_gate_inputs import scope_step_script


def run_scope(*, invalid_base=False):
    with tempfile.TemporaryDirectory(prefix="ci-scope-rename-") as folder:
        root = Path(folder)
        git = ["git", "-C", str(root), "-c", "user.name=t", "-c", "user.email=t@example.invalid"]
        subprocess.run(["git", "init", "-q", str(root)], check=True)
        subprocess.run([*git, "config", "diff.renames", "true"], check=True)
        source = root / "scripts/axiom_audit.py"
        source.parent.mkdir()
        source.write_text("print('the prize flagship audit')\n")
        subprocess.run([*git, "add", "-A"], check=True)
        subprocess.run([*git, "commit", "-qm", "base"], check=True)
        base = subprocess.check_output([*git, "rev-parse", "HEAD"], text=True).strip()
        (root / "docs").mkdir()
        subprocess.run([*git, "mv", "scripts/axiom_audit.py", "docs/retired-audit.md"], check=True)
        subprocess.run([*git, "commit", "-qm", "rename gate input"], check=True)
        output = root / "github-output"
        env = dict(os.environ, EVENT_NAME="pull_request", GITHUB_OUTPUT=str(output),
                   PR_BASE_SHA="0" * 40 if invalid_base else base)
        result = subprocess.run(["bash", "-c", scope_step_script()], cwd=root,
                                env=env, capture_output=True, text=True)
        return result, output.read_text() if output.exists() else ""


class ScopeRenames(unittest.TestCase):
    def test_moving_flagship_gate_into_docs_still_requires_validation(self):
        result, output = run_scope()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("lean-relevant=true", output)

    def test_invalid_comparison_cannot_certify_documentation_only(self):
        result, output = run_scope(invalid_base=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertNotIn("lean-relevant=false", output)
