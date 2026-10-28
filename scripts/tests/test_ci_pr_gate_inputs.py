#!/usr/bin/env python3
"""Pull requests that change a merge-gate input must run that gate.

`ci.yml` skips `validate.sh` (forbidden tokens, sorry census, axiom audit,
Python regressions, knowledge-base checks) when its "Determine Lean
validation scope" step decides a pull request is documentation-only, and
`kb-generated.yml` only runs where its triggers say so.  These tests run the
scope step verbatim against throwaway commits and check that every file a
gate reads is covered by at least one pull-request check.
"""

import os
from pathlib import Path
import re
import subprocess
import tempfile
import textwrap
import unittest

REPO = Path(__file__).resolve().parents[2]
WORKFLOWS = REPO / ".github" / "workflows"


def scope_step_script() -> str:
    """Return the shell body of ci.yml's validation-scope step."""

    lines = (WORKFLOWS / "ci.yml").read_text(encoding="utf-8").splitlines()
    start = next(i for i, line in enumerate(lines)
                 if line.strip() == "- name: Determine Lean validation scope")
    run = next(i for i in range(start, len(lines)) if lines[i].strip() == "run: |")
    indent = len(lines[run]) - len(lines[run].lstrip())
    body = []
    for line in lines[run + 1:]:
        if line.strip() and len(line) - len(line.lstrip()) <= indent:
            break
        body.append(line)
    return textwrap.dedent("\n".join(body)) + "\n"


def lean_relevant(changed: str) -> bool:
    """Run the scope step for a pull request that changes only ``changed``."""

    with tempfile.TemporaryDirectory(prefix="ci-scope-test-") as tmp:
        root = Path(tmp)
        git = ["git", "-C", str(root), "-c", "user.name=t", "-c", "user.email=t@example.invalid"]
        subprocess.run(["git", "init", "-q", str(root)], check=True)
        (root / "base.txt").write_text("base\n")
        subprocess.run([*git, "add", "-A"], check=True)
        subprocess.run([*git, "commit", "-qm", "base"], check=True)
        base = subprocess.run([*git, "rev-parse", "HEAD"], check=True,
                              capture_output=True, text=True).stdout.strip()
        target = root / changed
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text("changed\n")
        subprocess.run([*git, "add", "-A"], check=True)
        subprocess.run([*git, "commit", "-qm", "head"], check=True)
        output = root / "github-output"
        env = dict(os.environ, EVENT_NAME="pull_request", PR_BASE_SHA=base,
                   GITHUB_OUTPUT=str(output))
        subprocess.run(["bash", "-c", scope_step_script()], cwd=root, env=env,
                       check=True, capture_output=True)
        values = dict(line.split("=", 1) for line in output.read_text().splitlines())
        return values["lean-relevant"] == "true"


def pull_request_paths(workflow: str) -> list[str]:
    """Return the ``on.pull_request.paths`` globs of a workflow (empty if absent)."""

    lines = (WORKFLOWS / workflow).read_text(encoding="utf-8").splitlines()
    paths: list[str] = []
    section = None
    in_paths = False
    for line in lines:
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        indent = len(line) - len(line.lstrip())
        if indent == 0:
            section = line.strip()
            continue
        if section != "on:":
            continue
        if indent == 2:
            current = line.strip()
            in_paths = False
            continue
        if current == "pull_request:" and indent == 4:
            in_paths = line.strip() == "paths:"
            continue
        if current == "pull_request:" and in_paths and line.strip().startswith("- "):
            paths.append(line.strip()[2:].strip().strip("\"'"))
    return paths


def github_glob(pattern: str, path: str) -> bool:
    """Match a GitHub Actions path filter (`**` crosses `/`, `*` does not)."""

    regex = ""
    i = 0
    while i < len(pattern):
        if pattern.startswith("**/", i):
            regex += "(?:.*/)?"
            i += 3
        elif pattern.startswith("**", i):
            regex += ".*"
            i += 2
        elif pattern[i] == "*":
            regex += "[^/]*"
            i += 1
        else:
            regex += re.escape(pattern[i])
            i += 1
    return re.fullmatch(regex, path) is not None


class ValidationInputsRunValidation(unittest.TestCase):
    """Gate inputs under scripts/ must not be classified as documentation."""

    INPUTS = [
        "scripts/flagship_axioms.txt",       # axiom_audit.py manifest (gate 3)
        "scripts/sorry_baseline.json",       # sorry_census.py baseline (gate 2)
        "scripts/requirements-validation.txt",
        "scripts/tests/test_exact_jump_dp.cpp",
        "scripts/probes/probe_rate_quarter_exact_jump_multiline.cpp",
    ]

    def test_gate_inputs_are_lean_relevant(self):
        for path in self.INPUTS:
            with self.subTest(path=path):
                self.assertTrue((REPO / path).is_file(), f"{path} no longer exists")
                self.assertTrue(lean_relevant(path), f"{path} skips validate.sh")

    def test_documentation_only_changes_still_skip_lean(self):
        for path in ["README.md", "docs/kb/papers/BCIKS20.md", "scripts/README.md"]:
            with self.subTest(path=path):
                self.assertFalse(lean_relevant(path))


class KnowledgeBaseInputsCheckedOnPullRequests(unittest.TestCase):
    """KB gate inputs need either validate.sh or the KB workflow on pull requests."""

    INPUTS = [
        "blueprint/src/references.bib",
        "docs/kb/papers/BCIKS20.md",
        "docs/kb/sources/BCIKS20/metadata.yml",
        "docs/kb/_generated/references.json",
        "docs/kb/_generated/lean-citations.json",
    ]

    def test_kb_inputs_are_checked(self):
        kb_paths = pull_request_paths("kb-generated.yml")
        for path in self.INPUTS:
            with self.subTest(path=path):
                self.assertTrue((REPO / path).is_file(), f"{path} no longer exists")
                checked = lean_relevant(path) or any(github_glob(p, path) for p in kb_paths)
                self.assertTrue(checked, f"no pull-request check runs the KB gates for {path}")


class GlobHelper(unittest.TestCase):
    def test_github_glob(self):
        self.assertTrue(github_glob("docs/kb/papers/**", "docs/kb/papers/a/b.md"))
        self.assertTrue(github_glob("ArkLib/**/*.lean", "ArkLib/A.lean"))
        self.assertFalse(github_glob("docs/*.md", "docs/kb/a.md"))


if __name__ == "__main__":
    unittest.main()
