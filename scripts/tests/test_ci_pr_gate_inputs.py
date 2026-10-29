#!/usr/bin/env python3
"""Pull requests that change a merge-gate input must run that gate.

The canonical `ci.yml` runs `validate.sh` unconditionally; historical downstream
versions used a "Determine Lean validation scope" step. These tests exercise that
step when present, otherwise verify the unconditional validation command, and
check path-trigger coverage for both CI and the separate import gate.
"""

import os
from pathlib import Path
import re
import shlex
import subprocess
import tempfile
import textwrap
import tomllib
import unittest
from unittest.mock import patch

REPO = Path(__file__).resolve().parents[2]
WORKFLOWS = REPO / ".github" / "workflows"
INTEGRATION_INPUTS = [
    "ProximityPrize.lean",
    "ProximityPrize/Extensions.lean",
    "ArkLibTest/Compatibility/Probability.lean",
    "scripts/arklib-upstream.json",
    "scripts/upstream-source-policy.json",
    "scripts/update-library-surfaces.py",
    "scripts/check-imports.sh",
    "scripts/tests/test_ci_pr_gate_inputs.py",
    *sorted(str(path.relative_to(REPO))
            for path in (REPO / "ProximityPrize/Compatibility").rglob("*.lean")),
    *sorted(str(path.relative_to(REPO))
            for path in (REPO / "scripts/integration").rglob("*")
            if path.suffix in {".py", ".json"}),
]


def yaml_block(lines: list[str], start: int) -> list[str]:
    """Read a block in the repository's indented workflow style, retaining its header."""

    indent = len(lines[start]) - len(lines[start].lstrip())
    end = start + 1
    while end < len(lines):
        line = lines[end]
        if (line.strip() and not line.lstrip().startswith("#")
                and len(line) - len(line.lstrip()) <= indent):
            break
        end += 1
    return lines[start:end]


def event_path_filters(workflow: str, event: str) -> tuple[bool, list[str], list[str]]:
    """Read event presence and its include/ignore path filters without a YAML dependency."""

    lines = (WORKFLOWS / workflow).read_text(encoding="utf-8").splitlines()
    on = next((i for i, line in enumerate(lines) if line == "on:"), None)
    if on is None:
        raise AssertionError(f"{workflow} must declare its events in an on: block")
    triggers = yaml_block(lines, on)
    start = next((i for i, line in enumerate(triggers)
                  if re.fullmatch(r"  " + re.escape(event) + r":(?:\s.*)?", line)), None)
    if start is None:
        return False, [], []
    if triggers[start].split(":", 1)[1].strip():
        raise AssertionError(f"{workflow}: inline event settings need explicit test support")
    body = yaml_block(triggers, start)
    filters = {}
    for key in ["paths", "paths-ignore"]:
        if any(line.startswith(f"    {key}:") and line != f"    {key}:" for line in body):
            raise AssertionError(f"{workflow}: inline {key} needs explicit test support")
        index = next((i for i, line in enumerate(body) if line == f"    {key}:"), None)
        filters[key] = ([] if index is None else
                        [line.strip()[2:].strip().strip("\"'")
                         for line in yaml_block(body, index)[1:]
                         if line.strip().startswith("- ")])
    return True, filters["paths"], filters["paths-ignore"]


def workflow_runs_for_path(workflow: str, event: str, path: str) -> bool:
    enabled, includes, ignores = event_path_filters(workflow, event)
    if not enabled:
        return False
    selected = not includes
    for pattern in includes:
        excluded = pattern.startswith("!")
        if github_glob(pattern[1:] if excluded else pattern, path):
            selected = not excluded
    return selected and not any(github_glob(pattern, path) for pattern in ignores)


def has_unconditional_gate(workflow: str, job: str, command: str) -> bool:
    """Require an actual unguarded run command, not a timing label or an env value."""

    lines = (WORKFLOWS / workflow).read_text(encoding="utf-8").splitlines()
    jobs = next(i for i, line in enumerate(lines) if line == "jobs:")
    job_lines = yaml_block(lines, jobs)
    start = next((i for i, line in enumerate(job_lines) if line == f"  {job}:"), None)
    if start is None:
        return False
    body = yaml_block(job_lines, start)
    if any(line.startswith("    if:") for line in body):
        return False
    for index, line in enumerate(body):
        if not line.startswith("      - "):
            continue
        step = yaml_block(body, index)
        if any(line.startswith("        if:") for line in step):
            continue
        run = next((i for i, line in enumerate(step) if line.startswith("        run:")), None)
        if run is None:
            continue
        script = yaml_block(step, run)
        for line in script:
            content = line.strip().removeprefix("run:").strip()
            if content.startswith("#"):
                continue
            try:
                words = shlex.split(content)
            except ValueError:
                continue  # A shell continuation is checked on its complete command line.
            if not words:
                continue
            if words[0] == command:
                return True
            if words[0] in {"bash", "sh"} and "-c" in words:
                index = words.index("-c") + 1
                if index < len(words):
                    nested = shlex.split(words[index])
                    if nested and nested[0] == command:
                        return True
    return False


def scope_step_script() -> str:
    """Return the shell body of ci.yml's validation-scope step."""

    lines = (WORKFLOWS / "ci.yml").read_text(encoding="utf-8").splitlines()
    starts = [i for i, line in enumerate(lines)
              if line.strip() == "- name: Determine Lean validation scope"]
    if not starts:
        # The canonical upstream CI validates every pull request unconditionally.
        # This is stronger than the historical file-filtered downstream gate.
        if not has_unconditional_gate("ci.yml", "build", "./scripts/validate.sh"):
            raise AssertionError("CI has neither a validation scope nor unconditional validation")
        return 'echo "lean-relevant=true" >> "$GITHUB_OUTPUT"\n'
    start = starts[0]
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

    if not workflow_runs_for_path("ci.yml", "pull_request", changed):
        return False
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

    return event_path_filters(workflow, "pull_request")[1]


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
        *INTEGRATION_INPUTS,
    ]

    def test_gate_inputs_are_lean_relevant(self):
        for path in self.INPUTS:
            with self.subTest(path=path):
                self.assertTrue((REPO / path).is_file(), f"{path} no longer exists")
                self.assertTrue(lean_relevant(path), f"{path} skips validate.sh")

    def test_documentation_changes_use_the_declared_validation_policy(self):
        for path in ["README.md", "docs/kb/papers/BCIKS20.md", "scripts/README.md"]:
            with self.subTest(path=path):
                filtered = "Determine Lean validation scope" in (WORKFLOWS / "ci.yml").read_text()
                self.assertEqual(lean_relevant(path), not filtered)


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


class ImportInputsRunImportGate(unittest.TestCase):
    """A generated root alone, or any integration control input, must run the import gate."""

    def test_pull_requests_and_merge_groups_run_import_check_for_integration_inputs(self):
        self.assertTrue(has_unconditional_gate(
            "check-imports.yml", "check-imports", "./scripts/check-imports.sh"))
        for event in ["pull_request", "merge_group"]:
            for path in INTEGRATION_INPUTS:
                with self.subTest(event=event, path=path):
                    self.assertTrue(workflow_runs_for_path("check-imports.yml", event, path),
                                    f"{event} skips the import gate for {path}")

    def test_merge_groups_run_full_ci_for_integration_inputs(self):
        for path in INTEGRATION_INPUTS:
            with self.subTest(path=path):
                self.assertTrue(workflow_runs_for_path("ci.yml", "merge_group", path))


class ProvenanceCheckoutHistory(unittest.TestCase):
    """Full validation must have the Git objects used by the inherited-debt gates."""

    def assert_full_history_checkout(self, workflow: str, job: str):
        lines = (WORKFLOWS / workflow).read_text().splitlines()
        start = next(i for i, line in enumerate(lines) if line == f"  {job}:")
        body = yaml_block(lines, start)
        steps = [yaml_block(body, i) for i, line in enumerate(body)
                 if line.startswith("      - ")]
        checkouts = [step for step in steps
                     if any(re.match(r"\s*(?:- )?uses: actions/checkout@", line)
                            for line in step)]
        self.assertTrue(checkouts, f"{workflow}/{job} has no source checkout")
        for checkout in checkouts:
            self.assertTrue(any(re.fullmatch(r"\s*fetch-depth: [\"']?0[\"']?", line)
                                for line in checkout),
                            f"{workflow}/{job} cannot read the pinned upstream history")

    def test_validation_and_import_jobs_fetch_pinned_history(self):
        for workflow, job in [("ci.yml", "build"),
                              ("check-imports.yml", "check-imports"),
                              ("incidence-research.yml", "kernel"),
                              ("sponsor-finite.yml", "kernel")]:
            with self.subTest(workflow=workflow, job=job):
                self.assert_full_history_checkout(workflow, job)

    def test_shallow_manual_validator_checkout_is_rejected(self):
        source = (WORKFLOWS / "incidence-research.yml").read_text()
        with tempfile.TemporaryDirectory(prefix="ci-history-test-") as tmp:
            root = Path(tmp)
            for depth in [None, "1"]:
                changed = (source.replace("        with:\n          fetch-depth: 0\n", "", 1)
                           if depth is None else
                           source.replace("fetch-depth: 0", "fetch-depth: 1", 1))
                (root / "incidence-research.yml").write_text(changed)
                with self.subTest(depth=depth), patch(__name__ + ".WORKFLOWS", root):
                    with self.assertRaisesRegex(AssertionError, "pinned upstream history"):
                        self.assert_full_history_checkout("incidence-research.yml", "kernel")


class LeanCachePaths(unittest.TestCase):
    """Every restored or saved Lean cache omits Lake's regenerated setup files."""

    def test_lean_cache_paths_exclude_setup_files(self):
        checked = set()
        for workflow in WORKFLOWS.glob("*.yml"):
            lines = workflow.read_text().splitlines()
            for i, line in enumerate(lines):
                if not line.startswith("      - "):
                    continue
                step = yaml_block(lines, i)
                if not any("uses: actions/cache" in item for item in step):
                    continue
                start = next((j for j, item in enumerate(step)
                              if item.strip().startswith("path:")), None)
                if start is None:
                    continue
                paths = [item.strip() for item in yaml_block(step, start)[1:]
                         if item.strip() and not item.strip().startswith("#")]
                positives = [item for item in paths if item.startswith(".lake")]
                if step[start].strip() == "path: .lake":
                    positives.append(".lake")
                for path in positives:
                    with self.subTest(workflow=workflow.name, path=path):
                        self.assertIn(f"!{path}/**/*.setup.json", paths)
                    checked.add(workflow.name)
        self.assertTrue({"ci.yml", "interaction.yml", "incidence-research.yml",
                         "sponsor-finite.yml", "sponsor-weighted.yml",
                         "multiline-rank-kernel.yml", "first-sponsor-udr.yml",
                         "six-error-support-multiplicity.yml"}.issubset(checked))


class ResearchBuildResourceBudget(unittest.TestCase):
    def test_main_research_build_has_one_job_level_lake_worker(self):
        config = tomllib.loads((REPO / "lakefile.toml").read_text())
        self.assertIn("ResearchProximityPrize", config["defaultTargets"])
        lines = (WORKFLOWS / "ci.yml").read_text().splitlines()
        start = next(i for i, line in enumerate(lines) if line == "  build:")
        body = yaml_block(lines, start)
        env = next(i for i, line in enumerate(body) if line == "    env:")
        self.assertIn("      LEAN_NUM_THREADS: '1'", yaml_block(body, env))
        for line in body:
            if re.match(r"\s*LEAN_NUM_THREADS:", line):
                self.assertRegex(line, r"^\s*LEAN_NUM_THREADS: [\"']?1[\"']?$")


class UnconditionalScopeFallback(unittest.TestCase):
    """Timing metadata and skipped commands must not masquerade as a validation gate."""

    def assert_fallback_rejects(self, workflow):
        with tempfile.TemporaryDirectory(prefix="ci-workflow-test-") as tmp:
            root = Path(tmp)
            (root / "ci.yml").write_text(workflow)
            with patch(__name__ + ".WORKFLOWS", root):
                with self.assertRaisesRegex(AssertionError, "unconditional validation"):
                    scope_step_script()

    def test_timing_metadata_is_not_a_validation_command(self):
        workflow = (WORKFLOWS / "ci.yml").read_text()
        self.assertIn("'./scripts/validate.sh'", workflow)
        self.assert_fallback_rejects(workflow.replace("'./scripts/validate.sh'", "'true'"))

    def test_conditional_validation_is_not_unconditional(self):
        workflow = (WORKFLOWS / "ci.yml").read_text()
        label = "      - name: Time validation wrapper\n"
        self.assertIn(label, workflow)
        self.assert_fallback_rejects(workflow.replace(label, label + "        if: false\n"))


class GlobHelper(unittest.TestCase):
    def test_github_glob(self):
        self.assertTrue(github_glob("docs/kb/papers/**", "docs/kb/papers/a/b.md"))
        self.assertTrue(github_glob("ArkLib/**/*.lean", "ArkLib/A.lean"))
        self.assertFalse(github_glob("docs/*.md", "docs/kb/a.md"))


if __name__ == "__main__":
    unittest.main()
