"""Exercise the hosted prebuild handoff and the full build's fail-closed guard."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import textwrap
import unittest

from test_ci_pr_gate_inputs import REPO, WORKFLOWS, find_bash, yaml_block


def shell_step(path: Path, label: str) -> str:
    lines = path.read_text(encoding="utf-8").splitlines()
    start = next(i for i, line in enumerate(lines) if line.strip() == f"- name: {label}")
    step = yaml_block(lines, start)
    script = next(i for i, line in enumerate(step) if line.strip() == "run: |")
    return textwrap.dedent("\n".join(yaml_block(step, script)[1:])) + "\n"


def run_shell(script: str, root: Path, **env: str) -> subprocess.CompletedProcess:
    return subprocess.run([find_bash(), "-eo", "pipefail", "-c", script], cwd=root,
                          env={**os.environ, **env}, capture_output=True, text=True)


class HostedBuildPrebuild(unittest.TestCase):
    def test_prebuilds_are_serial_and_full_build_waits_for_both_and_blueprint(self):
        lines = (WORKFLOWS / "ci.yml").read_text(encoding="utf-8").splitlines()
        canonical = yaml_block(lines, lines.index("  canonical:"))
        extensions = yaml_block(lines, lines.index("  extensions:"))
        full_build = yaml_block(lines, lines.index("  build:"))
        for phase in [canonical, extensions]:
            self.assertIn("    uses: ./.github/workflows/ci-lean-prebuild.yml", phase)
        self.assertIn("    needs: canonical", extensions)
        self.assertIn("    needs: [canonical, extensions, blueprint]", full_build)
        self.assertIn("    if: ${{ always() && !cancelled() }}", full_build)

    def test_failed_preparation_cannot_skip_the_full_gate_as_success(self):
        script = shell_step(WORKFLOWS / "ci.yml", "Require successful preparation")
        results = dict.fromkeys(("CANONICAL_RESULT", "EXTENSIONS_RESULT", "BLUEPRINT_RESULT"),
                                "success")
        self.assertEqual(run_shell(script, REPO, **results).returncode, 0)
        for prerequisite in results:
            for failure in ("failure", "cancelled", "skipped", ""):
                with self.subTest(prerequisite=prerequisite, result=failure):
                    result = run_shell(script, REPO, **{**results, prerequisite: failure})
                    self.assertNotEqual(result.returncode, 0)

    @unittest.skipUnless(shutil.which("jq"), "jq is required for the timing aggregation fixture")
    def test_report_includes_time_and_logs_from_all_three_library_phases(self):
        script = shell_step(WORKFLOWS / "ci.yml",
                            "Combine library timings from the three serial build phases")
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            bundle = root / "arklib-lean-extensions"
            bundle.mkdir()
            for index, name in enumerate(("canonical", "extensions", "library_build"), start=1):
                directory = bundle if index < 3 else root
                row = {"label": "library_build", "real": index, "user": index + 1,
                       "sys": index + 2, "exit_code": 124 if index == 3 else 0, "measured": True}
                (directory / f"{name}.jsonl").write_text(json.dumps(row) + "\n", encoding="utf-8")
                (directory / f"{name}.log").write_text(f"{name}\n", encoding="utf-8")
            results = root / "library_build.jsonl"
            result = run_shell(script, root, RUNNER_TEMP=root.as_posix(),
                               BUILD_TIMING_RESULTS=results.as_posix(),
                               BUILD_TIMING_LOG_DIR=root.as_posix())
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(results.read_text(encoding="utf-8")),
                             {"label": "library_build", "real": 6, "user": 9, "sys": 12,
                              "exit_code": 124, "measured": True})
            self.assertEqual((root / "library_build.log").read_text(encoding="utf-8"),
                             "canonical\nextensions\nlibrary_build\n")

    @unittest.skipUnless(all(shutil.which(tool) for tool in ("tar", "zstd", "sha256sum")),
                         "tar, zstd, and sha256sum are required for the handoff fixture")
    def test_handoff_rejects_changed_identity_and_excludes_regenerated_setup_files(self):
        script = shell_step(REPO / ".github/actions/lean-prebuild-bundle/action.yml",
                            "Verify and transfer Lean build state")
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            workspace = root / "workspace"
            workspace.mkdir()
            subprocess.run(["git", "init", "-q", str(workspace)], check=True)
            subprocess.run(["git", "-C", str(workspace), "-c", "user.name=Fixture",
                            "-c", "user.email=fixture@example.invalid", "commit",
                            "--allow-empty", "-qm", "fixture"], check=True)
            for filename in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
                (workspace / filename).write_text(f"{filename}\n", encoding="utf-8")
            for directory in (".lake/build", ".lake/packages/package"):
                path = workspace / directory
                path.mkdir(parents=True)
                (path / "test.olean").write_bytes(b"build output")
                (path / "test.setup.json").write_text("generated\n", encoding="utf-8")
            bundle = root / "arklib-lean-canonical"
            bundle.mkdir()
            env = {"RUNNER_TEMP": root.as_posix(), "PREBUILD_PHASE": "canonical", "GITHUB_RUN_ID": "1",
                   "RUNNER_OS": "Linux", "RUNNER_ARCH": "X64"}
            save = run_shell(script, workspace, **env, PREBUILD_OPERATION="save")
            self.assertEqual(save.returncode, 0, save.stderr)
            shutil.rmtree(workspace / ".lake")
            for changed in ({"GITHUB_RUN_ID": "2"}, {"RUNNER_ARCH": "ARM64"}):
                reject = run_shell(script, workspace, **{**env, **changed},
                                   PREBUILD_OPERATION="restore")
                self.assertNotEqual(reject.returncode, 0)
                self.assertFalse((workspace / ".lake").exists())
            archive = bundle / "lake.tar.zst"
            original_archive = archive.read_bytes()
            archive.write_bytes(original_archive + b"corruption")
            reject = run_shell(script, workspace, **env, PREBUILD_OPERATION="restore")
            self.assertNotEqual(reject.returncode, 0)
            self.assertFalse((workspace / ".lake").exists())
            archive.write_bytes(original_archive)
            restore = run_shell(script, workspace, **env, PREBUILD_OPERATION="restore")
            self.assertEqual(restore.returncode, 0, restore.stderr)
            self.assertEqual(len(list((workspace / ".lake").rglob("*.olean"))), 2)
            self.assertFalse(list((workspace / ".lake").rglob("*.setup.json")))
