#!/usr/bin/env python3
"""Check renderer completion and stage outputs in a fresh directory outside the project."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
import urllib.request


def require_success(result):
    if result != "success":
        raise ValueError(f"Blueprint rendering did not succeed: {result or 'missing result'}")


def fetch_run_jobs():
    """The jobs of this workflow run attempt, from the GitHub REST API."""
    api = os.environ.get("GITHUB_API_URL", "https://api.github.com")
    url = (f"{api}/repos/{os.environ['GITHUB_REPOSITORY']}/actions/runs/"
           f"{os.environ['GITHUB_RUN_ID']}/attempts/{os.environ.get('GITHUB_RUN_ATTEMPT', '1')}"
           "/jobs?per_page=100")
    request = urllib.request.Request(url, headers={
        "Accept": "application/vnd.github+json",
        "Authorization": f"Bearer {os.environ['GITHUB_TOKEN']}",
    })
    with urllib.request.urlopen(request, timeout=30) as response:
        return json.load(response)["jobs"]


def wait_for_job(name, fetch=fetch_run_jobs, timeout=2700, interval=15, sleep=time.sleep):
    """Wait until the job `name` of this run completes, and return its conclusion.

    The build job starts alongside the renderer instead of after it and waits here only when it
    reaches the steps that read the rendered outputs. A job that never appears or never finishes
    within `timeout` seconds yields no conclusion, which `require_success` rejects."""
    waited = 0
    while True:
        try:
            jobs = fetch()
        except OSError as error:  # a transient API failure; the timeout still bounds the wait
            print(f"Could not read the run's jobs yet: {error}", file=sys.stderr)
            jobs = []
        for job in jobs:
            if job.get("name") == name and job.get("status") == "completed":
                return job.get("conclusion") or ""
        if waited >= timeout:
            return ""
        sleep(interval)
        waited += interval


def require_plain_path(project, relative):
    """Reject symlinked files and ancestors before reading or writing build paths."""
    path = project
    for part in relative.parts:
        path = path / part
        if path.is_symlink():
            raise ValueError(f"Generated output path is a symlink: {path.relative_to(project)}")


def require_web_tree(project, relative):
    require_plain_path(project, relative)
    source = project / relative
    if not source.is_dir():
        raise ValueError(f"Missing generated output: {relative}")
    for path in source.rglob("*"):
        if path.is_symlink() or {".git", ".lake"}.intersection(path.relative_to(project).parts):
            raise ValueError(f"Unexpected generated output: {path.relative_to(project)}")


def render_blueprint(project, run=subprocess.run):
    """Use leanblueprint's renderer commands with our explicit source directory.

    The upstream CLI fixes its root at `<git root>/blueprint`, even when called
    from another directory. Keep its PDF/bibliography/HTML sequence here instead.
    https://github.com/PatrickMassot/leanblueprint/blob/master/leanblueprint/client.py
    """
    blueprint = Path("website/blueprint")
    site = Path("build/site")
    for relative in (blueprint / "src", blueprint / "print", blueprint / "web",
                     blueprint / "print/print.pdf", blueprint / "print/print.bbl",
                     blueprint / "src/web.bbl", blueprint / "lean_decls",
                     site, site / "blueprint", site / "blueprint.pdf"):
        require_plain_path(project, relative)
    if (project / blueprint / "web").exists():
        require_web_tree(project, blueprint / "web")
    source = project / blueprint / "src"
    if not source.is_dir():
        raise ValueError(f"Missing blueprint source: {source}")
    (project / blueprint / "print").mkdir(exist_ok=True)
    run(["latexmk", "-output-directory=../print"], cwd=source, check=True)
    bibliography = blueprint / "print/print.bbl"
    if (project / bibliography).exists():
        require_plain_path(project, bibliography)
        require_plain_path(project, blueprint / "src/web.bbl")
        shutil.copyfile(project / bibliography, source / "web.bbl")
    (project / blueprint / "web").mkdir(exist_ok=True)
    run(["plastex", "-c", "plastex.cfg", "web.tex"], cwd=source, check=True)
    pdf = blueprint / "print/print.pdf"
    require_plain_path(project, pdf)
    if not (project / pdf).is_file():
        raise ValueError(f"Missing generated output: {pdf}")
    require_plain_path(project, blueprint / "lean_decls")
    if not (project / blueprint / "lean_decls").is_file():
        raise ValueError("Missing generated output: website/blueprint/lean_decls")
    require_web_tree(project, blueprint / "web")
    (project / site).mkdir(parents=True, exist_ok=True)
    shutil.copyfile(project / pdf, project / site / "blueprint.pdf")
    destination = project / site / "blueprint"
    if destination.exists():
        shutil.rmtree(destination)
    shutil.copytree(project / blueprint / "web", destination, symlinks=True)


def stage_artifact(project, output):
    if output.resolve().is_relative_to(project.resolve()):
        raise ValueError("The artifact output directory must be outside the project")
    files = (Path("website/blueprint/lean_decls"), Path("build/site/blueprint.pdf"))
    web = Path("build/site/blueprint")
    for relative in (*files, web):
        require_plain_path(project, relative)
        source = project / relative
        if not (source.is_dir() if relative == web else source.is_file()):
            raise ValueError(f"Missing generated output: {relative}")
    require_web_tree(project, web)
    output.mkdir(parents=True, exist_ok=False)
    for relative in files:
        target = output / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(project / relative, target)
    shutil.copytree(project / web, output / web, symlinks=True)


class BlueprintCITests(unittest.TestCase):
    def test_only_success_is_accepted(self):
        for result in ("failure", "cancelled", "skipped", "", None, "unexpected"):
            with self.subTest(result=result):
                with self.assertRaisesRegex(ValueError, "Blueprint rendering did not succeed"):
                    require_success(result)
        require_success("success")

    def test_waiting_returns_the_named_job_conclusion_once_completed(self):
        polls = iter([
            [],
            [{"name": "blueprint", "status": "in_progress", "conclusion": None}],
            [{"name": "build", "status": "completed", "conclusion": "success"},
             {"name": "blueprint", "status": "completed", "conclusion": "failure"}],
        ])
        sleeps = []
        self.assertEqual(
            wait_for_job("blueprint", fetch=lambda: next(polls), sleep=sleeps.append), "failure")
        self.assertEqual(len(sleeps), 2)

    def test_waiting_times_out_without_a_conclusion(self):
        sleeps = []
        result = wait_for_job(
            "blueprint", fetch=lambda: [{"name": "blueprint", "status": "queued"}],
            timeout=30, interval=15, sleep=sleeps.append)
        self.assertEqual(result, "")
        self.assertEqual(len(sleeps), 2)
        with self.assertRaises(ValueError):
            require_success(result)

    def fixture(self, directory):
        project = Path(directory) / "project"
        for name, data in (
            ("website/blueprint/lean_decls", "Nat.add"),
            ("build/site/blueprint.pdf", "%PDF"),
            ("build/site/blueprint/index.html", "<html></html>"),
            ("build/site/blueprint/assets/style.css", "body {}"),
            ("build/site/blueprint/.nojekyll", ""),
            ("build/site/blueprint/.assets/hidden.css", "body {}"),
            (".lake/build/private", "not an output"),
            (".git/config", "not an output"),
            ("env/credentials", "not an output"),
        ):
            path = project / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(data)
        return project, Path(directory) / "artifact"

    def test_staging_copies_only_generated_outputs(self):
        with tempfile.TemporaryDirectory(prefix="arklib-blueprint-ci-") as directory:
            project, output = self.fixture(directory)
            stage_artifact(project, output)
            self.assertEqual(
                {str(path.relative_to(output)) for path in output.rglob("*") if path.is_file()},
                {"website/blueprint/lean_decls", "build/site/blueprint.pdf",
                 "build/site/blueprint/index.html", "build/site/blueprint/assets/style.css",
                 "build/site/blueprint/.nojekyll", "build/site/blueprint/.assets/hidden.css"},
            )
            self.assertEqual((output / "website/blueprint/lean_decls").read_text(), "Nat.add")
            with self.assertRaises(FileExistsError):
                stage_artifact(project, output)

    def test_staging_rejects_output_inside_the_project(self):
        for relative in ("artifact", "build/site/blueprint/artifact"):
            with self.subTest(relative=relative):
                with tempfile.TemporaryDirectory(prefix="arklib-blueprint-ci-") as directory:
                    project, _ = self.fixture(directory)
                    output = project / relative
                    with self.assertRaisesRegex(ValueError, "outside the project"):
                        stage_artifact(project, output)
                    self.assertFalse(output.exists())

    def test_staging_rejects_missing_linked_and_cache_outputs(self):
        for malformed in (
            "missing", "linked_file", "linked_directory", "linked_website", "linked_blueprint",
            "linked_build", "linked_site", "cache", "git",
        ):
            with self.subTest(malformed=malformed):
                with tempfile.TemporaryDirectory(prefix="arklib-blueprint-ci-") as directory:
                    project, output = self.fixture(directory)
                    if malformed == "missing":
                        (project / "website/blueprint/lean_decls").unlink()
                    elif malformed == "linked_file":
                        (project / "build/site/blueprint.pdf").unlink()
                        (project / "build/site/blueprint.pdf").symlink_to(project / ".git/config")
                    elif malformed == "linked_directory":
                        (project / "build/site/blueprint/leak").symlink_to(project / ".lake")
                    elif malformed.startswith("linked_"):
                        name = {"linked_website": "website", "linked_blueprint": "website/blueprint",
                                "linked_build": "build", "linked_site": "build/site"}[malformed]
                        destination = Path(directory) / "outside"
                        shutil.move(str(project / name), destination)
                        (project / name).symlink_to(destination, target_is_directory=True)
                    else:
                        name = ".git" if malformed == "git" else ".lake"
                        (project / "build/site/blueprint" / name).mkdir()
                    with self.assertRaises(ValueError):
                        stage_artifact(project, output)
                    self.assertFalse(output.exists())

    def test_render_uses_moved_sources_and_copies_bibliography_before_html(self):
        with tempfile.TemporaryDirectory(prefix="arklib-blueprint-render-") as directory:
            project = Path(directory) / "project"
            source = project / "website/blueprint/src"
            source.mkdir(parents=True)
            calls = []

            def run(command, cwd, check):
                self.assertEqual(cwd, source)
                self.assertTrue(check)
                calls.append(command)
                if command[0] == "latexmk":
                    (source.parent / "print/print.pdf").write_text("%PDF")
                    (source.parent / "print/print.bbl").write_text("bibliography")
                else:
                    self.assertEqual((source / "web.bbl").read_text(), "bibliography")
                    (source.parent / "web/index.html").write_text("<html></html>")
                    (source.parent / "lean_decls").write_text("Nat.add")

            render_blueprint(project, run=run)
            self.assertEqual(calls, [["latexmk", "-output-directory=../print"],
                                     ["plastex", "-c", "plastex.cfg", "web.tex"]])
            self.assertEqual((project / "build/site/blueprint.pdf").read_text(), "%PDF")
            self.assertTrue((project / "build/site/blueprint/index.html").is_file())
            self.assertFalse((project / "blueprint").exists())

    def test_render_failure_does_not_publish_stale_outputs(self):
        with tempfile.TemporaryDirectory(prefix="arklib-blueprint-render-") as directory:
            project = Path(directory) / "project"
            (project / "website/blueprint/src").mkdir(parents=True)

            def fail(command, **kwargs):
                raise subprocess.CalledProcessError(1, command)

            with self.assertRaises(subprocess.CalledProcessError):
                render_blueprint(project, run=fail)
            self.assertFalse((project / "build/site/blueprint.pdf").exists())

    def test_render_rejects_output_symlinks_before_running_tools(self):
        with tempfile.TemporaryDirectory(prefix="arklib-blueprint-render-") as directory:
            project = Path(directory) / "project"
            (project / "website/blueprint/src").mkdir(parents=True)
            (project / "website/blueprint/print").mkdir()
            outside = Path(directory) / "outside"
            outside.write_text("preserve me")
            (project / "website/blueprint/print/print.pdf").symlink_to(outside)
            calls = []
            with self.assertRaisesRegex(ValueError, "symlink"):
                render_blueprint(project, run=lambda *args, **kwargs: calls.append(args))
            self.assertEqual(calls, [])
            self.assertEqual(outside.read_text(), "preserve me")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command", choices=("render", "wait-for-success", "stage-artifact", "self-test"))
    parser.add_argument("output", nargs="?", type=Path)
    arguments = parser.parse_args()
    if arguments.command == "self-test":
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(BlueprintCITests)
        return 0 if unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful() else 1
    try:
        if arguments.command == "wait-for-success":
            require_success(wait_for_job("blueprint"))
        elif arguments.command == "render":
            render_blueprint(Path.cwd())
        else:
            if arguments.output is None:
                parser.error("stage-artifact requires an output directory")
            stage_artifact(Path.cwd(), arguments.output)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(error, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
