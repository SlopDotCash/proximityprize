"""The fast Lean wrapper must distinguish compiler status, admissions, and path text."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "pg-iterate.sh"


class PgIterateDiagnostics(unittest.TestCase):
    def run_wrapper(self, output, status=0):
        with tempfile.TemporaryDirectory() as directory:
            fake_lake = Path(directory) / "lake"
            fake_lake.write_text('#!/bin/sh\nprintf "%s\\n" "$@" > "$ITERATION_TEST_ARGS"\n'
                                 'printf "%s\\n" "$ITERATION_TEST_OUTPUT"\n'
                                 'exit "$ITERATION_TEST_STATUS"\n')
            fake_lake.chmod(0o755)
            env = dict(os.environ, PATH=directory + os.pathsep + os.environ["PATH"],
                       ITERATION_TEST_OUTPUT=output, ITERATION_TEST_STATUS=str(status),
                       ITERATION_TEST_ARGS=str(Path(directory) / "arguments"))
            result = subprocess.run(["bash", str(SCRIPT), "/tmp/errors-sorryAx.lean"],
                                    env=env, text=True, capture_output=True)
            result.invoked_arguments = (Path(directory) / "arguments").read_text().splitlines()
            return result

    def test_uses_project_autoimplicit_policy(self):
        result = self.run_wrapper("checked")
        self.assertEqual(result.invoked_arguments,
                         ["env", "lean", "-DautoImplicit=false", "/tmp/errors-sorryAx.lean"])

    def test_filenames_and_benign_text_do_not_mean_failure(self):
        result = self.run_wrapper(
            "/tmp/errors-sorryAx.lean:3:1: warning: unused variable `x`\n"
            "No sorry found; errors: 0\n'clean' depends on axioms: [propext]")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_compiler_failure_status_is_preserved(self):
        result = self.run_wrapper("compiler detail", 7)
        self.assertEqual(result.returncode, 7)
        self.assertIn("compiler detail", result.stderr)

    def test_actual_admission_warning_is_rejected(self):
        for prefix in ("", "/tmp/errors.lean:4:0: "):
            with self.subTest(prefix=prefix):
                result = self.run_wrapper(prefix + "warning: declaration uses `sorry`")
                self.assertEqual(result.returncode, 1)

    def test_sorry_axiom_reports_are_rejected_including_multiline(self):
        for report in ("'t' depends on axioms: [propext, sorryAx]",
                       "'t' depends on axioms: [propext,\n sorryAx]",
                       "/tmp/source.lean:3:0: info: 't' depends on axioms: [sorryAx]"):
            with self.subTest(report=report):
                self.assertEqual(self.run_wrapper(report).returncode, 2)

    def test_constant_name_is_not_an_axiom_list(self):
        self.assertEqual(self.run_wrapper("'sorryAx' depends on axioms: [propext]").returncode, 0)


if __name__ == "__main__":
    unittest.main()
