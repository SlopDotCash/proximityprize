"""G328 field-stability boundary checks must stay active under python -O."""

from __future__ import annotations

import ast
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

PROBE = Path(__file__).resolve().parents[1] / "probes" / "g328_k2_field_stability_boundary.py"
PASS_MARKER = "PASS: universal field-independence is false; the tested stable range starts at p=41"
P17_REQUIRE = "    require(results[17] == (16, 9, EXPECTED_MAXIMIZERS), results[17])"
P17_CORRUPT = "    require(results[17] == (0, 0, EXPECTED_MAXIMIZERS), results[17])  # corrupt"
FAST_LIMIT = "LIMIT = 200"


def with_fast_limit(source_text: str) -> str:
    """Shrink the scan window so unit tests stay cheap while still covering p=17 and p=41."""
    if "LIMIT = 10_000" not in source_text:
        raise AssertionError("expected LIMIT = 10_000 in probe source")
    return source_text.replace("LIMIT = 10_000", FAST_LIMIT, 1)


def run_probe_source(source_text: str, *, python_flags=(), env=None, timeout=60):
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "g328_k2_field_stability_boundary.py"
        path.write_text(source_text, encoding="utf-8")
        merged_env = {**os.environ, **(env or {})}
        if env is None or "PYTHONOPTIMIZE" not in env:
            merged_env.pop("PYTHONOPTIMIZE", None)
        return subprocess.run(
            [sys.executable, *python_flags, "-X", "utf8", "-B", str(path)],
            capture_output=True,
            text=True,
            encoding="utf-8",
            timeout=timeout,
            env=merged_env,
        )


def to_bare_assert_source(source_text: str) -> str:
    """Rewrite require(cond, detail) call sites into bare assert statements."""
    pattern = re.compile(
        r"^([ \t]*)require\((.+),\s*(.+)\)$",
        re.MULTILINE,
    )
    rewritten = pattern.sub(r"\1assert \2, \3", source_text)
    # Multi-line require in main for the stable_primes check:
    rewritten = re.sub(
        r"^([ \t]*)require\(\n"
        r"([ \t]*)all\(results\[p\] == \(40, 9, EXPECTED_MAXIMIZERS\) for p in stable_primes\),\n"
        r"([ \t]*)\{p: results\[p\] for p in stable_primes if results\[p\] != \(40, 9, EXPECTED_MAXIMIZERS\)\},\n"
        r"([ \t]*)\)\n",
        r"\1assert all(results[p] == (40, 9, EXPECTED_MAXIMIZERS) for p in stable_primes)\n",
        rewritten,
        count=1,
        flags=re.MULTILINE,
    )
    rewritten = re.sub(
        r"\ndef require\(condition, detail\):\n"
        r"    \"\"\"Certificate checks must survive python -O and PYTHONOPTIMIZE\.\"\"\"\n"
        r"    if not condition:\n"
        r"        raise AssertionError\(detail\)\n",
        "\n",
        rewritten,
        count=1,
    )
    return rewritten


class FieldStabilityOptimization(unittest.TestCase):
    def test_no_bare_assert_statements(self):
        tree = ast.parse(PROBE.read_text(encoding="utf-8"))
        offenders = [node.lineno for node in ast.walk(tree) if isinstance(node, ast.Assert)]
        self.assertEqual(offenders, [])

    def test_valid_probe_passes_with_optimization(self):
        source = with_fast_limit(PROBE.read_text(encoding="utf-8"))
        baseline = run_probe_source(source)
        self.assertEqual(baseline.returncode, 0, baseline.stderr)
        self.assertIn(PASS_MARKER, baseline.stdout)
        modes = (
            (("-O",), None),
            (("-OO",), None),
            ((), {**os.environ, "PYTHONOPTIMIZE": "1"}),
        )
        for python_flags, env in modes:
            with self.subTest(python_flags=python_flags, env=env is not None):
                completed = run_probe_source(source, python_flags=python_flags, env=env)
                self.assertEqual(completed.returncode, 0, completed.stderr)
                self.assertEqual(completed.stdout, baseline.stdout)

    def test_corrupted_p17_certificate_rejected_with_optimization(self):
        source = with_fast_limit(PROBE.read_text(encoding="utf-8"))
        self.assertIn(P17_REQUIRE, source)
        bad = source.replace(P17_REQUIRE, P17_CORRUPT, 1)
        for python_flags in ((), ("-O",), ("-OO",)):
            with self.subTest(python_flags=python_flags):
                completed = run_probe_source(bad, python_flags=python_flags)
                self.assertNotEqual(completed.returncode, 0, completed.stdout)
                self.assertIn("AssertionError", completed.stderr)
                self.assertNotIn(PASS_MARKER, completed.stdout)

    def test_bare_assert_would_be_stripped_under_optimization(self):
        """Document the pre-fix defect: bare asserts on a corrupt p=17 certificate
        fail without -O but are stripped under -O and still print PASS.
        """
        source = with_fast_limit(PROBE.read_text(encoding="utf-8"))
        bare = to_bare_assert_source(source)
        self.assertNotIn("def require", bare)
        self.assertIn("assert results[17] == (16, 9, EXPECTED_MAXIMIZERS)", bare)
        bare = bare.replace(
            "assert results[17] == (16, 9, EXPECTED_MAXIMIZERS), results[17]",
            "assert results[17] == (0, 0, EXPECTED_MAXIMIZERS), results[17]",
            1,
        )
        without = run_probe_source(bare)
        self.assertNotEqual(without.returncode, 0, without.stdout)
        self.assertIn("AssertionError", without.stderr)
        with_o = run_probe_source(bare, python_flags=("-O",))
        self.assertEqual(with_o.returncode, 0, with_o.stderr)
        self.assertIn(PASS_MARKER, with_o.stdout)


if __name__ == "__main__":
    unittest.main()
