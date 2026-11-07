"""G299 prize-depth window checks must stay active under python -O."""

from __future__ import annotations

import ast
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

PROBE = Path(__file__).resolve().parents[1] / "probes" / "g299_prize_depth_in_window.py"
PASS_MARKER = (
    "ALL G299 CHECKS PASS: production prize depth is INSIDE the palindrome window; "
    "G296 escape-prose refuted."
)
SIGMA_FAIL_BLOCK = """expected_sigma = n + 1 - 89
if sigma(n, rstar) != expected_sigma or expected_sigma != 2**30 - 88:
    fail(
        f"sigma(n,r*) identity failed: got {sigma(n, rstar)}, "
        f"expected {expected_sigma} == 2^30-88"
    )"""
SIGMA_CORRUPT_BLOCK = """expected_sigma = 0  # corrupt
if sigma(n, rstar) != expected_sigma or expected_sigma != 2**30 - 88:
    fail(
        f"sigma(n,r*) identity failed: got {sigma(n, rstar)}, "
        f"expected {expected_sigma} == 2^30-88"
    )"""


def run_probe_source(source_text: str, *, python_flags=(), env=None, timeout=30):
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "g299_prize_depth_in_window.py"
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
    """Rewrite the hardened sigma identity back into a bare assert (pre-fix shape)."""
    if SIGMA_FAIL_BLOCK not in source_text:
        raise AssertionError("expected hardened sigma fail block in probe source")
    return source_text.replace(
        SIGMA_FAIL_BLOCK,
        "assert sigma(n, rstar) == n + 1 - 89 == 2**30 - 88",
        1,
    )


class PrizeDepthOptimization(unittest.TestCase):
    def test_no_bare_assert_statements(self):
        tree = ast.parse(PROBE.read_text(encoding="utf-8"))
        offenders = [node.lineno for node in ast.walk(tree) if isinstance(node, ast.Assert)]
        self.assertEqual(offenders, [])

    def test_valid_probe_passes_with_optimization(self):
        source = PROBE.read_text(encoding="utf-8")
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

    def test_corrupted_sigma_identity_rejected_with_optimization(self):
        source = PROBE.read_text(encoding="utf-8")
        self.assertIn(SIGMA_FAIL_BLOCK, source)
        bad = source.replace(SIGMA_FAIL_BLOCK, SIGMA_CORRUPT_BLOCK, 1)
        for python_flags in ((), ("-O",), ("-OO",)):
            with self.subTest(python_flags=python_flags):
                completed = run_probe_source(bad, python_flags=python_flags)
                self.assertNotEqual(completed.returncode, 0, completed.stdout)
                self.assertIn("FAIL:", completed.stdout)
                self.assertNotIn(PASS_MARKER, completed.stdout)

    def test_bare_assert_would_be_stripped_under_optimization(self):
        """Document the pre-fix defect: bare assert on a corrupt sigma identity
        fails without -O but is stripped under -O and still prints PASS.
        """
        source = PROBE.read_text(encoding="utf-8")
        bare = to_bare_assert_source(source)
        self.assertIn("assert sigma(n, rstar) == n + 1 - 89 == 2**30 - 88", bare)
        bare = bare.replace(
            "assert sigma(n, rstar) == n + 1 - 89 == 2**30 - 88",
            "assert sigma(n, rstar) == 0  # corrupt",
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
