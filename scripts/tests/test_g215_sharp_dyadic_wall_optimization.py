"""G215 sharp dyadic wall floor checks must stay active under python -O."""

from __future__ import annotations

import ast
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

PROBE = Path(__file__).resolve().parents[1] / "probes" / "g215_sharp_dyadic_wall_floor.py"
PASS_LINE = (
    "G215 sharp dyadic wall floor: ALL constant/witness/gap checks PASS "
    "for n=2m, m in [2,199]."
)
FLAT_RETURN = "    return 1 * 1 + (m - 1) * (2 * 2)"
FLAT_CORRUPT = "    return 1 * 1 + (m - 1) * (2 * 2) + 1  # corrupt flat witness"
CS_GAP = "            require(cs_tail < tail_sharp, (n, cs_tail, tail_sharp))"
CS_GAP_FLIP = "            require(cs_tail > tail_sharp, (n, cs_tail, tail_sharp))"


def run_probe_source(source_text: str, *, python_flags=(), env=None):
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "g215_sharp_dyadic_wall_floor.py"
        path.write_text(source_text, encoding="utf-8")
        merged_env = {**os.environ, **(env or {})}
        # Drop PYTHONOPTIMIZE from the ambient env unless the caller set it.
        if env is None or "PYTHONOPTIMIZE" not in env:
            merged_env.pop("PYTHONOPTIMIZE", None)
        return subprocess.run(
            [sys.executable, *python_flags, "-X", "utf8", "-B", str(path)],
            capture_output=True,
            text=True,
            encoding="utf-8",
            timeout=30,
            env=merged_env,
        )


def to_bare_assert_source(source_text: str) -> str:
    """Rewrite require(cond, detail) call sites into bare assert statements."""
    pattern = re.compile(
        r"^([ \t]*)require\((.+),\s*(.+)\)$",
        re.MULTILINE,
    )
    rewritten = pattern.sub(r"\1assert \2, \3", source_text)
    # Drop the unused require helper so the file only uses bare asserts.
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


class SharpDyadicWallOptimization(unittest.TestCase):
    def test_no_bare_assert_statements(self):
        tree = ast.parse(PROBE.read_text(encoding="utf-8"))
        offenders = [node.lineno for node in ast.walk(tree) if isinstance(node, ast.Assert)]
        self.assertEqual(offenders, [])

    def test_valid_probe_passes_with_optimization(self):
        source = PROBE.read_text(encoding="utf-8")
        baseline = run_probe_source(source)
        self.assertEqual(baseline.returncode, 0, baseline.stderr)
        self.assertIn(PASS_LINE, baseline.stdout)
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

    def test_corrupted_flat_witness_rejected_with_optimization(self):
        source = PROBE.read_text(encoding="utf-8")
        self.assertIn(FLAT_RETURN, source)
        bad = source.replace(FLAT_RETURN, FLAT_CORRUPT, 1)
        for python_flags in ((), ("-O",), ("-OO",)):
            with self.subTest(python_flags=python_flags):
                completed = run_probe_source(bad, python_flags=python_flags)
                self.assertNotEqual(completed.returncode, 0, completed.stdout)
                self.assertIn("AssertionError", completed.stderr)
                self.assertNotIn(PASS_LINE, completed.stdout)

    def test_flipped_cs_gap_rejected_with_optimization(self):
        source = PROBE.read_text(encoding="utf-8")
        self.assertIn(CS_GAP, source)
        bad = source.replace(CS_GAP, CS_GAP_FLIP, 1)
        for python_flags in ((), ("-O",), ("-OO",)):
            with self.subTest(python_flags=python_flags):
                completed = run_probe_source(bad, python_flags=python_flags)
                self.assertNotEqual(completed.returncode, 0, completed.stdout)
                self.assertIn("AssertionError", completed.stderr)
                self.assertNotIn(PASS_LINE, completed.stdout)

    def test_bare_assert_would_be_stripped_under_optimization(self):
        """Document the pre-fix defect: bare asserts on a corrupt witness
        fail without -O but are stripped under -O and still print ALL PASS.
        """
        source = PROBE.read_text(encoding="utf-8")
        bare = to_bare_assert_source(source)
        self.assertNotIn("def require", bare)
        self.assertIn("assert flat == 2 * n - 3", bare)
        bare = bare.replace(FLAT_RETURN, FLAT_CORRUPT, 1)
        without = run_probe_source(bare)
        self.assertNotEqual(without.returncode, 0, without.stdout)
        self.assertIn("AssertionError", without.stderr)
        with_o = run_probe_source(bare, python_flags=("-O",))
        self.assertEqual(with_o.returncode, 0, with_o.stderr)
        self.assertIn(PASS_LINE, with_o.stdout)


if __name__ == "__main__":
    unittest.main()
