"""Optimization-mode regression tests for the incidence-triple-budget probe.

Bare ``assert`` statements are compiled out by ``python -O`` / ``-OO``, so a
probe that guards a certificate with ``assert`` would silently print a wrong
candidate bound with exit 0 under optimization. These tests pin the probe at
``scripts/probes/probe_incidence_triple_budget.py`` to fail closed in every
optimization mode:

* the probe contains no bare ``assert`` statements at all;
* the probe exits 0 and prints byte-identical stdout with no flags, ``-O``,
  ``-OO`` and ``PYTHONOPTIMIZE=1``;
* a negated-``slack`` corruption is rejected under plain, ``-O`` and ``-OO``;
* an ``s = 1`` corruption is rejected under plain, ``-O`` and ``-OO``.

Run with::

    python3 -m unittest scripts.tests.test_incidence_triple_budget_optimization -v
"""

import ast
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

PROBE_PATH = Path(__file__).resolve().parents[1] / "probes" / "probe_incidence_triple_budget.py"

EXPECTED_BOUND = 210683555
EXPECTED_BLOCK_SIZE = 56755


def _run_probe(probe_path, extra_flags=(), extra_env=None):
    env = dict(os.environ)
    if extra_env:
        env.update(extra_env)
    return subprocess.run(
        [sys.executable, *extra_flags, str(probe_path)],
        capture_output=True,
        text=True,
        env=env,
        timeout=300,
    )


def _corrupted_copy(source, old, new, tmpdir):
    if old not in source:
        raise ValueError(f"corruption anchor not found in probe: {old!r}")
    path = Path(tmpdir) / "probe_corrupted.py"
    path.write_text(source.replace(old, new, 1), encoding="utf-8")
    return path


class TestIncidenceTripleBudgetOptimization(unittest.TestCase):
    def test_no_bare_assert_in_probe(self):
        tree = ast.parse(PROBE_PATH.read_text(encoding="utf-8"))
        bare_asserts = [node for node in ast.walk(tree) if isinstance(node, ast.Assert)]
        self.assertEqual(bare_asserts, [])

    def test_probe_output_identical_across_optimization_modes(self):
        runs = [
            ("no flags", _run_probe(PROBE_PATH)),
            ("-O", _run_probe(PROBE_PATH, ("-O",))),
            ("-OO", _run_probe(PROBE_PATH, ("-OO",))),
            ("PYTHONOPTIMIZE=1", _run_probe(PROBE_PATH, extra_env={"PYTHONOPTIMIZE": "1"})),
        ]
        for label, result in runs:
            with self.subTest(mode=label):
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn('"candidate_error_bound": 210683555', result.stdout)
                payload = json.loads(result.stdout)
                self.assertEqual(payload["candidate_error_bound"], EXPECTED_BOUND)
                self.assertEqual(payload["block_size"], EXPECTED_BLOCK_SIZE)
        outputs = {result.stdout for _, result in runs}
        self.assertEqual(len(outputs), 1, "probe stdout differs across optimization modes")

    def test_negated_slack_corruption_rejected_in_all_modes(self):
        source = PROBE_PATH.read_text(encoding="utf-8")
        with tempfile.TemporaryDirectory() as tmpdir:
            corrupted = _corrupted_copy(source, "return lower - upper", "return upper - lower", tmpdir)
            for flags in ((), ("-O",), ("-OO",)):
                with self.subTest(mode=" ".join(flags) or "plain"):
                    result = _run_probe(corrupted, flags)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertNotIn("candidate_error_bound", result.stdout)
                    self.assertIn("slack(lo) must be positive", result.stderr)
                    self.assertIn("AssertionError", result.stderr)

    def test_s_equals_one_corruption_rejected_in_all_modes(self):
        source = PROBE_PATH.read_text(encoding="utf-8")
        with tempfile.TemporaryDirectory() as tmpdir:
            corrupted = _corrupted_copy(source, "s = isqrt(3 * m)", "s = 1", tmpdir)
            for flags in ((), ("-O",), ("-OO",)):
                with self.subTest(mode=" ".join(flags) or "plain"):
                    result = _run_probe(corrupted, flags)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertNotIn("candidate_error_bound", result.stdout)
                    self.assertIn("AssertionError", result.stderr)


if __name__ == "__main__":
    unittest.main()
