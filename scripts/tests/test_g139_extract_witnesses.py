"""G139 Phi-collision extract checks must stay active under python -O."""

from __future__ import annotations

import ast
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

PROBE = Path(__file__).resolve().parents[1] / "probes" / "extract_g139_phi_collision_witnesses.py"
CONTROL_ANCHOR = (
    "CONTROL_CELLS = (\n"
    '    (64, 17318209, "G173-accident"),\n'
    '    (512, 138027521, "n512-offdiag-accident"),\n'
    ")"
)
INJECTIVE_DECOY = (
    "CONTROL_CELLS = (\n"
    '    (8, 73, "injective-decoy"),\n'
    ")"
)
RELATION_HOLD = "relation_holds = (gr + u) % p == (1 + d_value) % p"
RELATION_FLIP = "relation_holds = (gr + u) % p != (1 + d_value) % p"


def run_probe_source(source_text: str, *, python_flags=(), env=None):
    """Execute a probe source tree from the probes directory so sibling imports work."""
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "extract_g139_phi_collision_witnesses.py"
        path.write_text(source_text, encoding="utf-8")
        # Sibling import probe_g139_phi_certificate lives next to the real probe.
        # Point PYTHONPATH at scripts/probes rather than copying that module.
        probes_dir = str(PROBE.parent)
        merged_env = {**os.environ, **(env or {}), "PYTHONPATH": probes_dir}
        return subprocess.run(
            [sys.executable, *python_flags, "-X", "utf8", "-B", str(path)],
            capture_output=True,
            text=True,
            encoding="utf-8",
            timeout=30,
            env=merged_env,
            cwd=probes_dir,
        )


class ExtractWitnessOptimization(unittest.TestCase):
    def test_no_bare_assert_statements(self):
        tree = ast.parse(PROBE.read_text(encoding="utf-8"))
        offenders = [node.lineno for node in ast.walk(tree) if isinstance(node, ast.Assert)]
        self.assertEqual(offenders, [])

    def test_valid_control_cells_pass_with_optimization(self):
        source = PROBE.read_text(encoding="utf-8")
        baseline = run_probe_source(source)
        self.assertEqual(baseline.returncode, 0, baseline.stderr)
        self.assertIn('"relation_holds": true', baseline.stdout)
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

    def test_injective_decoy_rejected_with_optimization(self):
        source = PROBE.read_text(encoding="utf-8")
        self.assertIn(CONTROL_ANCHOR, source)
        bad = source.replace(CONTROL_ANCHOR, INJECTIVE_DECOY, 1)
        for python_flags in ((), ("-O",), ("-OO",)):
            with self.subTest(python_flags=python_flags):
                completed = run_probe_source(bad, python_flags=python_flags)
                self.assertNotEqual(completed.returncode, 0, completed.stdout)
                self.assertIn("expected at least one Phi collision", completed.stderr)

    def test_broken_relation_rejected_with_optimization(self):
        source = PROBE.read_text(encoding="utf-8")
        self.assertIn(RELATION_HOLD, source)
        bad = source.replace(RELATION_HOLD, RELATION_FLIP, 1)
        for python_flags in ((), ("-O",), ("-OO",)):
            with self.subTest(python_flags=python_flags):
                completed = run_probe_source(bad, python_flags=python_flags)
                self.assertNotEqual(completed.returncode, 0, completed.stdout)
                self.assertIn("additive Sidon relation failed", completed.stderr)
                self.assertNotIn('"relation_holds": false', completed.stdout)


if __name__ == "__main__":
    unittest.main()
