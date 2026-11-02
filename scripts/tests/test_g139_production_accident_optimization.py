"""G139 production accident census checks must stay active under python -O."""

from __future__ import annotations

import ast
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

PROBE = (
    Path(__file__).resolve().parents[1]
    / "probes"
    / "probe_g139_production_accident_census.py"
)

WITNESS_GATE = (
    '    require(witness in accidents, "G173 retained witness missing from accidents")'
)
WITNESS_FLIP = (
    '    require(False, "G173 retained witness missing from accidents")'
)

HARNESS_TAIL = r'''

def _optimization_harness() -> None:
    check_g173_witness()
    print("HARNESS_OK")


if __name__ == "__main__":
    _optimization_harness()
'''


def _harness_source(probe_source: str) -> str:
    stripped = probe_source.replace(
        'if __name__ == "__main__":\n    main()\n',
        "",
        1,
    )
    return stripped + HARNESS_TAIL


def run_harness(source_text: str, *, python_flags=(), env=None):
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "probe_g139_production_accident_census.py"
        path.write_text(source_text, encoding="utf-8")
        merged_env = {**os.environ, **(env or {})}
        return subprocess.run(
            [sys.executable, *python_flags, "-X", "utf8", "-B", str(path)],
            capture_output=True,
            text=True,
            encoding="utf-8",
            timeout=60,
            env=merged_env,
        )


class ProductionAccidentOptimization(unittest.TestCase):
    def test_no_bare_assert_statements(self):
        tree = ast.parse(PROBE.read_text(encoding="utf-8"))
        offenders = [
            node.lineno for node in ast.walk(tree) if isinstance(node, ast.Assert)
        ]
        self.assertEqual(offenders, [])

    def test_g173_harness_passes_with_optimization(self):
        source = _harness_source(PROBE.read_text(encoding="utf-8"))
        baseline = run_harness(source)
        self.assertEqual(baseline.returncode, 0, baseline.stderr)
        self.assertIn("HARNESS_OK", baseline.stdout)
        self.assertIn("G173 cross-check:", baseline.stdout)
        modes = (
            (("-O",), None),
            (("-OO",), None),
            ((), {**os.environ, "PYTHONOPTIMIZE": "1"}),
        )
        for python_flags, env in modes:
            with self.subTest(python_flags=python_flags, env=env is not None):
                completed = run_harness(source, python_flags=python_flags, env=env)
                self.assertEqual(completed.returncode, 0, completed.stderr)
                self.assertEqual(completed.stdout, baseline.stdout)

    def test_missing_witness_rejected_with_optimization(self):
        base = PROBE.read_text(encoding="utf-8")
        harness = _harness_source(base)
        # Corrupt census so accidents drop the retained witness.
        needle = "    total, accidents = census(h, p)\n"
        self.assertGreaterEqual(harness.count(needle), 1)
        # Only flip the G173 path: replace the first occurrence inside check_g173.
        idx = harness.find("def check_g173_witness()")
        self.assertGreater(idx, 0)
        head, tail = harness[:idx], harness[idx:]
        self.assertIn(needle, tail)
        tail = tail.replace(
            needle,
            "    total, accidents = census(h, p)\n"
            "    accidents = []\n",
            1,
        )
        bad = head + tail
        for python_flags in ((), ("-O",), ("-OO",)):
            with self.subTest(python_flags=python_flags):
                completed = run_harness(bad, python_flags=python_flags)
                self.assertNotEqual(completed.returncode, 0, completed.stdout)
                self.assertIn(
                    "G173 retained witness missing from accidents",
                    completed.stderr,
                )

    def test_wrong_witness_coordinates_rejected_with_optimization(self):
        base = PROBE.read_text(encoding="utf-8")
        harness = _harness_source(base)
        needle = (
            '    require(witness == (5663213, 17079628, 5424631),\n'
            '            "G173 retained witness coordinates drifted")'
        )
        self.assertIn(needle, harness)
        bad = harness.replace(
            needle,
            '    require(witness == (0, 0, 0),\n'
            '            "G173 retained witness coordinates drifted")',
            1,
        )
        for python_flags in ((), ("-O",), ("-OO",)):
            with self.subTest(python_flags=python_flags):
                completed = run_harness(bad, python_flags=python_flags)
                self.assertNotEqual(completed.returncode, 0, completed.stdout)
                self.assertIn(
                    "G173 retained witness coordinates drifted",
                    completed.stderr,
                )

    def test_forced_witness_gate_flip_rejected_with_optimization(self):
        base = PROBE.read_text(encoding="utf-8")
        harness = _harness_source(base)
        self.assertEqual(harness.count(WITNESS_GATE), 1)
        bad = harness.replace(WITNESS_GATE, WITNESS_FLIP, 1)
        for python_flags in ((), ("-O",), ("-OO",)):
            with self.subTest(python_flags=python_flags):
                completed = run_harness(bad, python_flags=python_flags)
                self.assertNotEqual(completed.returncode, 0, completed.stdout)
                self.assertIn(
                    "G173 retained witness missing from accidents",
                    completed.stderr,
                )


if __name__ == "__main__":
    unittest.main()
