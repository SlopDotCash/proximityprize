"""G139 Phi certificate checks must stay active under python -O."""

from __future__ import annotations

import ast
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

PROBE = Path(__file__).resolve().parents[1] / "probes" / "probe_g139_phi_certificate.py"

COMPOSITE_GATE = '    require(is_prime(17318209), "harness G173-accident modulus must be prime")'
COMPOSITE_FLIP = '    require(is_prime(9), "harness G173-accident modulus must be prime")'

HARNESS_TAIL = r'''

def _synthetic_injective_row() -> PhiRow:
    return PhiRow(
        label="synthetic-injective",
        n=8,
        p=73,
        q=9,
        generator=2,
        domain_size=4,
        image_size=4,
        injective=True,
        collision_count=0,
        collisions=(),
        phi_image_sha256="0" * 64,
    )


def _optimization_harness() -> None:
    accidents = [
        phi_certificate(64, 17318209, "G173-accident"),
        phi_certificate(512, 138027521, "n512-offdiag-accident"),
    ]
    pad = [_synthetic_injective_row() for _ in range(8)]
    check_rows = pad + accidents
    require(all(row.injective for row in check_rows[:8]),
            "expected first eight Phi rows injective")
    require([row.collision_count for row in check_rows[8:]] == [3, 3],
            "expected accident collision counts [3, 3]")
    require(is_prime(17318209), "harness G173-accident modulus must be prime")
    print("HARNESS_OK", check_rows[8].collision_count, check_rows[9].collision_count)


if __name__ == "__main__":
    # Override module main so importing helpers does not run the full diagonal search.
    _optimization_harness()
'''


def _harness_source(probe_source: str) -> str:
    """Drive accident cells plus synthetic injective pads; skip full main()."""
    # Drop the real __main__ guard so our harness is the only entrypoint.
    stripped = probe_source.replace(
        'if __name__ == "__main__":\n    main()\n',
        "",
        1,
    )
    return stripped + HARNESS_TAIL


def run_harness(source_text: str, *, python_flags=(), env=None):
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "probe_g139_phi_certificate.py"
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


class PhiCertificateOptimization(unittest.TestCase):
    def test_no_bare_assert_statements(self):
        tree = ast.parse(PROBE.read_text(encoding="utf-8"))
        offenders = [node.lineno for node in ast.walk(tree) if isinstance(node, ast.Assert)]
        self.assertEqual(offenders, [])

    def test_accident_harness_passes_with_optimization(self):
        source = _harness_source(PROBE.read_text(encoding="utf-8"))
        baseline = run_harness(source)
        self.assertEqual(baseline.returncode, 0, baseline.stderr)
        self.assertIn("HARNESS_OK 3 3", baseline.stdout)
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

    def test_noninjective_pad_rejected_with_optimization(self):
        base = PROBE.read_text(encoding="utf-8")
        harness = _harness_source(base)
        self.assertIn("injective=True", harness)
        bad = harness.replace(
            """def _synthetic_injective_row() -> PhiRow:
    return PhiRow(
        label="synthetic-injective",
        n=8,
        p=73,
        q=9,
        generator=2,
        domain_size=4,
        image_size=4,
        injective=True,
        collision_count=0,
        collisions=(),
        phi_image_sha256="0" * 64,
    )""",
            """def _synthetic_injective_row() -> PhiRow:
    return PhiRow(
        label="synthetic-noninjective-decoy",
        n=8,
        p=73,
        q=9,
        generator=2,
        domain_size=4,
        image_size=3,
        injective=False,
        collision_count=1,
        collisions=((1, 2),),
        phi_image_sha256="0" * 64,
    )""",
            1,
        )
        for python_flags in ((), ("-O",), ("-OO",)):
            with self.subTest(python_flags=python_flags):
                completed = run_harness(bad, python_flags=python_flags)
                self.assertNotEqual(completed.returncode, 0, completed.stdout)
                self.assertIn("expected first eight Phi rows injective", completed.stderr)

    def test_wrong_accident_counts_rejected_with_optimization(self):
        base = PROBE.read_text(encoding="utf-8")
        harness = _harness_source(base)
        needle = (
            'require([row.collision_count for row in check_rows[8:]] == [3, 3],\n'
            '            "expected accident collision counts [3, 3]")'
        )
        self.assertIn(needle, harness)
        bad = harness.replace(
            needle,
            'require([row.collision_count for row in check_rows[8:]] == [0, 0],\n'
            '            "expected accident collision counts [3, 3]")',
            1,
        )
        for python_flags in ((), ("-O",), ("-OO",)):
            with self.subTest(python_flags=python_flags):
                completed = run_harness(bad, python_flags=python_flags)
                self.assertNotEqual(completed.returncode, 0, completed.stdout)
                self.assertIn("expected accident collision counts [3, 3]", completed.stderr)

    def test_composite_accident_modulus_rejected_with_optimization(self):
        base = PROBE.read_text(encoding="utf-8")
        harness = _harness_source(base)
        # Only flip the harness gate, not any require inside the probe helpers.
        self.assertEqual(harness.count(COMPOSITE_GATE), 1)
        bad = harness.replace(COMPOSITE_GATE, COMPOSITE_FLIP, 1)
        for python_flags in ((), ("-O",), ("-OO",)):
            with self.subTest(python_flags=python_flags):
                completed = run_harness(bad, python_flags=python_flags)
                self.assertNotEqual(completed.returncode, 0, completed.stdout)
                self.assertIn("harness G173-accident modulus must be prime", completed.stderr)


if __name__ == "__main__":
    unittest.main()
