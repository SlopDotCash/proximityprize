# Copyright (c) 2026 nerd27dk.
# Released under MIT and Apache-2.0; see LICENSE-MIT and LICENSE.
"""G330 boundary certificate gates must stay active under python -O."""

import ast
import contextlib
import io
from pathlib import Path
import unittest

SOURCE = Path(__file__).resolve().parents[1] / "probes" / "g330_spectrum_exact_boundary.py"
TAMPERED_OK_SET = "OK_SET = {2, 4, 8, 16, 18, 32, 34, 36, 50, 64, 68, 98, 145}"


def load_main(source_text, optimization):
    tree = ast.parse(source_text)
    namespace = {"__name__": "g330_under_test"}
    exec(compile(tree, str(SOURCE), "exec", optimize=optimization), namespace)
    return namespace["main"]


class BoundaryCertificateOptimization(unittest.TestCase):
    def test_no_bare_assert_statements(self):
        tree = ast.parse(SOURCE.read_text())
        offenders = [node.lineno for node in ast.walk(tree)
                     if isinstance(node, ast.Assert)]
        self.assertEqual(offenders, [])

    def test_tampered_certificate_rejected_at_every_optimization_level(self):
        source_text = SOURCE.read_text()
        original = "OK_SET = {2, 4, 8, 16, 18, 32, 34, 36, 50, 64, 68, 98, 144}"
        self.assertIn(original, source_text)
        tampered = source_text.replace(original, TAMPERED_OK_SET, 1)
        for optimization in (0, 1, 2):
            with self.subTest(optimization=optimization), \
                    contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaises(AssertionError):
                    load_main(tampered, optimization)()

    def test_valid_certificate_passes_at_every_optimization_level(self):
        source_text = SOURCE.read_text()
        for optimization in (0, 1, 2):
            with self.subTest(optimization=optimization):
                out = io.StringIO()
                with contextlib.redirect_stdout(out):
                    load_main(source_text, optimization)()
                self.assertIn("PASS: the weight-{1,3} spectrum collision "
                              "boundary is exactly {17}", out.getvalue())


if __name__ == "__main__":
    unittest.main()
