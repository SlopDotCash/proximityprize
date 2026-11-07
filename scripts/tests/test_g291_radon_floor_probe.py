"""G291 minimal Radon-floor probe gates must stay active under python -O."""

import ast
import contextlib
import io
from pathlib import Path
import unittest

SOURCE = Path(__file__).resolve().parents[1] / "probes" / "g291_minimal_radon_floor_nogo.py"
PASS_LINE = "ALL PASS: minimal r-uniform positive Radon circuit"

TAMPERS = {
    "weight": ("weight = [770888209934274952,", "weight = [770888209934274953,"),
    "ranks": ("ranks = [5, 6, 5, 6, 5]", "ranks = [5, 5, 5, 5, 5]"),
}


def run_probe(source_text, optimization):
    tree = ast.parse(source_text)
    namespace = {"__name__": "g291_under_test"}
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        exec(compile(tree, str(SOURCE), "exec", optimize=optimization), namespace)
    return out.getvalue()


class RadonFloorProbeOptimization(unittest.TestCase):
    def test_no_bare_assert_statements(self):
        tree = ast.parse(SOURCE.read_text())
        offenders = [node.lineno for node in ast.walk(tree)
                     if isinstance(node, ast.Assert)]
        self.assertEqual(offenders, [])

    def test_tampered_data_rejected_at_every_optimization_level(self):
        source_text = SOURCE.read_text()
        for name, (original, tampered) in TAMPERS.items():
            self.assertIn(original, source_text)
            bad = source_text.replace(original, tampered, 1)
            for optimization in (0, 1, 2):
                with self.subTest(tamper=name, optimization=optimization):
                    with self.assertRaises(AssertionError):
                        run_probe(bad, optimization)

    def test_valid_data_passes_at_every_optimization_level(self):
        source_text = SOURCE.read_text()
        for optimization in (0, 1, 2):
            with self.subTest(optimization=optimization):
                self.assertIn(PASS_LINE, run_probe(source_text, optimization))


if __name__ == "__main__":
    unittest.main()
