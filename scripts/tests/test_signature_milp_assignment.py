"""Exercise binary certificate checks without requiring either solver backend."""
import ast
from math import inf
from pathlib import Path
import unittest
import numpy as np

source = Path(__file__).resolve().parents[1] / 'probes/probe_rate_quarter_noeight_source7_signatures_milp.py'
node = next(n for n in ast.parse(source.read_text()).body if isinstance(n, ast.ClassDef) and n.name == 'BinaryMILP')
namespace = {'np': np, 'inf': inf}
exec(compile(ast.Module(body=[node], type_ignores=[]), str(source), 'exec'), namespace)


class AssignmentCheck(unittest.TestCase):
    def test_exact_constraint_and_integrality_checks(self):
        model = namespace['BinaryMILP']()
        a, b = model.variable('a'), model.variable('b')
        model.equal({a: 1, b: 1}, 1)
        self.assertEqual(model.checked_assignment([1 - 1e-8, 1e-8]), [1, 0])
        for invalid in ([0, 0], [1, 1], [0.5, 0.5], [float('nan'), 1], [float('inf'), 0], [2, -1], [1]):
            with self.subTest(invalid=invalid), self.assertRaises(ValueError):
                model.checked_assignment(invalid)
