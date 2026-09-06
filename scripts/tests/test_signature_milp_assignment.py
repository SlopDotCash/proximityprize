"""Exercise binary certificate checks without requiring either solver backend."""
import ast
from math import inf
from itertools import product
from pathlib import Path
import unittest
import numpy as np

source = Path(__file__).resolve().parents[1] / 'probes/probe_rate_quarter_noeight_source7_signatures_milp.py'
nodes = [n for n in ast.parse(source.read_text()).body if isinstance(n, (ast.ClassDef, ast.FunctionDef)) and n.name in ('BinaryMILP', 'add_and', 'add_fresh_and')]
namespace = {'np': np, 'inf': inf}
exec(compile(ast.Module(body=nodes, type_ignores=[]), str(source), 'exec'), namespace)


class AssignmentCheck(unittest.TestCase):
    def test_exact_constraint_and_integrality_checks(self):
        model = namespace['BinaryMILP']()
        a, b = model.variable('a'), model.variable('b')
        model.equal({a: 1, b: 1}, 1)
        self.assertEqual(model.checked_assignment([1 - 1e-8, 1e-8]), [1, 0])
        for invalid in ([0, 0], [1, 1], [0.5, 0.5], [float('nan'), 1], [float('inf'), 0], [2, -1], [1]):
            with self.subTest(invalid=invalid), self.assertRaises(ValueError):
                model.checked_assignment(invalid)

    def test_boolean_encodings_exhaustively(self):
        for helper in ('add_and', 'add_fresh_and'):
            for count in range(5):
                model = namespace['BinaryMILP']()
                inputs = [model.variable(str(i)) for i in range(count)]
                output = namespace[helper](model, inputs, 'output')
                for bits in product((0, 1), repeat=count):
                    expected = int(all(bits) if helper == 'add_and' else not any(bits))
                    for result in (0, 1):
                        assignment = list(bits) + [result]
                        if result == expected:
                            self.assertEqual(model.checked_assignment(assignment)[output], expected)
                        else:
                            with self.assertRaises(ValueError):
                                model.checked_assignment(assignment)
