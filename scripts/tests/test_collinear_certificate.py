"""Reject malformed certificates before checking collinearity geometry."""
import ast
import contextlib
import io
import itertools
from pathlib import Path
import unittest

source = Path(__file__).resolve().parents[1] / 'probes/probe_w6_kfour_collinear_cpsat.py'
node = next(n for n in ast.parse(source.read_text()).body if isinstance(n, ast.FunctionDef) and n.name == 'verify')
namespace = {'itertools': itertools}
exec(compile(ast.Module(body=[node], type_ignores=[]), str(source), 'exec'), namespace)


class CertificateShape(unittest.TestCase):
    def test_regular_signature_and_invalid_shapes(self):
        valid = ([0, 1, 2], [0, 1, 2])
        with contextlib.redirect_stdout(io.StringIO()):
            namespace['verify']([valid])
        for invalid in [([], []), ([0, 0, 1], [0, 1, 2]), ([0, 1, 7], [0, 1, 2]), ([0, 1, 2], [-1, 1, 2]), ([0, 1, 2], [0, 1, 9])]:
            with self.subTest(invalid=invalid), self.assertRaises(AssertionError):
                namespace['verify']([invalid])
        with self.assertRaises(AssertionError):
            namespace['verify']([valid, valid])
