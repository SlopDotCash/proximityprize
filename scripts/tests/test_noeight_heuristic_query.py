# Copyright (c) 2026 Oz-0s. All rights reserved.
# Released under the MIT and Apache 2.0 licenses. See LICENSE-MIT and LICENSE.
# Authors: Oz-0s

"""A signature SAT certificate must satisfy the query the operator requested."""
import ast
import contextlib
import importlib.util
import io
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

SOURCE = Path(__file__).resolve().parents[1] / 'probes' / (
    'probe_rate_quarter_noeight_source7_signatures_z3.py')


class HeuristicQuery(unittest.TestCase):
    def run_cli(self, *arguments):
        # These query checks must not need Z3 or SciPy in routine validation.
        # Execute the actual CLI with a solver-free mathematical heuristic stub.
        tree = ast.parse(SOURCE.read_text(encoding='utf-8'))
        cli = next(n for n in tree.body if isinstance(n, ast.If)
                   and ast.unparse(n.test) == "__name__ == '__main__'")
        from argparse import ArgumentParser
        calls = []
        namespace = {'__name__': '__main__', 'ArgumentParser': ArgumentParser,
                     'heuristic_regular_model': lambda *a: calls.append(a) or [1]}
        with contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()), \
                patch.object(sys, 'argv', [str(SOURCE),
                    '--signatures', '3', '--heuristic-restarts', '1', *arguments]):
            with self.assertRaises(SystemExit) as result:
                exec(compile(ast.Module(body=[cli], type_ignores=[]), str(SOURCE), 'exec'),
                     namespace)
        return result.exception.code, calls

    def test_mixed_regularity_is_not_silently_replaced_with_all_regular(self):
        for count in ('0', '1', '2', '4'):
            with self.subTest(count=count):
                status, calls = self.run_cli('--regular-count', count)
                self.assertEqual((status, calls), (2, []))

    def test_intersection_slices_and_incomplete_pairs_are_rejected_before_search(self):
        for flags in (('--second-root-intersection', '0'),
                      ('--second-missed-intersection', '0'),
                      ('--second-root-intersection', '0', '--second-missed-intersection', '0')):
            with self.subTest(flags=flags):
                self.assertEqual(self.run_cli(*flags), (2, []))

    def test_equivalent_all_regular_query_is_preserved(self):
        for flags in ((), ('--regular-count', '3'), ('--regular-only',)):
            status, calls = self.run_cli(*flags)
            self.assertEqual(status, 0)
            self.assertEqual(len(calls), 1)

    @unittest.skipUnless(importlib.util.find_spec('z3'), 'optional Z3 backend')
    def test_real_cli_rejects_the_former_false_sat_and_keeps_valid_search(self):
        command = [sys.executable, str(SOURCE), '--signatures', '3',
                   '--heuristic-restarts', '1', '--heuristic-steps', '100', '--seed', '466']
        invalid = subprocess.run([*command, '--regular-count', '0'],
                                 capture_output=True, text=True, timeout=30)
        self.assertEqual(invalid.returncode, 2)
        self.assertNotIn("'heuristic': 'sat'", invalid.stdout)
        self.assertIn('--regular-count', invalid.stderr)
        valid = subprocess.run(command, capture_output=True, text=True, timeout=30)
        self.assertEqual(valid.returncode, 0, valid.stderr)
        self.assertIn("'heuristic': 'sat'", valid.stdout)


if __name__ == '__main__':
    unittest.main()
