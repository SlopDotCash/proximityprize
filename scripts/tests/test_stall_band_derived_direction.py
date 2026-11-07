"""Stall-band diagnostics must use the derived flow-map direction (audit L116).

The probe runs its census at import time, so the helper functions are extracted
with ast (as in test_collinear_certificate.py).  Replays the audit fixture:
F17, n=16, k=4, T=9, domain 0..15, constant pencils (0,0) and (16,2).
"""
import ast
from collections import Counter
from math import isqrt
from pathlib import Path
import unittest

import numpy as np

source = Path(__file__).resolve().parents[1] / 'probes/probe_rate_quarter_p1_stall_band_census.py'
NAMES = {'modinv', 'interp_check', 'row_is_codeword_on', 'nonjoint', 'census_against_pencils',
         'derived_direction', 'rider_direction_buckets'}
nodes = [n for n in ast.parse(source.read_text()).body
         if isinstance(n, ast.FunctionDef) and n.name in NAMES]
assert {n.name for n in nodes} == NAMES
namespace = {'np': np, 'isqrt': isqrt, 'Counter': Counter}
exec(compile(ast.Module(body=nodes, type_ignores=[]), str(source), 'exec'), namespace)

Q, N, K, T, F0 = 17, 16, 4, 9, 2
DOM = list(range(N))
U0 = np.array([0] * 9 + [1] * 7, dtype=np.int64)
U1 = np.array([1] * 2 + [0] * 14, dtype=np.int64)
PENCILS = [(np.zeros(N, dtype=np.int64), np.zeros(N, dtype=np.int64)),
           (np.full(N, 16, dtype=np.int64), np.full(N, 2, dtype=np.int64))]


class DerivedDirection(unittest.TestCase):
    def setUp(self):
        out = namespace['census_against_pencils'](N, Q, K, T, F0, DOM, U0, U1, PENCILS)
        self.stall = {g: [x for x in o if x[2] and x[0] >= F0 + 1] for g, o in out.items()}
        self.stall = {g: o for g, o in self.stall.items() if o}

    def test_fixture_witnesses(self):
        # gamma0 = 0 with p0 = 0 and gamma = 1 with q_1 = 1: nonjoint, agreement 9, pool 7.
        self.assertEqual(sorted(self.stall), [0, 1])
        self.assertEqual([(x[0], x[1]) for x in self.stall[0]], [(7, 9)])
        self.assertEqual([(x[0], x[1]) for x in self.stall[1]], [(7, 9)])

    def test_derived_direction_not_stored_slope(self):
        p0 = np.zeros(N, dtype=np.int64)
        z = np.arange(9)
        w0, w1 = self.stall[1][0][3]
        derived = namespace['derived_direction'](Q, p0, 0, w0, w1, 1)
        self.assertTrue(np.all(derived == 1))
        self.assertEqual(int((derived[z] == U1[z]).sum()), 2)  # = T - F, in window [2, 5]
        self.assertEqual(int((w1[z] == U1[z]).sum()), 0)  # the old, wrong measurement

    def test_buckets_and_flow_map_bound(self):
        p0 = np.zeros(N, dtype=np.int64)
        hist, agrs, z, pool, window = namespace['rider_direction_buckets'](
            Q, T, K, U0, U1, 0, p0, self.stall)
        self.assertEqual(list(z), list(range(9)))
        self.assertEqual((pool, window), (7, (2, 5)))
        self.assertEqual(agrs, {1: 2})
        self.assertEqual(hist, {'in window': 1})

    def test_bound_violation_is_caught(self):
        # A fabricated partner whose recorded agreement A is too large to be real.
        p0 = np.zeros(N, dtype=np.int64)
        bogus = {1: [(0, N, True, (np.full(N, 3, dtype=np.int64), np.zeros(N, dtype=np.int64)))]}
        with self.assertRaises(AssertionError):
            namespace['rider_direction_buckets'](Q, T, K, U0, U1, 0, p0, bogus)


if __name__ == '__main__':
    unittest.main()
