# Copyright (c) 2026 Jonas-Augustinus-Linus.
# Released under MIT and Apache-2.0; see LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""The first-sponsor arithmetic audit must reject false certificates under -O."""

from pathlib import Path
import unittest

SOURCE = Path(__file__).resolve().parents[1] / 'probes' / 'probe_sponsor_finite_audit.py'


def load_audit(optimization):
    namespace = {'__name__': 'sponsor_audit_under_test'}
    exec(compile(SOURCE.read_text(), str(SOURCE), 'exec', optimize=optimization), namespace)
    return namespace


class SponsorCertificateChecks(unittest.TestCase):
    def test_order_one_generator_is_rejected(self):
        for optimization in (0, 1, 2):
            with self.subTest(optimization=optimization):
                audit = load_audit(optimization)
                audit['G'] = 1
                with self.assertRaises(AssertionError):
                    audit['construction_arithmetic']()

    def test_non_subgroup_generator_is_rejected(self):
        for optimization in (0, 1, 2):
            with self.subTest(optimization=optimization):
                audit = load_audit(optimization)
                audit['G'] = 0
                with self.assertRaises(AssertionError):
                    audit['construction_arithmetic']()

    def test_missing_moment_boundary_is_rejected(self):
        for optimization in (0, 1, 2):
            with self.subTest(optimization=optimization):
                audit = load_audit(optimization)
                audit['moment_slack'] = lambda t, r, s: 1
                with self.assertRaises(AssertionError):
                    audit['moment_frontier'](3)

    def test_published_construction_and_frontiers_are_preserved(self):
        for optimization in (0, 1, 2):
            with self.subTest(optimization=optimization):
                audit = load_audit(optimization)
                construction = audit['construction_arithmetic']()
                self.assertEqual(construction['radius'], '178956971/536870912')
                self.assertEqual(construction['distinct_scalars'], 1073741829)
                self.assertEqual(audit['moment_frontier'](3)['lattice_floor'],
                                 '52670889/268435456')
                self.assertEqual(audit['constant_line_frontier']()['lattice_floor'],
                                 '110756187/536870912')


if __name__ == '__main__':
    unittest.main()
